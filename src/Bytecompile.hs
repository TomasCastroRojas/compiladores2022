{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}
{-|
Module      : Bytecompile
Description : Compila a bytecode. Ejecuta bytecode.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

Este módulo permite compilar módulos a la Macchina. También provee
una implementación de la Macchina para ejecutar el bytecode.
-}
module Bytecompile
  (Bytecode, runBC, bcWrite, bcRead, bytecompileModule, showBC, bcc, bc2string)
 where

import Lang
import Subst
import MonadFD4 ( printFD4, printFD4inline, lookupDecl, MonadFD4, failFD4 )

import qualified Data.ByteString.Lazy as BS
import Data.Binary ( Word32, Binary(put, get), decode, encode )
import Data.Binary.Put ( putWord32le )
import Data.Binary.Get ( getWord32le, isEmpty )

import Data.List (intercalate)
import Data.Char

type Opcode = Int
type Bytecode = [Int]

newtype Bytecode32 = BC { un32 :: [Word32] }

data Val = I Int | Fun Env Bytecode | RA Env Bytecode deriving Show
type Env = [Val]

{- Esta instancia explica como codificar y decodificar Bytecode de 32 bits -}
instance Binary Bytecode32 where
  put (BC bs) = mapM_ putWord32le bs
  get = go
    where go =
           do
            empty <- isEmpty
            if empty
              then return $ BC []
              else do x <- getWord32le
                      BC xs <- go
                      return $ BC (x:xs)

{- Estos sinónimos de patrón nos permiten escribir y hacer
pattern-matching sobre el nombre de la operación en lugar del código
entero, por ejemplo:

   f (CALL : cs) = ...

 Notar que si hubieramos escrito algo como
   call = 5
 no podríamos hacer pattern-matching con `call`.

 En lo posible, usar estos códigos exactos para poder ejectutar un
 mismo bytecode compilado en distintas implementaciones de la máquina.
-}
pattern NULL     = 0
pattern RETURN   = 1
pattern CONST    = 2
pattern ACCESS   = 3
pattern FUNCTION = 4
pattern CALL     = 5
pattern ADD      = 6
pattern SUB      = 7
pattern JUMP     = 8
pattern FIX      = 9
pattern STOP     = 10
pattern SHIFT    = 11
pattern DROP     = 12
pattern PRINT    = 13
pattern PRINTN   = 14
-- CJUMP i salta i posiciones del bytecode si el tope de la pila es distinto de 0 (analogo a jnz)
-- JUMP i salta i posiciones del bytecode (analogo a jmp)
pattern CJUMP     = 15
pattern TAILCALL = 16

--función util para debugging: muestra el Bytecode de forma más legible.
showOps :: Bytecode -> [String]
showOps [] = []
showOps (NULL:xs)        = "NULL" : showOps xs
showOps (RETURN:xs)      = "RETURN" : showOps xs
showOps (CONST:i:xs)     = ("CONST " ++  show i) : showOps xs
showOps (ACCESS:i:xs)    = ("ACCESS " ++ show i) : showOps xs
showOps (FUNCTION:i:xs)  = ("FUNCTION len=" ++ show i) : showOps xs
showOps (CALL:xs)        = "CALL" : showOps xs
showOps (ADD:xs)         = "ADD" : showOps xs
showOps (SUB:xs)         = "SUB" : showOps xs
showOps (FIX:xs)         = "FIX" : showOps xs
showOps (STOP:xs)        = "STOP" : showOps xs
showOps (JUMP:i:xs)      = ("JUMP off=" ++ show i) : showOps xs
showOps (CJUMP:i:xs)     = ("CJUMP off=" ++ show i): showOps xs
showOps (SHIFT:xs)       = "SHIFT" : showOps xs
showOps (DROP:xs)        = "DROP" : showOps xs
showOps (PRINT:xs)       = let (msg,_:rest) = span (/=NULL) xs
                           in ("PRINT " ++ show (bc2string msg)) : showOps xs
showOps (PRINTN:xs)      = "PRINTN" : showOps xs
showOps (ADD:xs)         = "ADD" : showOps xs
showOps (TAILCALL:xs)    = "TAILCALL" : showOps xs
showOps (x:xs)           = show x : showOps xs

showBC :: Bytecode -> String
showBC = intercalate "; " . showOps

bcc :: MonadFD4 m => TTerm -> m Bytecode
bcc (Const info (CNat n)) = return [CONST, n]
bcc (App info t1 t2) = do
  bc1 <- bcc t1
  bc2 <- bcc t2
  return $ bc1 ++ bc2 ++ [CALL]

bcc (V info (Bound i)) = return [ACCESS,i]
bcc (V info (Global name)) = do
  def <- lookupDecl name
  case def of
    Nothing -> failFD4 "Variable no declarada"
    Just t -> bcc t

bcc (V info (Free name)) = error "Error variable libre"

bcc (BinaryOp info Add t1 t2) = do
  bc1 <- bcc t1
  bc2 <- bcc t2
  return $ bc1 ++ bc2 ++ [ADD]
bcc (BinaryOp info Sub t1 t2) = do
  bc1 <- bcc t1
  bc2 <- bcc t2
  return $ bc1 ++ bc2 ++ [SUB]

bcc (Let _ _ _ def (Sc1 term)) = do
  bc1 <- bcc def
  bc2 <- bcc term
  return $ bc1 ++ [SHIFT] ++ bc2 ++ [DROP]

bcc (Lam _ _ _ (Sc1 tterm)) = do
  bc_body <- tcc tterm
  return $ [FUNCTION, length bc_body] ++ bc_body
bcc (Fix info _ _ _ _ (Sc2 term)) = do
  bc_body <- tcc term
  return $ [FUNCTION, length bc_body] ++ bc_body ++ [FIX]

bcc (Print _ str term) = do
  bc <- bcc term
  return $ [PRINT] ++ string2bc str ++ [NULL] ++ bc ++ [PRINTN]

-- Si el tope de la pila es 0 salta el bytecode de false,
-- sino ejecuta el false y salta el bytecode de true
bcc (IfZ info c t f) = do
  bcC <- bcc c
  bcT <- bcc t
  bcF <- bcc f
  let lenTrue = length bcT
  let lenFalse = length bcF
  return $ bcC ++ [CJUMP, lenTrue + 2] ++ bcT ++ [JUMP, lenFalse] ++ bcF


tcc :: MonadFD4 m => TTerm -> m Bytecode
tcc (App _ t1 t2) = do
  t1' <- bcc t1
  t2' <- bcc t2
  return $ t1' ++ t2' ++ [TAILCALL]

tcc (IfZ _ tc tt tf) = do
  c <- bcc tc
  tt' <- tcc tt
  tf' <- tcc tf
  let lenTrue = length tt'
  return $ c ++ [CJUMP, lenTrue] ++ tt' ++ tf'

tcc (Let _ _ _ def (Sc1 term)) = do
  def' <- bcc def
  term' <- tcc term
  return $ def' ++ [SHIFT] ++ term'

tcc term = do
  t' <- bcc term
  return $ t' ++ [RETURN]


-- ord/chr devuelven los codepoints unicode, o en otras palabras
-- la codificación UTF-32 del caracter.
string2bc :: String -> Bytecode
string2bc = map ord

bc2string :: Bytecode -> String
bc2string = map chr

glb2free :: Name -> TTerm -> TTerm
glb2free name = varChangerGlobal  (\v p n -> if n == name then V p (Free n) else V p (Global n))

openModule :: Module -> TTerm
openModule []                         = error "Modulo vacio" 
openModule [Decl p nm ty body]        = body
openModule (Decl p nm ty body: decls) = Let (p, getTy body) nm ty body (close nm $ glb2free nm $ openModule decls)

-- TODO: Funcion para compilar el termino evitando los DROPS al final
--       Seria igual a tcc pero sin usar RETURN sino STOP

bytecompileModule :: MonadFD4 m => Module -> m Bytecode
bytecompileModule m = do bc <- bcc (openModule m) -- fix later
                         return $ bc ++ [STOP]
  


-- | Toma un bytecode, lo codifica y lo escribe un archivo
bcWrite :: Bytecode -> FilePath -> IO ()
bcWrite bs filename = BS.writeFile filename (encode $ BC $ fromIntegral <$> bs)

---------------------------
-- * Ejecución de bytecode
---------------------------

-- | Lee de un archivo y lo decodifica a bytecode
bcRead :: FilePath -> IO Bytecode
bcRead filename = (map fromIntegral <$> un32) . decode <$> BS.readFile filename

runBC :: MonadFD4 m => Bytecode -> m ()
runBC bc = do execVM bc [] []

execVM :: MonadFD4 m => Bytecode -> [Val] -> [Val] -> m ()
execVM [] _ _ = error "Codigo vacio"
execVM (STOP:xs) _ _                 = return ()
execVM (CONST:n:xs) e s              = execVM xs e (I n:s)
execVM (ADD:xs) e (I n:I m:s)        = execVM xs e (I (n+m):s)
execVM (SUB:xs) e (I n:I m:s)        = execVM xs e (I (max 0 (m-n)):s)
execVM (ACCESS:n:xs) e s             = execVM xs e ((e !! n):s)
execVM (CALL:xs) e (v:Fun e' bc: s)  = execVM bc (v:e') (RA e xs:s)
execVM (FUNCTION:len:xs) e s         = execVM (drop len xs) e (Fun e (take len xs):s)
execVM (RETURN:_) _ (val: RA e' c:s) = execVM c e' (val:s)
execVM (SHIFT:xs) e (val:s)          = execVM xs (val:e) s
execVM (DROP:xs) (val:e) s           = execVM xs e s
execVM (PRINTN:xs) e s@(I i:s')      = printFD4 (show i) >> execVM xs e s
execVM (PRINT:xs) e s                = let (str,_:rest) = span (/= NULL) xs
                                       in printFD4inline (bc2string str) >> execVM rest e s
execVM (JUMP:j:xs) e s               = execVM (drop j xs) e s
execVM (CJUMP:j:xs) e ((I n):s)      = case n of
                                        0 -> execVM xs e s
                                        _ -> execVM (drop j xs) e s
execVM (FIX:xs) e ((Fun ef bc):s)    = let efix = Fun efix bc:e 
                                       in execVM xs e (Fun efix bc:s)
execVM (TAILCALL:xs) e (v: Fun e' c': s) = execVM c' (v:e') s 

execVM xs e s = do
  printFD4 (showBC xs)
  error "Caso feo"
