{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use <$>" #-}
{-|
Module      : Parse
Description : Define un parser de términos FD40 a términos fully named.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

-}

module Parse (tm, Parse.parse, decl, runP, P, program, declOrTm) where

import Prelude hiding ( const )
import Lang hiding (getPos)
import Global
import Common
import Text.Parsec hiding (runP,parse)
--import Data.Char ( isNumber, ord )
import qualified Text.Parsec.Token as Tok
import Text.ParserCombinators.Parsec.Language --( GenLanguageDef(..), emptyDef )
import qualified Text.Parsec.Expr as Ex
import Text.Parsec.Expr (Operator, Assoc)
import Control.Monad.Identity (Identity)

type P = Parsec String ()

-----------------------
-- Lexer
-----------------------
-- | Analizador de Tokens
lexer :: Tok.TokenParser u
lexer = Tok.makeTokenParser langDef

langDef :: LanguageDef u
langDef = emptyDef {
         commentLine    = "#",
         reservedNames = ["let", "rec","fun", "fix", "then", "else","in",
                           "ifz", "print","Nat","type"],
         reservedOpNames = ["->",":","=","+","-"]
        }

whiteSpace :: P ()
whiteSpace = Tok.whiteSpace lexer

natural :: P Integer 
natural = Tok.natural lexer

stringLiteral :: P String
stringLiteral = Tok.stringLiteral lexer

parens :: P a -> P a
parens = Tok.parens lexer

identifier :: P String
identifier = Tok.identifier lexer

reserved :: String -> P ()
reserved = Tok.reserved lexer

reservedOp :: String -> P ()
reservedOp = Tok.reservedOp lexer

tyIdentifier :: P String
tyIdentifier = Tok.lexeme lexer $ do
  c  <- upper
  cs <- many (identLetter langDef)
  return (c:cs)

-----------------------
-- Parsers
-----------------------

num :: P Int
num = fromInteger <$> natural

var :: P Name
var = identifier

getPos :: P Pos
getPos = do pos <- getPosition
            return $ Pos (sourceLine pos) (sourceColumn pos)

tyatom :: P STy
tyatom = (reserved "Nat" >> return SNatTy)
         <|> parens typeP

typeP :: P STy
typeP = try (do 
          x <- tyatom
          reservedOp "->"
          y <- typeP
          return (SFunTy x y))
      <|> tyatom
          
const :: P Const
const = CNat <$> num

printOp :: P STerm
printOp = do
  i <- getPos
  reserved "print"
  str <- option "" stringLiteral
  ( do  a <- atom
        return (SPrint i str a)
    <|> return (SLam i [("x", SNatTy)] (SPrint i str (SV i "x")))) 


binary :: String -> BinaryOp -> Assoc -> Operator String () Identity STerm
binary s f = Ex.Infix (reservedOp s >> return (SBinaryOp NoPos f))

table :: [[Operator String () Identity STerm]]
table = [[binary "+" Add Ex.AssocLeft,
          binary "-" Sub Ex.AssocLeft]]

expr :: P STerm
expr = Ex.buildExpressionParser table tm

atom :: P STerm
atom =     (flip SConst <$> const <*> getPos)
       <|> flip SV <$> var <*> getPos
       <|> parens expr
       <|> printOp

-- parsea un par (variable : tipo)
binding :: P (Name, STy)
binding = do v <- var
             reservedOp ":"
             ty <- typeP
             return (v, ty)

binders :: P [(Name, STy)]
binders = do 
  lst <- many1 $ (parens binding <|> binding)
  return lst

lam :: P STerm
lam = do i <- getPos
         reserved "fun"
         bnds <- binders
         reservedOp "->"
         t <- expr
         return (SLam i bnds t)



-- Nota el parser app también parsea un solo atom.
app :: P STerm
app = do i <- getPos
         f <- atom
         args <- many atom
         return (foldl (SApp i) f args)

ifz :: P STerm
ifz = do i <- getPos
         reserved "ifz"
         c <- expr
         reserved "then"
         t <- expr
         reserved "else"
         e <- expr
         return (SIfZ i c t e)

fix :: P STerm
fix = do i <- getPos
         reserved "fix"
         (f, fty) <- parens binding
         args <- many $ (parens binding) <|> binding
         reservedOp "->"
         t <- expr
         return (SFix i (f,fty) args t)


letexp :: P STerm
letexp = do
  i <- getPos
  reserved "let"
  (v,ty) <- (parens binding <|> binding)
  reservedOp "="  
  def <- expr
  reserved "in"
  body <- expr
  return (SLet False i [(v,ty)] def body)


  
letexpFun :: P STerm
letexpFun = do
  i <- getPos
  reserved "let"
  (name, lst@((v, ty):tl), retType) <- parse_func
  reservedOp "=" 
  def <- expr
  reserved "in"
  body <- expr
  return (SLet False i ([(name, buildFunTy lst retType)] ++ lst) def body)



-- parsea algo de la forma
-- f (x1:T1) ... (nx:Tn) : Tr
parse_func :: P (Name, [(Name, STy)], STy)
parse_func = do
  name <- var
  args <- many $ (parens binding) <|> binding
  reservedOp ":"
  retType <- typeP
  return (name, args, retType)


-- toma una lista con lista de argumentos de una función y sus tipos
-- y el tipo que retorna una función y crea el tipo de la función
buildFunTy :: [(Name, STy)] -> STy -> STy
buildFunTy [] retType = retType
buildFunTy ((x, xty):tl) retType = (SFunTy xty (buildFunTy tl retType))


letrecexp :: P STerm
letrecexp = do
  i <- getPos
  reservedOp "let"
  reservedOp "rec"
  (name, lst@((v, ty):tl), retType) <- parse_func
  reservedOp "=" 
  def <- expr
  reserved "in"
  body <- expr
  return (SLet True i ([(name, buildFunTy lst retType)] ++ lst) def body)




-- | Parser de términos
tm :: P STerm
tm = app <|> lam <|> ifz <|> printOp <|> fix  <|> try letexpFun <|> (try letexp <|> letrecexp)



decl_let :: P (SDecl STerm)
decl_let = do
  i <- getPos
  reservedOp "let"
  (x, xty) <- parens binding <|> binding
  reservedOp "="
  body <- expr
  return $ SDecl  i x body

decl_letfun :: P (SDecl STerm)
decl_letfun = do 
  i <- getPos
  reservedOp "let"
  (name, lst@((v, ty):tl), retType) <- parse_func
  reservedOp "="
  body <- expr
  return $ SDecl  i name body


decl_letrec :: P (SDecl STerm)
decl_letrec = do 
  i <- getPos
  reservedOp "let"
  reservedOp "rec"
  (name, lst@((v, ty):tl), retType) <- parse_func
  reservedOp "=" 
  body <- expr
  return $ SDecl i name body


decl_typeDef :: P (SDecl STerm)
decl_typeDef = do
  i <- getPos
  reservedOp "type"
  n <- var
  reservedOp "="
  ty <- typeP
  return (SDeclTy i n ty)

-- | Parser de declaraciones
decl :: P (SDecl STerm)
decl = decl_letfun <|> decl_letrec <|> decl_let


-- | Parser de programas (listas de declaraciones) 
program :: P [SDecl STerm]
program = many decl

-- | Parsea una declaración a un término
-- Útil para las sesiones interactivas
declOrTm :: P (Either (SDecl STerm) STerm)
declOrTm =  try (Left <$> decl) <|> (Right <$> expr)

-- Corre un parser, chequeando que se pueda consumir toda la entrada
runP :: P a -> String -> String -> Either ParseError a
runP p s filename = runParser (whiteSpace *> p <* eof) () filename s

--para debugging en uso interactivo (ghci)
parse :: String -> STerm
parse s = case runP expr s "" of
            Right t -> t
            Left e -> error ("no parse: " ++ show s)
