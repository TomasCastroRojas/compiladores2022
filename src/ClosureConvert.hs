{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use second" #-}
module ClosureConvert where
import IR
import Lang
import MonadFD4
import Subst
import Control.Monad.Writer

varName :: MonadFD4 m => Name -> StateT Int (WriterT [IrDecl] m) Name
varName prefix = do
    n <- get
    put (n+1)
    return (prefix ++ "-" ++  show n)

var2ir :: Var -> Ir
var2ir (Free name) = IrVar name
var2ir (Global name)  = IrGlobal name
var2ir (Bound _) = undefined

ty2IrTy :: Ty -> IrTy
ty2IrTy NatTy = IrInt
ty2IrTy (FunTy _ _) = IrFunTy
ty2IrTy (VarTy _ ty) = ty2IrTy ty


{--
Toma lista de variables [v1...vn], un termino t, y el nombre de una clausura
Genera algo como
let
    v1 = closure[1]
    ...
    vn = closure[n]
in
    t
--}
args2vars :: [(Name, Ty)] -> Ir -> Name -> Ir
args2vars fv t closure =
    foldr   (\((v, ty), i) ir -> IrLet v (ty2IrTy ty) (IrAccess (IrVar closure) (ty2IrTy ty) i) ir)
            t
            (zip fv [1..])


closureConvert :: MonadFD4 m => TTerm -> StateT Int (WriterT [IrDecl] m) Ir
closureConvert (V info var) = return $ var2ir var
closureConvert (Const info c) = return $ IrConst c
closureConvert (IfZ info c t f) = do
    irc <- closureConvert c
    irt <- closureConvert t
    irf <- closureConvert f
    return $ IrIfZ irc irt irf
closureConvert (BinaryOp info op t1 t2) = do
    t1' <- closureConvert t1
    t2' <- closureConvert t2
    return $ IrBinaryOp op t1' t2'
closureConvert (Print info s t) = do
    t' <- closureConvert t
    printname <- varName "print"
    return $ IrLet printname IrInt t' (IrPrint s (IrVar printname))
closureConvert (Let i n ty def body) = do
    let irty = ty2IrTy ty
    name <- varName n
    def' <- closureConvert def
    body' <- closureConvert (open name body)
    return $ IrLet name irty def' body'

closureConvert t@(Lam i n ty body@(Sc1 b)) = do
    nombreFuncion <- varName "f"
    nombreArg <- varName n
    let body' = open nombreArg body -- se llama al argumento dentro de body donde antes había (Bound 0)
    body'' <- closureConvert body'

    let fv = freeVarsTy b

    closure <- varName (nombreFuncion ++ "clos")

    -- cuerpo va a tener las variables libres igualadas a alguna posición del entorno de la clausura
    -- y finalmente body''
    let cuerpo = args2vars fv body'' closure
    let tipoRetorno = ty2IrTy ty

    let decl = IrFun nombreFuncion tipoRetorno [(closure, IrClo), (nombreArg, IrInt)] cuerpo
    tell [decl]

    return $ MkClosure nombreFuncion $ map (IrVar . fst) fv

closureConvert t@(Fix i fn fty vn vty body@(Sc2 b)) = do
    nombreFuncion <- varName ("fix_" ++ fn)
    nombreArg <- varName vn
    closure <- varName (nombreFuncion ++ "clos")
    let body' = open2 closure nombreArg body
    body'' <- closureConvert body'

    let fv = freeVarsTy b

    let cuerpo = args2vars fv body'' closure
    let tipoRetorno = ty2IrTy fty

    let decl = IrFun nombreFuncion tipoRetorno [(closure, IrClo), (nombreArg, IrInt)] cuerpo
    tell [decl]

    return $ MkClosure nombreFuncion $ map (IrVar . fst) fv

closureConvert (App info t1 t2) = do
    clos <- closureConvert t1
    t2' <- closureConvert t2
    fun <- varName "fun"
    return $ IrLet fun IrClo clos $ IrCall (IrAccess (IrVar fun) IrClo 0) [IrVar fun, t2'] IrInt


runCC :: MonadFD4 m => [Decl TTerm] -> m [IrDecl]
runCC = runCC' 0

-- Mejor usar mapM y luego correr las monadas una unica vez
-- Esta haciendo el bind de ambas monadas manualmente
runCC' :: MonadFD4 m => Int -> [Decl TTerm] -> m [IrDecl]
runCC' _ [] = return []
runCC' s list@(dec@(Decl pos name ty body):xs) = do
    ((ir, i), ls) <- runWriterT $ runStateT (closureConvert body) s
    let newDecl = IrVal name (ty2IrTy ty) ir
    tl <- runCC' (i + 1) xs
    return $ newDecl : ls ++ tl
