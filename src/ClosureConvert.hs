{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module ClosureConvert where
import IR
import C
import Lang
import MonadFD4
import Subst
import Control.Monad.Writer

varName :: MonadFD4 m => Name -> StateT Int (WriterT [IrDecl] m) Name
varName prefix = do
    n <- get
    put (n+1)
    return (prefix ++ "_" ++ (show n))

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
args2vars :: [Name] -> Ir -> Name -> Ir
args2vars fv t closure = 
    foldr   (\(v, i) ir -> (IrLet v {-tipo??-} (IrAccess (IrVar closure) i) ir))
            t
            (zip fv [1..])


closureConvert :: MonadFD4 m => Term -> StateT Int (WriterT [IrDecl] m) Ir
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
    return $ IrPrint s t'
closureConvert (Let i n ty def body) = do
    let irty = ty2IrTy ty
    def' <- closureConvert def
    body' <- closureConvert (open n body)
    return $ IrLet n irty def' body'

closureConvert t@(Lam i n ty body) = do
    nombreFuncion <- varName n
    let body' = open nombreFuncion body -- se llama a la función dentro de body donde antes había (Bound 0)
    body'' <- closureConvert body'

    let fv = freeVars body'

    -- cuerpo va a tener las variables libres igualadas a alguna posición del entorno de la clausura
    -- y finalmente body''
    let cuerpo = args2vars fv body'' nombreFuncion

    let tipoRetorno = ty2IrTy ty

    let declArgs = map (\n -> (n, {-tipo??-})) fv

    let decl = IrFun nombreFuncion tipoRetorno declArgs cuerpo

    return $ MkClosure nombreFuncion $ map IrVar fv

closureConvert (App info t1 t2) = do
    clos <- closureConvert t1
    t2' <- closureConvert t2
    return $ IrCall (IrAccess clos IrClo 0) [clos, t2'] IrInt
    

runCC :: MonadFD4 m => [Decl Term] -> m [IrDecl]
runCC ((Decl pos name ty body):xs) = undefined