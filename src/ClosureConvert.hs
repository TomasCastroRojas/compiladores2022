{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module ClosureConvert where
import IR
import C
import Lang
import MonadFD4
import Subst
import Control.Monad.Writer

varName :: Var -> Int -> Ir
varName (Global name) _ = IrGlobal ("_" ++ name)
varName (Bound i) count = IrVar ("__x" ++ show count)
varName (Free n) count = varName (Global n) count

ty2IrTy :: Ty -> IrTy
ty2IrTy NatTy = IrInt
ty2IrTy (FunTy _ _) = IrFunTy
ty2IrTy (VarTy _ ty) = ty2IrTy ty

closureConvert :: MonadFD4 m => Term -> StateT Int (WriterT [IrDecl] m) Ir
closureConvert (V info var) = do
    c <- get
    put (c+1)
    return $ varName var c
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
closureConvert t@(Lam i n ty body) = return $ MkClosure n $ map IrVar $ freeVars t
closureConvert (App info t1 t2) = do
    clos <- closureConvert t1
    t2' <- closureConvert t2
    return $ IrCall (IrAccess clos IrClo 0) [clos, t2'] IrInt


runCC :: MonadFD4 m => [Decl Term] -> m [IrDecl]
runCC ((Decl pos name ty body):xs) = undefined