module Opt where
import MonadFD4 (MonadFD4)
import Lang
import Eval (semOp)
import Subst (subst)

maxOpt :: Int
maxOpt = 10

constantFolding :: MonadFD4 m => TTerm -> m TTerm
constantFolding (BinaryOp i Add t (Const i'' (CNat 0))) = constantFolding t
constantFolding (BinaryOp i Add (Const i' (CNat 0)) t) = constantFolding t
constantFolding (BinaryOp i Sub t (Const i'' (CNat 0))) = constantFolding t
constantFolding (BinaryOp i Sub (Const i' (CNat 0)) t) =
    return $ Const i (CNat 0)
constantFolding (BinaryOp i op (Const i' (CNat n)) (Const i'' (CNat m))) =
    return $ Const i (CNat (semOp op n m))
constantFolding t = return t

constantPropagation :: MonadFD4 m => TTerm -> m TTerm
constantPropagation (Let info name ty nat@(Const i (CNat n)) scope) =
    return $ subst nat scope
constantPropagation t = return t


deadCode :: MonadFD4 m => TTerm -> m TTerm
deadCode (IfZ i (Const i' (CNat 0)) t1 t2) = deadCode t1
deadCode (IfZ i (Const i' (CNat n)) t1 t2) = deadCode t2
deadCode t = return t


{-
TODO >> Abstraccion de recorrido del AST, evita reescribir todos los casos de TTerm en cada funcion


visit :: Monad m => (TTerm -> m TTerm) -> TTerm -> m TTerm
visit f (App i l r) = do
    l' <- visit f l
    r' <- visit f r
    f (App i l' r')


br = visit br1 where
    br1 (App (Lam ...) v) = algo 
    br1 t = return t
-}

optimizeN :: MonadFD4 m => Int -> TTerm -> m TTerm
optimizeN 0 t = return t
optimizeN n t = constantPropagation t >>= constantFolding >>= deadCode >>= optimizeN (n-1)

optimize :: MonadFD4 m => Decl TTerm -> m (Decl TTerm)
optimize (Decl p n ty tt) = Decl p n ty <$> optimizeN maxOpt tt
                           