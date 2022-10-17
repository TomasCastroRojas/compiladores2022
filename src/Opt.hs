import MonadFD4 (MonadFD4)
import Lang
import Eval (semOp)
import Subst

optimizeN :: MonadFD4 m => Int -> TTerm -> m TTerm
optimizeN 0 t = return t
optimizeN iters (BinaryOp i op (Const i' (CNat n)) (Const i'' (CNat 0))) =
    return $ Const i (CNat n)
optimizeN iters (BinaryOp i op (Const i' (CNat 0)) (Const i'' (CNat n))) =
    return $ Const i (CNat n)
optimizeN iters (BinaryOp i op (Const i' (CNat n)) (Const i'' (CNat m))) =
    return $ Const i (CNat (semOp op n m))

optimizeN iters (Let info name ty nat@(Const i (CNat n)) scope) =
    return $ subst nat scope

optimizeN iters (Let info name ty def (Sc1 tterm)) = do
    optDef <- optimizeN (iters - 1) def
    optScope <- optimizeN (iters- 1) tterm
    --return $ optimizeN (iters - 1) (Let info name ty optDef (Sc1 optScope))

optimizeN n term = do
    optimizeN (n - 1) term




optimize :: MonadFD4 m => TTerm -> m TTerm
optimize = optimizeN 20