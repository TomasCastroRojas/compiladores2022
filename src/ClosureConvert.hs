module ClosureConvert where
import IR
import C
import Lang
import MonadFD4
import Control.Monad.Writer

varName :: Var -> Int -> Ir 
varName (Global name) _ = IrGlobal ("_" ++ name)
varName (Bound i) count = IrVar ("__x" ++ show count)
varName (Free n) _ = undefined

closureConvert :: MonadFD4 m => Term -> StateT Int (WriterT [IrDecl] m) Ir
closureConvert (V info var) = do
    c <- get
    put (c+1)
    return $ varName var c
closureConvert (Const info const) = return $ IrConst const
closureConvert (App info t1 t2) = do
    ct1 <- closureConvert t1
    ct2 <- closureConvert t2
    return IrCall 
runCC :: [Decl Term] -> [IrDecl]
runCC = undefined