{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module Opt where
import MonadFD4
import Lang
import Eval (semOp)
import Subst (subst, open, close, open2, close2)
import Control.Monad

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

inline :: MonadFD4 m => TTerm -> m TTerm
inline  (App i (Lam i' name ty scope) nat@(Const i'' c)) = do
    printFD4 "hola"
    return $ subst nat scope
inline  (App i (Lam i' name ty scope) t) = return (Let i name ty t scope)
inline t = do
    printFD4 "Chau"
    return t

freshen :: [Name] -> Name -> Name
freshen ns n = let cands = n : map (\i -> n ++ show i) [0..] 
               in head (filter (`notElem` ns) cands)


visit :: MonadFD4 m => (TTerm -> m TTerm) -> TTerm -> [Name] -> m TTerm
visit f v@(V i var) ns = f v
visit f (Const i c) ns = return $ Const i c

visit f (Lam i name ty t) ns = do
    let n' = freshen ns name
    t' <- visit f (open n' t) ns
    f (Lam i name ty (close n' t'))


visit f (App i l r) ns = do
    l' <- visit f l ns
    r' <- visit f r ns
    f (App i l' r')

visit f (Print i str t) ns = do
    t' <- visit f t ns
    f (Print i str t')

visit f (BinaryOp i op t1 t2) ns = do
    t1' <- visit f t1 ns
    t2' <- visit f t2 ns
    f (BinaryOp i op t1' t2')

visit f (Fix i n1 t1 n2 t2 term) ns = do
    let n1' = freshen ns n1
    let n2' = freshen ns n2 
    term' <- visit f (open2 n1' n2' term) ns
    f (Fix i n1 t1 n2 t2 (close2 n1' n2' term'))

visit f (IfZ info tc tt tf) ns = do
    tc' <- visit f tc ns
    tt' <- visit f tt ns
    tf' <- visit f tf ns
    f (IfZ info tc' tt' tf')

visit f (Let i n ty def t) ns = do
    def' <- visit f def ns
    let n' = freshen ns n
    body' <- visit f (open n' t) ns
    f (Let i n ty def' (close n' body'))

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
optimizeN n t = visit (constantPropagation >=> constantFolding >=> deadCode >=> inline) t [] >>= optimizeN (n-1)

optimize :: MonadFD4 m => Decl TTerm -> m (Decl TTerm)
optimize (Decl p n ty tt) = Decl p n ty <$> optimizeN maxOpt tt
                           