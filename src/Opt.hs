{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module Opt where
import MonadFD4
import Lang
import Eval (semOp)
import Subst (subst, open, close, open2, close2, pureTerm, termSize, countBound)

maxOpt :: Int
maxOpt = 10

maxSize :: Int
maxSize = 10

maxCalls :: Int
maxCalls = 5


constantFolding :: MonadFD4 m => TTerm -> m TTerm
constantFolding (BinaryOp i Add t (Const i'' (CNat 0))) = constantFolding t
constantFolding (BinaryOp i Add (Const i' (CNat 0)) t) = constantFolding t
constantFolding (BinaryOp i Sub t (Const i'' (CNat 0))) = constantFolding t
constantFolding (BinaryOp i Sub (Const i' (CNat 0)) t) = return $ Const i (CNat 0)
constantFolding (BinaryOp i op (Const i' (CNat n)) (Const i'' (CNat m))) = return $ Const i (CNat (semOp op n m))
constantFolding (IfZ i (Const i' (CNat 0)) t1 t2) = constantFolding t1
constantFolding (IfZ i (Const i' (CNat n)) t1 t2) = constantFolding t2
constantFolding (Let info name ty nat@(Const i (CNat n)) scope) = return $ subst nat scope
constantFolding t = return t


betaRedex :: MonadFD4 m => TTerm -> m TTerm
betaRedex  (App i f@(Lam i' name ty scope) val@(Const _ _)) | pureTerm f = return $ subst val scope
betaRedex  (App i (Lam i' name ty scope) t) = return (Let i name ty t scope)
betaRedex t = return t

inline :: MonadFD4 m => TTerm -> m TTerm
inline (Let i name ty def body@(Sc1 t)) | calls == 1 || (pureTerm def && termSize def < maxSize && calls < maxCalls) = return $ subst def body
                                                                                                           where calls = countBound 0 t      
inline t = return t

-- Desplaza las constantes a la derecha, habilita constant folding
shiftConst :: MonadFD4 m => TTerm -> m TTerm
shiftConst (BinaryOp i Add (BinaryOp i' Add t (Const i0 (CNat n))) (Const i1 (CNat m))) = return $ BinaryOp i Add t (Const i0 (CNat (n+m)))
shiftConst (BinaryOp i Add (BinaryOp i' Add (Const i0 (CNat n)) t) (Const i1 (CNat m))) = return $ BinaryOp i Add t (Const i0 (CNat (n+m)))
shiftConst (BinaryOp i Add (BinaryOp i' Add t num@(Const _ _)) t') = return $ BinaryOp i Add (BinaryOp i' Add t t') num
shiftConst (BinaryOp i Add (BinaryOp i' Add num@(Const _ _) t) t') = return $ BinaryOp i Add (BinaryOp i' Add t t') num
shiftConst (BinaryOp i Add t (BinaryOp i' Add num@(Const _ _) t')) = return $ BinaryOp i Add (BinaryOp i' Add t t') num
shiftConst (BinaryOp i Add t (BinaryOp i' Add t' num@(Const _ _))) = return $ BinaryOp i Add (BinaryOp i' Add t t') num
shiftConst t = return t

visit :: MonadFD4 m => (TTerm -> m TTerm) -> TTerm -> [Name] -> m TTerm
visit f v@(V i var) ns = f v
visit f (Const i c) ns = return $ Const i c

visit f (Lam i name ty t) ns = do
    let n' = freshen ns name
    t' <- visit f (open n' t) (n':ns)
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
    let n2' = freshen (n1':ns) n2 
    term' <- visit f (open2 n1' n2' term) (n2':n1':ns)
    f (Fix i n1 t1 n2 t2 (close2 n1' n2' term'))

visit f (IfZ info tc tt tf) ns = do
    tc' <- visit f tc ns
    tt' <- visit f tt ns
    tf' <- visit f tf ns
    f (IfZ info tc' tt' tf')

visit f (Let i n ty def t) ns = do
    def' <- visit f def ns
    let n' = freshen ns n
    body' <- visit f (open n' t) (n':ns)
    f (Let i n ty def' (close n' body'))

optimizeN :: MonadFD4 m => Int -> TTerm -> m TTerm
optimizeN 0 t = return t
optimizeN n t = visit (shiftConst >=> constantFolding >=> betaRedex >=> inline) t [] >>= optimizeN (n-1)

optimize :: MonadFD4 m => Decl TTerm -> m (Decl TTerm)
optimize (Decl p n ty tt) = Decl p n ty <$> optimizeN maxOpt tt
                           