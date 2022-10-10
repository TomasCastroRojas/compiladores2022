{-|
Module      : Elab
Description : Elabora un término fully named a uno locally closed.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

Este módulo permite elaborar términos y declaraciones para convertirlas desde
fully named (@STerm) a locally closed (@Term@)
-}

module Elab ( elab, elabDecl, elabTy ) where

import Lang
import Subst
import MonadFD4

-- | 'elab' transforma variables ligadas en índices de de Bruijn
-- en un término dado. 
elab :: MonadFD4 m => STerm -> m Term
elab = elab' []

elab' :: MonadFD4 m =>  [Name] -> STerm -> m Term
elab' env (SV p v) =
  -- Tenemos que ver si la variable es Global o es un nombre local
  -- En env llevamos la lista de nombres locales.
  if v `elem` env
    then  return $ V p (Free v)
    else return $ V p (Global v)

elab' _ (SConst p c) = return $ Const p c


elab' env (SLam p [] t) = failPosFD4 p "Función sin argumentos"
elab' env (SLam p [(v, ty)] t) = do
  t' <- elab' (v:env) t
  ty' <- elabTy ty
  return $ Lam p v ty' (close v t')
elab' env (SLam p ((v,ty):tl) t) = do
  t' <- elab' (v:env) (SLam p tl t)
  ty' <- elabTy ty
  return $ Lam p v ty' (close v t')


elab' env (SFix p (f,fty) [] t) = failPosFD4 p "Fix sin argumentos"
elab' env (SFix p (f,fty) [(x,xty)] t) = do
  t'   <- elab' (x:f:env) t
  fty' <- elabTy fty
  xty' <- elabTy xty
  return $ Fix p f fty' x xty' (close2 f x t')
elab' env (SFix p (f, fty) ((x, xty):tl) t) = do
  t'   <- elab' (x:f:env) (SLam p tl t)
  fty' <- elabTy fty
  xty' <- elabTy xty
  return $ Fix p f fty' x xty' (close2 f x t')



elab' env (SIfZ p c t e)         = do
  cc <- elab' env c
  tt <- elab' env t
  ff <- elab' env e
  return $ IfZ p cc tt ff
-- Operadores binarios
elab' env (SBinaryOp i o t u) = do
  t' <- elab' env t
  BinaryOp i o t' <$> elab' env u
-- Operador Print
elab' env (SPrint i str t) = do
  Print i str <$> elab' env t
-- Aplicaciones generales
elab' env (SApp p h a) = do
  h' <- elab' env h
  App p h' <$> elab' env a

elab' env (SLet _ p [] _ _) = failPosFD4 p "Let vacio"
elab' env (SLet _ p [(name, ty)] def body) = do
  def' <- elab' env def
  ty' <- elabTy ty
  body' <- elab' (name:env) body
  return $ Let p name ty' def' (close name body')
elab' env (SLet False p ((v,rty):xs) def body) = do
  def' <- elab' env (SLam p xs def)
  rty' <- elabTy $ buildFunTy xs rty
  body' <- elab' (v:env) body
  return $ Let p v rty' def' (close v body')

elab' env (SLet True p ((f,rty):xs) def body) =
  let rty' = buildFunTy xs rty in do
  def' <- elab' env (SFix p (f,rty') xs def)
  ty <- elabTy rty'
  body' <- elab' (f : env) body
  return $ Let p f ty def' (close f body')

elabTy :: MonadFD4 m => STy -> m Ty
elabTy SNatTy = return NatTy
elabTy (SFunTy t1 t2) = do
  t1' <- elabTy t1
  t2' <- elabTy t2
  return $ FunTy t1' t2'
elabTy (SNameTy name) = do
  tipo <- lookupTypeSin name
  case tipo of
    Nothing -> failFD4 $ "Sinónimo de tipo no declarado " ++ show name
    (Just t) -> return $ VarTy name t

elabDecl :: MonadFD4 m => SDecl STerm -> m (Decl Term)
elabDecl (SDecl pos [(n, sty)] body _) = do
  body' <- elab body
  ty <- elabTy sty
  return $ Decl pos n ty body'
elabDecl (SDecl pos ((n, sty):bs) body False) = do
  body' <- elab (SLam pos bs body)
  fty <- elabTy $ buildFunTy bs sty
  return $ Decl pos n fty body'
elabDecl (SDecl pos ((n, sty):bs) body True) = do
  body' <- elab (SFix pos (n, buildFunTy bs sty) bs body)
  ty <- elabTy $ buildFunTy bs sty
  return $ Decl pos n ty body'
elabDecl _ = failFD4 "Unreacheable error"


buildFunTy :: [(Name, STy)] -> STy -> STy
buildFunTy xs sty = foldr1 SFunTy (map snd xs ++ [sty])