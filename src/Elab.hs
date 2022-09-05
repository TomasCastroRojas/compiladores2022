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

module Elab ( elab, elabDecl) where

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
    then  V p (Free v)
    else V p (Global v)

elab' _ (SConst p c) = return $ Const p c


elab' env (SLam p [] t) = return $ elab' env t
elab' env (SLam p ((v,ty):tl) t) = do
  t' <-(elab' (v:env) (SLam p tl t))
  return $ Lam p v ty (close v t')



elab' env (SFix p (f,fty) [(x,xty)] t) = do
  t' <- elab' (x:f:env) t
  return $ Fix p f fty x xty (close2 f x (t'))
elab' env (SFix p (f, fty) ((x, xty):tl) t) = do
  t' <- (elab' (x:f:env) (SLam p tl t))
  return $ Fix p f fty x xty (close2 f x t') 



elab' env (SIfZ p c t e)         = do 
  cc <- elab' env c
  tt <- elab' env t
  ff <- elab' env e
  return $ IfZ p cc tt ff
-- Operadores binarios
elab' env (SBinaryOp i o t u) = do
  t' <- (elab' env t) 
  u' <- (elab' env u)
  return $ BinaryOp i o t' u'
-- Operador Print
elab' env (SPrint i str t) = do
  t' <- (elab' env t)
  return $ Print i str t'
-- Aplicaciones generales
elab' env (SApp p h a) = do 
  h' <- (elab' env h) 
  a' <- (elab' env a)
  return $ App p h' a'


elab' env (SLet False p [(v,vty)] def body) = do
  def' <- (elab' env def)
  body'  <- (elab' (v:env) body)
  return $ Let p v vty def' (close v body')

-- elab' env (SLet False p ((f,fty):tl) def body) =  
--   Let p f fty (elab' env def) (close f (elab' (f:env) (SLam p tl body)))

elab' env (SLet False p ((f,fty):tl) def body) = do
  def' <- (elab' env (SLam p tl def))
  body' <- (elab' (f:env) body)
  return $ Let p f fty def' (close f body')


-- elab' env (SLet p True [(v,vty)] def body) =  
--   Let p v vty (elab' env def) (close v (elab' (v:env) body))

elab' env (SLet True p ((f,fty):tl) def body) = do
  def' <- (elab' env def)
  body' <- (elab' (f:env) (SFix p (f, fty) tl body))
  return $ Let p f fty def' (close f body')

elabTy :: STy -> Ty
elabTy 
elabTy
elabTy 

elabDecl :: MonadFd4 m => Decl STerm -> m Decl Term
elabDecl (SDecl pos name body) = return $ Decl pos name (elab body)
elabDecl (SDeclTy pos name t) = do

  return $ Decl pos name t

--elabDecl :: SDecl STerm -> Decl Term
--elabDecl d@(SDecl True pos name body) = 
--  let term = elab body
--  in Decl pos name term
--elabDecl d@(SDecl False pos name body) = 
--  let term = elab body
--  in Decl pos name term
