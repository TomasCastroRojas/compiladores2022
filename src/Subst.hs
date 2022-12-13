{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE GADTs #-}
{-|
Module      : Subst
Description : Define las operaciones de la representacion locally nameless
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

Este módulo define las operaciones de la representacion locally nameless,
y la substitución.

-}

module Subst where

import Lang
import Common

-- Esta es una función auxiliar que usan el resto de las funciones de este módulo
-- para modificar las vsriables (ligadas y libres) de un término
varChanger :: (Int -> info -> Name -> Tm info Var) --que hacemos con las variables localmente libres
           -> (Int -> info -> Int ->  Tm info Var) --que hacemos con los indices de De Bruijn
           -> Tm info Var -> Tm info Var
varChanger local bound t = go 0 t where
  go n   (V p (Bound i)) = bound n p i
  go n   (V p (Free x)) = local n p x 
  go n   (V p (Global x)) = V p (Global x) 
  go n (Lam p y ty (Sc1 t))   = Lam p y ty (Sc1 (go (n+1) t))
  go n (App p l r)   = App p (go n l) (go n r)
  go n (Fix p f fty x xty (Sc2 t)) = Fix p f fty x xty (Sc2 (go (n+2) t))
  go n (IfZ p c t e) = IfZ p (go n c) (go n t) (go n e)
  go n t@(Const _ _) = t
  go n (Print p str t) = Print p str (go n t)
  go n (BinaryOp p op t u) = BinaryOp p op (go n t) (go n u)
  go n (Let p v vty m (Sc1 o)) = Let p v vty (go n m) (Sc1 (go (n+1) o))

-- `open n t` reemplaza la primera variable ligada
-- en `t` (que debe ser un Scope con una sola variable que 
-- escapa al término) por el nombre libre `n`.
-- La variable Bound 0 pasa a ser Free n. El nombre `n`
-- debe ser fresco en el término para que no ocurra shadowing.
open :: Name -> Scope info Var -> Tm info Var
open nm (Sc1 t) = varChanger (\_ p n -> V p (Free n)) bnd t
   where bnd depth p i | i <  depth = V p (Bound i)
                       | i == depth =  V p (Free nm)
                       | otherwise  = abort "open: M is not LC"

-- `open2 n1 n2 t` reemplaza la primeras dos variables ligadas en `t`, que debe ser
-- un Scope con dos variables ligadas que escapan al término.
open2 :: Name -> Name -> Scope2 info Var -> Tm info Var
open2 nm1 nm2 (Sc2 t) = varChanger (\_ p n -> V p (Free n)) bnd t
   where bnd depth p i | i <  depth   = V p (Bound i)
                       | i == depth   = V p (Free nm2)
                       | i == depth+1 = V p (Free nm1)
                       | otherwise  = abort "open2: M is not LC"

-- `subst u t` sustituye el índice de de Bruijn 0 en t con
-- el término u (Bound 0 pasa a ser u). Notar que t es un Scope 
-- con un solo índice que escapa el término.
-- Puede pensarse como una optimizacíon de primero hacer `open
-- n t`, con nombres frescos, y luego sustituir los nombres
-- por los términos correspondientes. La ventaja es que no hace falta
-- generar ningún nombre, y por lo tanto evitamos la necesidad de
-- nombres frescos.
subst :: Tm info Var -> Scope info Var -> Tm info Var
subst n (Sc1 m) = varChanger (\_ p n -> V p (Free n)) bnd m
   where bnd depth p i 
             | i <  depth = V p (Bound i)
             | i == depth = n
             | otherwise  = abort "subst: M is not LC"

-- `subst2 u1 u2 t1 sustituye índice de de Bruijn 0 en t por u1 y el índice 1 por u2. 
-- Notar que t es un Scope con dos índices que escapan el término.
subst2 :: Tm info Var -> Tm info Var -> Scope2 info Var -> Tm info Var
subst2 n1 n2 (Sc2 m) = varChanger (\_ p n -> V p (Free n)) bnd m
   where bnd depth p i 
             | i <  depth = V p (Bound i)
             | i == depth = n2
             | i == depth+1 = n1
             | otherwise  = abort "subst2: M is not LC"

-- Peligroso (no usa scopes)
--
-- `substN [t0,..,tn] t` sustituye los índices de de Bruijn en t con
-- los términos de la lista. Bound 0 pasa a t0, etc.
--
-- El término `t` debe tener a lo sumo tantos índices abiertos como
-- la longitud de la lista. Si es localmente cerrado (i.e. no tiene
-- índices abiertos), nada va a ser sustituido.
--
-- Puede pensarse como una optimizacíon de primero hacer `open
-- [n0,..,nn] t`, con nombres frescos, y luego sustituir los nombres
-- por los términos correspondientes. La ventaja es que no hace falta
-- generar ningún nombre, y por lo tanto evitamos la necesidad de
-- nombres frescos.
substN :: [Tm info Var] -> Tm info Var -> Tm info Var
substN ns = varChanger (\_ p n -> V p (Free n)) bnd
   where bnd depth p i
             | i <  depth = V p (Bound i)
             | i >= depth && i < depth + nns
                = ns !! (i - depth)
             | otherwise = abort "substN: M is not LC"
         nns = length ns

-- `close n t` es la operación inversa a open. Reemplaza
-- las variables `Free n` por la variable ligada `Bound 0`.
close :: Name -> Tm info Var -> Scope info Var
close nm t = Sc1 (varChanger lcl (\_ p i -> V p (Bound i)) t)
 where lcl depth p y =
            if y==nm then V p (Bound depth)
                     else V p (Free y)

-- Similar a `close` pero para el caso de cerrar dos nombres.
close2 :: Name -> Name -> Tm info Var -> Scope2 info Var
close2 nm1 nm2 t = Sc2 (varChanger lcl (\_ p i -> V p (Bound i)) t)
  where lcl depth p y | y == nm2 = V p (Bound depth)
                      | y == nm1 = V p (Bound (depth + 1))
                      | otherwise = V p (Free y)



-- Esta es una función auxiliar que usan el resto de las funciones de este módulo
-- para modificar las vsriables (ligadas y libres) de un término
varChangerGlobal :: (Int -> info -> Name -> Tm info Var) --que hacemos con las variables localmente libres
                     -> Tm info Var -> Tm info Var
varChangerGlobal local t = go 0 t where
  go n   (V p (Bound i)) = (V p (Bound i))
  go n   (V p (Free x)) = (V p (Free x))
  go n   (V p (Global x)) =  local n p x
  go n (Lam p y ty (Sc1 t))   = Lam p y ty (Sc1 (go (n+1) t))
  go n (App p l r)   = App p (go n l) (go n r)
  go n (Fix p f fty x xty (Sc2 t)) = Fix p f fty x xty (Sc2 (go (n+2) t))
  go n (IfZ p c t e) = IfZ p (go n c) (go n t) (go n e)
  go n t@(Const _ _) = t
  go n (Print p str t) = Print p str (go n t)
  go n (BinaryOp p op t u) = BinaryOp p op (go n t) (go n u)
  go n (Let p v vty m (Sc1 o)) = Let p v vty (go n m) (Sc1 (go (n+1) o))


-- Determina el tamaño de un termino
termSize :: TTerm -> Int
termSize (V x0 var) = 1
termSize (Const x0 co) = 1
termSize (Lam x0 s ty (Sc1 t)) = 1 + termSize t
termSize (App x0 t t') = 1 + termSize t + termSize t'
termSize (Print x0 s t) = 1 + termSize t
termSize (BinaryOp x0 bo t t') = 1 + termSize t + termSize t'
termSize (Fix x0 s ty str ty' (Sc2 t)) = 1 + termSize t
termSize (IfZ x0 t t' t'') = 1 + termSize t + termSize t' + termSize t''
termSize (Let x0 s ty t (Sc1 t')) = 1 + termSize t + termSize t'

-- Verifica que el termino no tenga efectos
pureTerm :: TTerm -> Bool
pureTerm (V x0 (Bound n)) = True
pureTerm (V x0 (Free s)) = True
pureTerm (V x0 (Global s)) = False
pureTerm (Const x0 co) = True
pureTerm (Lam x0 s ty (Sc1 t)) = pureTerm t
pureTerm (App x0 t t') = pureTerm t && pureTerm t'
pureTerm (Print x0 s tm') = False
pureTerm (BinaryOp x0 bo t t') = pureTerm t && pureTerm t'
pureTerm (Fix x0 s ty str ty' (Sc2 t)) = pureTerm t
pureTerm (IfZ x0 t t' t'') = pureTerm t && pureTerm t' && pureTerm t''
pureTerm (Let x0 s ty t (Sc1 t')) = pureTerm t && pureTerm t'

-- Cuenta la cantidad de apariciones de una variable ligada
countBound :: Int -> Tm info Var -> Int
countBound n (V p (Bound i)) = if i == n then 1 else 0
countBound n (V _ _) = 0
countBound n (Const _ _) = 0
countBound n (Lam p y ty (Sc1 t)) = countBound (n+1) t
countBound n (App p t t')   = countBound n t + countBound n t
countBound n (Fix p f fty x xty (Sc2 t)) = countBound (n+2) t
countBound n (IfZ p c t e) = countBound n c + countBound n t + countBound n e
countBound n (Print p str t) = countBound n t
countBound n (BinaryOp p op t u) = countBound n t + countBound n u
countBound n (Let p v vty m (Sc1 t)) = countBound n m + countBound (n+1) t
