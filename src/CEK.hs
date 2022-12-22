{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module CEK  where

import Lang
import MonadFD4
import Subst
import Common

data Val =
    VNat Int
    | VClosFun (Pos, Ty) Env Name Ty TTerm
    | VClosFix (Pos, Ty) Env Name Ty Name Ty TTerm
    deriving Show

type Env = [Val]

data Frame =
    KArg Env TTerm -- p.[] t
    | KClos Val -- clos []
    | KIfz Env TTerm TTerm -- p.ifz [] then t else e
    | KOp1 BinaryOp Env TTerm -- p.[] (+) u 
    | KOp2 BinaryOp Val --  v (+) []
    | KPrint String -- print str []
    | KLet Env Name TTerm -- p. let x = [] in t
    deriving Show

type Kont = [Frame]


runCEK :: MonadFD4 m => TTerm -> m Val
runCEK t = search t [] []


search :: MonadFD4 m => TTerm -> Env -> Kont -> m Val
search (Print info str t) p k = search t p (KPrint str:k)
search (BinaryOp info op t1 t2) p k = search t1 p (KOp1 op p t2:k)
search (IfZ info t1 t2 t3) p k = search t1 p (KIfz p t2 t3:k)
search (App info t1 t2) p k = search t1 p (KArg p t2:k)
search (V info (Global name)) p k = do
    m <- lookupDecl name
    case m of
        Nothing -> failPosFD4 (fst info) "Variable no declarada"
        Just t -> search t p k
search (V info (Free name)) p k = error "unreachable"
search (V info (Bound i)) p k = destroy (p !! i) k
search (Const info (CNat n)) p k = destroy (VNat n) k
search (Fix info name1 ty1 name2 ty2 (Sc2 t)) p k = destroy (VClosFix info p name1 ty1 name2 ty2 t) k
search (Lam info name ty (Sc1 t)) p k = destroy (VClosFun info p name ty t) k

search (Let info name ty tx (Sc1 tt)) p k = search tx p (KLet p name tt:k)





destroy :: MonadFD4 m => Val -> Kont -> m Val
destroy v@(VNat n) ((KPrint str):ktl) = do printFD4 $ str ++ show n
                                           destroy v ktl
destroy n ((KOp1 op env term):ktl) = search term env (KOp2 op n:ktl)
destroy (VNat n') ((KOp2 Add (VNat val)):ktl) = destroy (VNat (val + n')) ktl
destroy (VNat n') ((KOp2 Sub (VNat val)):ktl) = destroy (VNat (max 0 (val - n'))) ktl
destroy (VNat 0) ((KIfz p t2 t3):ktl) = search t2 p ktl
destroy (VNat n) ((KIfz p t2 t3):ktl) = search t3 p ktl
destroy clos@(VClosFun info env name ty t) ((KArg p t2):ktl) = search t2 p (KClos clos:ktl)
destroy clos@(VClosFix info env name1 fty name2 xty t) ((KArg p t2):ktl) = search t2 p (KClos clos:ktl)
destroy v ((KClos (VClosFun info env x xty t)):ktl) = search t (v:env) ktl
destroy v ((KClos clos@(VClosFix info env f fty x ftx t)):ktl) = search t (v:clos:env) ktl
destroy v ((KLet env name t):ktl) = search t (v:env) ktl
destroy v [] = return v
-- destroy v k = printFD4 (show v) >> printFD4 (show k) >> return (VNat 1)



val2tterm :: Val -> TTerm

val2tterm (VNat n) = Const (NoPos, NatTy) (CNat n)

val2tterm (VClosFun info env name ty tterm) =
  let ls = map val2tterm env
  in substN ls (Lam info name ty (Sc1 tterm))

val2tterm (VClosFix info env f fty x xty tterm) =
  let ls = map val2tterm env
  in substN ls (Fix info f fty x xty (Sc2 tterm))

