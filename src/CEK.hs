import Lang
import MonadFD4

data Val =
    VNat Int 
    | VClosFun Env Name TTerm 
    | VClosFix Env Name Name TTerm
    deriving Show

type Env = [Val]

data Frame = 
    KArg Env TTerm -- p.[] t
    | KClos Val -- clos []
    | KIfz Env TTerm TTerm -- p.ifz [] then t else e
    | KOp1 BinaryOp Env TTerm -- p.[] (+) u 
    | KOp2 BinaryOp Val --  v (+) []
    | KPrint String -- print str []
    deriving Show

type Kont = [Frame]


search :: MonadFD4 m => TTerm -> Env -> Kont -> m Val
search (Print info str t) p k = search t p ((KPrint str):k)
search (BinaryOp info op t1 t2) p k = search t1 p ((KOp1 op p t2):k)
search (IfZ info t1 t2 t3) p k = search t1 p ((KIfz p t2 t3):k)
search (App info t1 t2) p k = search t1 p ((KArg p t2):k)
search (V info (Global name)) p k = do
    m <- lookupDecl name
    case m of
        Nothing -> failPosFD4 (fst info) "Variable no declarada"
        Just t -> do v <- search t p k
                     destroy v k
search (V info (Free name)) p k = error "unreachable"
search (V info (Bound i)) p k = destroy (p !! i) k
search (Const info (CNat n)) p k = destroy (VNat n) k
search (Fix info name1 ty1 name2 ty2 (Sc2 t)) p k = destroy (VClosFix p name1 name2 t) k
search (Lam info name ty (Sc1 t)) p k = destroy (VClosFun p name t) k



destroy :: MonadFD4 m => Val -> Kont -> m Val
destroy val ((KPrint str):ktl) = do printFD4 (str ++ show val)
                                    destroy val ktl
destroy n ((KOp1 op env term):ktl) = search term env ((KOp2 op n):ktl)
destroy (VNat n') ((KOp2 Add (VNat val)):ktl) = destroy (VNat (val + n')) ktl
destroy (VNat n') ((KOp2 Sub (VNat val)):ktl) = destroy (VNat (val - n')) ktl
destroy (VNat 0) ((KIfz p t2 t3):ktl) = search t2 p ktl
destroy (VNat n) ((KIfz p t2 t3):ktl) = search t3 p ktl
destroy clos@(VClosFun env name t) ((KArg p t2):ktl) = search t env ((KClos clos):ktl)
destroy clos@(VClosFix env name1 name2 t) ((KArg p t2):ktl) = search t env ((KClos clos):ktl)
destroy v ((KClos (VClosFun env x t)):ktl) = search t (v:env) ktl
destroy v ((KClos clos@(VClosFix env f x t)):ktl) = search t (clos:v:env) ktl