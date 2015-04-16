module UnderlyingTypeSystem where

import Fun

--------------------------------------------------------------------------------
-- Type system:

data Type = TyInt | TyBool | Type :->: Type deriving (Show)
type TEnv = [(Var, Type)]

--dom ((x, _):es) = x : dom es
--dom [] = []

_Gamma ((x', t):es) x = if x == x' then t else _Gamma es x
_Gamma [] x = error ("Type not found: " ++ show x)

--------------------------------------------------------------------------------
-- Underlying type inference algorithm:

data AType = AugTyInt | AugTyBool | AType :-->: AType | AugTyVar TVar deriving (Show)
type TVar = String
type ATEnv = [(Var, AType)]

type TypeSubst = AType -> AType

(+->) :: TVar -> AType -> (AType -> AType)
(+->) a t = doSub a t
  where doSub tv ty AugTyInt = AugTyInt
        doSub tv ty AugTyBool = AugTyBool
        doSub tv ty (t1 :-->: t2) = (doSub tv ty t1) :-->: (doSub tv ty t2)
        doSub tv ty (AugTyVar a) | tv == a   = ty
                               | otherwise = AugTyVar a

-- Algorithm W:
_W :: (ATEnv, Exp) -> (AType, TypeSubst)

_W (env, Const c) = (constType c, id)

_W (env, Var x) = (_Gamma env x, id)

_W (env, Fn pi x e0) = let ax = freshTVar env
                           (t0, th0) = _W ((x, ax):env, e0)
                       in  ((th0 ax) :-->: t0, th0)

_W (env, Fun pi f x e0) = let (ax, a0) = freshTVars env
                              (t0, th0) = _W ((x, ax):(f, ax :-->: a0):env, e0)
                              th1 = _U (t0, th0 a0)
                          in  ((th1 (th0 ax)) :-->: th1 t0, th1.th0)

_U :: (AType, AType) -> TypeSubst
_U (AugTyInt, AugTyInt)   = id
_U (AugTyBool, AugTyBool) = id
_U (t1 :-->: t2, t1' :-->: t2') = let th1 = _U (t1, t1')
                                      th2 = _U (th1 t2, th1 t2')
                                  in  th2.th1
_U (AugTyVar a, AugTyVar a') | a == a' = id
_U (t, AugTyVar a) | a `doesNotOccurIn` t = a +-> t
_U (AugTyVar a, t) | a `doesNotOccurIn` t = a +-> t
_U (t1, t2) = error ("Could not unify types " ++ show t1 ++ " and " ++ show t2)

-- Helper functions:
constType :: Const -> AType
constType (CInt _) = AugTyInt
constType (CBool _) = AugTyBool

freshTVar :: ATEnv -> AType
freshTVar env = AugTyVar $ tryName 0
  where tryName i = if env `containsTVar` (mkName i) then tryName (i+1) else (mkName i)
        mkName i = "\'a" ++ show i

freshTVars :: ATEnv -> (AType, AType)
freshTVars env = (AugTyVar $ name ++ "_0", AugTyVar $ name ++ "_1")
  where name = tryName 0
        tryName i = if env `containsTVar` ((mkName i) ++ "_0") then tryName (i+1) else (mkName i)
        mkName i = "\'b" ++ show i

containsTVar :: ATEnv -> TVar -> Bool
containsTVar ((x, AugTyVar tv):es) a | a == tv   = True
                                     | otherwise = containsTVar es a
containsTVar ((_, _):es) a = containsTVar es a
containsTVar _ a = False

--subst :: TypeSubst -> AType -> AType
--subst Id t = t
--subst s@(Subst tv ty) AugTyInt = AugTyInt
--subst s@(Subst tv ty) AugTyBool = AugTyBool
--subst s@(Subst tv ty) (t1 :-->: t2) = (subst s t1) :-->: (subst s t2)
--subst s@(Subst tv ty) (AugTyVar a) | tv == a = ty
--                                   | otherwise   = AugTyVar a
--subst (th1 :.: th2) t = subst th1 $ subst th2 t

doesNotOccurIn :: TVar -> AType -> Bool
doesNotOccurIn a (AugTyVar tv) | a == tv = False
doesNotOccurIn a (t1 :-->: t2) = (a `doesNotOccurIn` t1) && (a `doesNotOccurIn` t2)
doesNotOccurIn a _ = True
