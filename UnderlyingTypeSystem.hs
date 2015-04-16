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

_GammaOr ((x', t):es) x y = if x == x' then t else _GammaOr es x y
_GammaOr [] x y = y

--------------------------------------------------------------------------------
-- Underlying type inference algorithm:

data AType = AugTyInt | AugTyBool | AType :-->: AType | AugTyVar TVar deriving (Show)
type TVar = String
type ATEnv = [(Var, AType)]

data TypeSubst = Id
               | TVar :+->: AType
               | TypeSubst:.:TypeSubst
               deriving (Show)

(|.|) :: TypeSubst -> TypeSubst -> TypeSubst
(|.|) Id th2 = th2
(|.|) th1 Id = th1
(|.|) th1 th2 = th1:.:th2

subst Id t = t
subst th@(tv :+->: ty) AugTyInt = AugTyInt
subst th@(tv :+->: ty) AugTyBool = AugTyBool
subst th@(tv :+->: ty) (t1 :-->: t2) = (subst th t1) :-->: (subst th t2)
subst th@(tv :+->: ty) (AugTyVar a) | tv == a   = ty
                                    | otherwise = AugTyVar a
subst (th1:.:th2) t = subst th1 $ subst th2 t

substEnv :: TypeSubst -> ATEnv -> ATEnv
substEnv th env = map modifyEnv env
  where modifyEnv (x, t) = (x, subst th t)

-- Algorithm W:
_W :: (ATEnv, Exp) -> (AType, TypeSubst)
_W input = (t, th)
  where (t, th, _) = _W' 0 input

_W' :: Int -> (ATEnv, Exp) -> (AType, TypeSubst, Int) -- Returns an unused integer

_W' i (env, Const c) = (constType c, Id, i)

_W' i (env, Var x) = (_GammaOr env x (AugTyVar ('$':x)), Id, i)

_W' i (env, Fn pi x e0) = let ax = freshTVar i
                              (t0, th0, i') = _W' (i+1) ((x, ax):env, e0)
                          in  ((subst th0 ax) :-->: t0, th0, i')

_W' i (env, Fun pi f x e0) = let (ax, a0) = freshTVars i
                                 (t0, th0, i') = _W' (i+1) ((x, ax):(f, ax :-->: a0):env, e0)
                                 th1 = _U (t0, subst th0 a0)
                             in  ((subst th1 (subst th0 ax)) :-->: subst th1 t0, th1|.|th0, i')

_W' i (env, App e1 e2) = let (t1, th1, i') = _W' i (env, e1)
                             (t2, th2, i'') = _W' i' (substEnv th1 env, e2)
                             a = freshTVar i''
                             th3 = _U (subst th2 t1, t2 :-->: a)
                         in  (subst th3 a, th3|.|th2|.|th1, i''+1)

_W' i (env, Op e1 op e2) = let (t1, th1, i') = _W' i (env, e1)
                               (t2, th2, i'') = _W' i' (substEnv th1 env, e2)
                               th3 = _U (subst th2 t1, opType1 op)
                               th4 = _U (subst th3 t2, opType2 op)
                           in  (opType op, th4|.|th3|.|th2|.|th1, i'')

_U :: (AType, AType) -> TypeSubst
_U (AugTyInt, AugTyInt)   = Id
_U (AugTyBool, AugTyBool) = Id
_U (t1 :-->: t2, t1' :-->: t2') = let th1 = _U (t1, t1')
                                      th2 = _U (subst th1 t2, subst th1 t2')
                                  in  th2|.|th1
_U (AugTyVar a, AugTyVar a') | a == a' = Id
_U (t, AugTyVar a) | a `doesNotOccurIn` t = a :+->: t
_U (AugTyVar a, t) | a `doesNotOccurIn` t = a :+->: t
_U (t1, t2) = error ("Could not unify types " ++ show t1 ++ " and " ++ show t2)

-- Helper functions:
constType :: Const -> AType
constType (CInt _) = AugTyInt
constType (CBool _) = AugTyBool

opType :: Op -> AType
opType x | x `elem` [Eq, Fun.LT, LTE, Fun.GT, GTE, Plus, Minus, Times, Div, Mod] = AugTyInt
         | x `elem` [And, Or] = AugTyBool
         | otherwise = error ("Unimplemented type for " ++ show x)
opType1 = opType
opType2 = opType

freshTVar :: Int -> AType
freshTVar i = AugTyVar $ "'a" ++ show i

freshTVars :: Int -> (AType, AType)
freshTVars i = (AugTyVar $ name ++ "_0", AugTyVar $ name ++ "_1")
  where name = "'b" ++ (show i)

doesNotOccurIn :: TVar -> AType -> Bool
doesNotOccurIn a (AugTyVar tv) | a == tv = False
doesNotOccurIn a (t1 :-->: t2) = (a `doesNotOccurIn` t1) && (a `doesNotOccurIn` t2)
doesNotOccurIn a _ = True

-- Pretty print
ppAType :: AType -> String
ppAType AugTyInt = "int"
ppAType AugTyBool = "bool"
ppAType (a :-->: b) = (ppAType a) ++ " --> " ++ (ppAType b)
ppAType (AugTyVar a) = a

ppTypeSubst :: TypeSubst -> String
ppTypeSubst Id = "id"
ppTypeSubst (tv :+->: ty) = tv ++ " +-> " ++ (ppAType ty)
ppTypeSubst (a :.: b) = (ppTypeSubst a) ++ "\n" ++ (ppTypeSubst b)

ppW :: (AType, TypeSubst) -> String
ppW (ty, th) = (ppAType ty) ++ "\n" ++ (ppTypeSubst th)
