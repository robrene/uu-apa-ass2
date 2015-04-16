module ControlFlowAnalysis where

import Fun
import qualified Data.Set as S

--------------------------------------------------------------------------------
-- Annotated types:

data SType = STyInt | STyBool | STyFunc AVar SType SType | STyVar TVar deriving (Show)
type TVar = String
type AVar = String
data SAnn = SAPnt Pnt | SAnn :++: SAnn | SAEmpty | SAVar AVar deriving (Show)

(-|) :: SType -> AVar -> (SType -> SType)
(-|) t1 b = \t2 -> STyFunc b t1 t2
(|>) :: (SType -> SType) -> SType -> SType
(|>) arr t2 = arr t2

infixl 6 -|
infixl 6 |>

type TEnv = [(Var, SType)]

_Gamma ((x', t):es) x = if x == x' then t else _Gamma es x
_Gamma [] x = error ("Type not found: " ++ show x)

_GammaOr ((x', t):es) x y = if x == x' then t else _GammaOr es x y
_GammaOr [] x y = y

type ConstraintSet = S.Set (AVar, Pnt)

--------------------------------------------------------------------------------
-- Substitutions:

data SimpleSubst = Id
                 | TVar :+->: SType
                 | AVar :+>>: AVar
                 | SimpleSubst:.:SimpleSubst
                 deriving (Show)

(|.|) :: SimpleSubst -> SimpleSubst -> SimpleSubst
(|.|) Id th2 = th2
(|.|) th1 Id = th1
(|.|) th1 th2 = th1:.:th2

infixl 8 |.|
infixl 7 :+->:

-- TODO make class Substitutable?

subst :: SimpleSubst -> SType -> SType
subst Id t = t
subst th@(tv :+->: ty) STyInt = STyInt
subst th@(tv :+->: ty) STyBool = STyBool
subst th@(tv :+->: ty) (STyFunc b t1 t2) = STyFunc b (subst th t1) (subst th t2)
subst th@(tv :+->: ty) (STyVar a) | tv == a   = ty
                                  | otherwise = STyVar a
subst th@(b1 :+>>: b2) STyInt = STyInt
subst th@(b1 :+>>: b2) STyBool = STyBool
subst th@(b1 :+>>: b2) (STyFunc b t1 t2) | b == b1   = STyFunc b2 (subst th t1) (subst th t2)
                                         | otherwise = STyFunc b (subst th t1) (subst th t2)
subst th@(b1 :+>>: b2) (STyVar a) = STyVar a
subst (th1:.:th2) t = subst th1 $ subst th2 t

substEnv :: SimpleSubst -> TEnv -> TEnv
substEnv th env = map modifyEnv env
  where modifyEnv (x, t) = (x, subst th t)

substC :: SimpleSubst -> ConstraintSet -> ConstraintSet
substC (th1:.:th2) _C = substC th1 $ substC th2 _C
substC (b1 :+>>: b2) _C = S.map modifyC _C
  where modifyC (b, pi) | b == b1   = (b2, pi)
                        | otherwise = (b, pi)
substC _ _C = _C

substAnn :: SimpleSubst -> AVar -> AVar
substAnn (th1:.:th2) b = substAnn th1 $ substAnn th2 b
substAnn (b1 :+>>: b2) b | b == b1   = b2
                         | otherwise = b
substAnn _ b = b

--------------------------------------------------------------------------------
-- Type unification

_U :: (SType, SType) -> SimpleSubst
_U (STyInt, STyInt) = Id
_U (STyBool, STyBool) = Id
_U (STyFunc b t1 t2, STyFunc b' t1' t2') = let th0 = b' :+>>: b
                                               th1 = _U (subst th0 t1, subst th0 t1')
                                               th2 = _U (subst th1 (subst th0 t2), subst th1 (subst th0 t2'))
                                           in  th2|.|th1|.|th0
_U (STyVar a, STyVar a') | a == a' = Id
_U (t, STyVar a) | a `doesNotOccurIn` t = a :+->: t
_U (STyVar a, t) | a `doesNotOccurIn` t = a :+->: t
_U (t1, t2) = error ("Could not unify types " ++ show t1 ++ " and " ++ show t2)

doesNotOccurIn :: TVar -> SType -> Bool
doesNotOccurIn a (STyVar tv) | a == tv = False
doesNotOccurIn a (STyFunc b t1 t2) = (a `doesNotOccurIn` t1) && (a `doesNotOccurIn` t2)
doesNotOccurIn a _ = True

--------------------------------------------------------------------------------
-- Type reconstruction

_W :: (TEnv, Exp) -> (SType, SimpleSubst, ConstraintSet)
_W (env, e) = (t, th, _C)
  where (t, th, _C, _) = _Wcc 0 (env, e)

-- cc: Call counter.
-- Each call to _Wcc gets a unique ID, used to generate fresh names.

_Wcc :: Int ->  (TEnv, Exp) -> (SType, SimpleSubst, ConstraintSet, Int)

_Wcc cc (env, Const c) = (constType c, Id, S.empty, cc+1)

_Wcc cc (env, Var x) = (_GammaOr env x (STyVar ('$':x)), Id, S.empty, cc+1)

_Wcc cc (env, Fn pi x e0) = let ax = STyVar $ '\'':(mkTVarName cc) ++ "_" ++ x
                                (t0, th0, _C0, cc0) = _Wcc cc ((x, ax):env, e0)
                                b0 = '\'':(mkAVarName cc)
                            in  ( (subst th0 ax) -|b0|> t0
                                , th0
                                , S.insert (b0, pi) _C0
                                , cc0+1 )

_Wcc cc (env, Fun pi f x e0) = let ax = STyVar $ '\'':(mkTVarName cc) ++ "_" ++ x
                                   a0 = STyVar $ '\'':(mkTVarName cc) ++ "_0"
                                   b0 = '\'':(mkAVarName cc)
                                   (t0, th0, _C0, cc0) = _Wcc cc ((x, ax):(f, ax -|b0|> a0):env, e0)
                                   th1 = _U (t0, subst th0 a0)
                               in  ( subst th1 (subst th0 ax) -|substAnn th1 (substAnn th0 b0)|> subst th1 t0
                                   , th1|.|th0
                                   , S.insert (substAnn th1 (substAnn th0 b0), pi) (substC th1 _C0)
                                   , cc0+1)


-- Helper functions:
constType :: Const -> SType
constType (CInt _) = STyInt
constType (CBool _) = STyBool

opType :: Op -> SType
opType x | x `elem` [Eq, Fun.LT, LTE, Fun.GT, GTE, Plus, Minus, Times, Div, Mod] = STyInt
         | x `elem` [And, Or] = STyBool
         | otherwise = error ("Unimplemented type for " ++ show x)
opType1 = opType
opType2 = opType

mkTVarName :: Int -> String  -- TODO make fancy
mkTVarName cc = "a" ++ (show cc)

mkAVarName :: Int -> String
mkAVarName cc = show cc
