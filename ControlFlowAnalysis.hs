module ControlFlowAnalysis where

import Fun
import qualified Data.Set as S

--------------------------------------------------------------------------------
-- Annotated types:

data SType = STyInt | STyBool | STyFunc AVar SType SType | STyVar TVar deriving (Show)
type TVar = String
type AVar = Int
data SAnn = SAPnt Pnt | SAnn :++: SAnn | SAEmpty | SAVar AVar deriving (Show)

type TEnv = [(Var, SType)]

_Gamma ((x', t):es) x = if x == x' then t else _Gamma es x
_Gamma [] x = error ("Type not found: " ++ show x)

_GammaOr ((x', t):es) x y = if x == x' then t else _GammaOr es x y
_GammaOr [] x y = y

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

type ConstraintSet = S.Set (AVar, Pnt)

_W :: (TEnv, Exp) -> (SType, SimpleSubst, ConstraintSet)
_W = undefined
