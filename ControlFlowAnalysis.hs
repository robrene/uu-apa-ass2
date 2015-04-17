module ControlFlowAnalysis where

import Fun
import Data.Char
import Data.List
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
  where (t, th, _C, _) = _WWW (0, 1) (env, e)

-- cc: Call counter.
-- Each call to _WWW gets a unique counter values, used to generate fresh names.

_WWW :: (Int, Int) ->  (TEnv, Exp) -> (SType, SimpleSubst, ConstraintSet, (Int, Int))

_WWW (ca,cb) (env, Const c) = (constType c, Id, S.empty, (ca,cb))

_WWW (ca,cb) (env, Var x) = (_GammaOr env x (STyVar ('$':x)), Id, S.empty, (ca,cb))

_WWW (ca,cb) (env, Fn pi x e0) =
  let ax = freshTVar ca
      (t0, th0, _C0, (ca0,cb0)) = _WWW (ca+1, cb) ((x, ax):env, e0)
      b0 = freshAVar cb0
  in  ( (subst th0 ax) -|b0|> t0
      , th0
      , S.insert (b0, pi) _C0
      , (ca0,cb0+1) )

_WWW (ca,cb) (env, Fun pi f x e0) =
  let ax = freshTVar ca
      a0 = freshTVar (ca+1)
      b0 = freshAVar cb
      (t0, th0, _C0, (ca0,cb0)) = _WWW (ca+2,cb+1) ((x, ax):(f, ax -|b0|> a0):env, e0)
      th1 = _U (t0, subst th0 a0)
  in  ( subst th1 (subst th0 ax) -|substAnn th1 (substAnn th0 b0)|> subst th1 t0
      , th1|.|th0
      , S.insert (substAnn th1 (substAnn th0 b0), pi) (substC th1 _C0)
      , (ca0,cb0) )

_WWW (ca,cb) (env, App e1 e2) =
  let (t1, th1, _C1, (ca1,cb1)) = _WWW (ca,cb) (env, e1)
      (t2, th2, _C2, (ca2,cb2)) = _WWW (ca1,cb1) (substEnv th1 env, e2)
      a = freshTVar ca2
      b = freshAVar cb2
      th3 = _U (subst th2 t1, t2 -|b|> a)
  in  ( subst th3 a
      , th3|.|th2|.|th1
      , S.union (substC th3 (substC th2 _C1)) (substC th3 _C2)
      , (ca2+1,cb2+1) )

_WWW (ca,cb) (env, ITE e0 e1 e2) =
  let (t0, th0, _C0, (ca0,cb0)) = _WWW (ca,cb) (env, e0)
      (t1, th1, _C1, (ca1,cb1)) = _WWW (ca0,cb0) (substEnv th0 env, e1)
      (t2, th2, _C2, (ca2,cb2)) = _WWW (ca1,cb1) (substEnv th1 (substEnv th2 env), e2)
      th3 = _U (subst th2 (subst th1 t0), STyBool)
      th4 = _U (subst th3 t2, subst th3 (subst th2 t1))
  in  ( subst th4 (subst th3 t2)
      , th4|.|th3|.|th2|.|th1|.|th0
      , S.unions [ substC th4 (substC th3 (substC th2 (substC th1 _C0)))
                 , substC th4 (substC th3 (substC th2 _C1))
                 , substC th4 (substC th3 _C2)]
      , (ca2,cb2) )

_WWW (ca,cb) (env, Let x e1 e2) =
  let (t1, th1, _C1, (ca1,cb1)) = _WWW (ca,cb) (env, e1)
      (t2, th2, _C2, (ca2,cb2)) = _WWW (ca1,cb1) ((x, t1):(substEnv th1 env), e2)
  in  ( t2
      , th2|.|th1
      , S.union (substC th2 _C1) _C2
      , (ca2,cb2) )

_WWW (ca,cb) (env, Op e1 op e2) =
  let (t1, th1, _C1, (ca1,cb1)) = _WWW (ca,cb) (env, e1)
      (t2, th2, _C2, (ca2,cb2)) = _WWW (ca1,cb1) (substEnv th1 env, e2)
      th3 = _U (subst th2 t1, opType1 op)
      th4 = _U (subst th3 t2, opType2 op)
  in  ( opType op
      , th4|.|th3|.|th2|.|th1
      , S.union (substC th4 (substC th3 (substC th2 _C1))) (substC th4 (substC th3 _C2))
      , (ca2,cb2) )

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

freshTVar :: Int -> SType  -- TODO make fancy
freshTVar cc | cc < 26   = STyVar $ '\'':[chr $ cc + ord 'a']
             | otherwise = STyVar $ '\'':("a" ++ show (cc-26))

freshAVar :: Int -> AVar
freshAVar cc = '\'':(show cc)

-- Pretty print
ppSType :: SType -> String
ppSType STyInt = "int"
ppSType STyBool = "bool"
ppSType (STyFunc b t1 t2) = "(" ++ (ppSType t1) ++ " --|" ++ b ++ "|->" ++ (ppSType t2) ++ ")"
ppSType (STyVar a) = a

ppSimpleSubst :: SimpleSubst -> String
ppSimpleSubst Id = "id"
ppSimpleSubst (tv :+->: ty) = "[" ++ tv ++ " +-> " ++ (ppSType ty) ++ "]"
ppSimpleSubst (b1 :+>>: b2) = "[" ++ b1 ++ " +>> " ++ b2 ++ "]"
ppSimpleSubst (a :.: b) = (ppSimpleSubst a) ++ " ∘\n" ++ (ppSimpleSubst b)

ppConstraints :: ConstraintSet -> String
ppConstraints _C = intercalate ", " $ S.toList $ S.map mkString _C
  where mkString (b, pi) = b ++ " ⊇ {" ++ pi ++ "}"

ppW :: (SType, SimpleSubst, ConstraintSet) -> String
ppW (ty, th, _C) = (ppSType ty) ++ "\n" ++ (ppSimpleSubst th) ++ "\n" ++ (ppConstraints _C)
