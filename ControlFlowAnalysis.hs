{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module ControlFlowAnalysis where

import Fun
import Data.Char
import Data.List
import qualified Data.Set as S

--------------------------------------------------------------------------------
-- Annotated types:

data SType =
    STyInt
  | STyBool
  | STyPair AVar SType SType
  | STyList AVar SType
  | STyDataType AVar Tag
  | STyFunc AVar SType SType
  | STyVar TVar
  deriving (Show)
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

class Substitutable a where
  sub :: SimpleSubst -> a -> a

instance Substitutable SType where
  sub (tv :+->: ty) (STyVar a) | tv == a = ty
  sub th (STyPair b t1 t2) = STyPair (sub th b) (sub th t1) (sub th t2)
  sub th (STyList b t1) = STyList (sub th b) (sub th t1)
  sub th (STyDataType b z) = STyDataType (sub th b) z
  sub th (STyFunc b t1 t2) = STyFunc (sub th b) (sub th t1) (sub th t2)
  sub (th1:.:th2) t = sub th1 $ sub th2 t
  sub _ t = t

instance Substitutable AVar where
  sub (b1 :+>>: b2) b | b == b1 = b2
  sub (th1:.:th2) b = sub th1 $ sub th2 b
  sub _ b = b

instance Substitutable TEnv where
  sub th env = map modifyEnv env
    where modifyEnv (x, t) = (x, sub th t)

instance Substitutable ConstraintSet where
  sub th _C = S.map modifyC _C
    where modifyC (b, pi) = (sub th b, pi)

--------------------------------------------------------------------------------
-- Type unification

_U :: (SType, SType) -> SimpleSubst
_U (STyInt, STyInt) = Id
_U (STyBool, STyBool) = Id
_U (STyPair b t1 t2, STyPair b' t1' t2') = let th0 = b' :+>>: b
                                               th1 = _U (sub th0 t1, sub th0 t1')
                                               th2 = _U (sub th1 (sub th0 t2), sub th1 (sub th0 t2'))
                                           in  th2|.|th1|.|th0
_U (STyList b t, STyList b' t') = let th0 = b' :+>>: b
                                      th1 = _U (sub th0 t, sub th0 t')
                                  in  th1|.|th0
_U (STyDataType b z, STyDataType b' z') | z == z' = b' :+>>: b
_U (STyFunc b t1 t2, STyFunc b' t1' t2') = let th0 = b' :+>>: b
                                               th1 = _U (sub th0 t1, sub th0 t1')
                                               th2 = _U (sub th1 (sub th0 t2), sub th1 (sub th0 t2'))
                                           in  th2|.|th1|.|th0
_U (STyVar a, STyVar a') | a == a' = Id
_U (t, STyVar a) | a `doesNotOccurIn` t = a :+->: t
_U (STyVar a, t) | a `doesNotOccurIn` t = a :+->: t
_U (t1, t2) = error ("Could not unify types " ++ ppSType t1 ++ " and " ++ ppSType t2)

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

_WWW (ca,cb) (env, Var x) = (_GammaOr env x (STyVar ("''"++x)), Id, S.empty, (ca,cb))

_WWW (ca,cb) (env, Fn pi x e0) =
  let ax = freshTVar ca
      (t0, th0, _C0, (ca0,cb0)) = _WWW (ca+1, cb) ((x, ax):env, e0)
      b0 = freshAVar cb0
  in  ( (sub th0 ax) -|b0|> t0
      , th0
      , S.insert (b0, pi) _C0
      , (ca0,cb0+1) )

_WWW (ca,cb) (env, Fun pi f x e0) =
  let ax = freshTVar ca
      a0 = freshTVar (ca+1)
      b0 = freshAVar cb
      (t0, th0, _C0, (ca0,cb0)) = _WWW (ca+2,cb+1) ((x, ax):(f, ax -|b0|> a0):env, e0)
      th1 = _U (t0, sub th0 a0)
  in  ( sub th1 (sub th0 ax) -|sub th1 (sub th0 b0)|> sub th1 t0
      , th1|.|th0
      , S.insert (sub th1 (sub th0 b0), pi) (sub th1 _C0)
      , (ca0,cb0) )

_WWW (ca,cb) (env, App e1 e2) =
  let (t1, th1, _C1, (ca1,cb1)) = _WWW (ca,cb) (env, e1)
      (t2, th2, _C2, (ca2,cb2)) = _WWW (ca1,cb1) (sub th1 env, e2)
      a = freshTVar ca2
      b = freshAVar cb2
      th3 = _U (sub th2 t1, t2 -|b|> a)
  in  ( sub th3 a
      , th3|.|th2|.|th1
      , S.union (sub th3 (sub th2 _C1)) (sub th3 _C2)
      , (ca2+1,cb2+1) )

_WWW (ca,cb) (env, ITE e0 e1 e2) =
  let (t0, th0, _C0, (ca0,cb0)) = _WWW (ca,cb) (env, e0)
      (t1, th1, _C1, (ca1,cb1)) = _WWW (ca0,cb0) (sub th0 env, e1)
      (t2, th2, _C2, (ca2,cb2)) = _WWW (ca1,cb1) (sub th1 (sub th2 env), e2)
      th3 = _U (sub th2 (sub th1 t0), STyBool)
      th4 = _U (sub th3 t2, sub th3 (sub th2 t1))
  in  ( sub th4 (sub th3 t2)
      , th4|.|th3|.|th2|.|th1|.|th0
      , S.unions [ sub th4 (sub th3 (sub th2 (sub th1 _C0)))
                 , sub th4 (sub th3 (sub th2 _C1))
                 , sub th4 (sub th3 _C2)]
      , (ca2,cb2) )

_WWW (ca,cb) (env, Let x e1 e2) =
  let (t1, th1, _C1, (ca1,cb1)) = _WWW (ca,cb) (env, e1)
      (t2, th2, _C2, (ca2,cb2)) = _WWW (ca1,cb1) ((x, t1):(sub th1 env), e2)
  in  ( t2
      , th2|.|th1
      , S.union (sub th2 _C1) _C2
      , (ca2,cb2) )

_WWW (ca,cb) (env, Op e1 op e2) =
  let (t1, th1, _C1, (ca1,cb1)) = _WWW (ca,cb) (env, e1)
      (t2, th2, _C2, (ca2,cb2)) = _WWW (ca1,cb1) (sub th1 env, e2)
      th3 = _U (sub th2 t1, opType1 op)
      th4 = _U (sub th3 t2, opType2 op)
  in  ( opType op
      , th4|.|th3|.|th2|.|th1
      , S.union (sub th4 (sub th3 (sub th2 _C1))) (sub th4 (sub th3 _C2))
      , (ca2,cb2) )

_WWW (ca,cb) (env, Pair pi e1 e2) =
  let (t1, th1, _C1, (ca1,cb1)) = _WWW (ca,cb) (env, e1)
      (t2, th2, _C2, (ca2,cb2)) = _WWW (ca1,cb1) (sub th1 env, e2)
      b = freshAVar cb2
  in  ( STyPair b (sub th2 (sub th1 t1)) (sub th2 t2)
      , th2|.|th1
      , S.insert (sub th2 (sub th1 b), pi) $ S.union (sub th2 _C1) _C2
      , (ca2,cb2+1) )

_WWW (ca,cb) (env, ListCons pi e1 e2) =
  let (t1, th1, _C1, (ca1,cb1)) = _WWW (ca,cb) (env, e1)
      (t2, th2, _C2, (ca2,cb2)) = _WWW (ca1,cb1) (sub th1 env, e2)
      b = freshAVar cb2
      th3 = _U (sub th2 (STyList b t1), t2)
  in  ( sub th3 t2
      , th3|.|th2|.|th1
      , S.insert (sub th3 (sub th2 (sub th1 b)), pi) $ S.union (sub th3 (sub th2 _C1)) (sub th3 _C2)
      , (ca2,cb2+1) )

_WWW (ca,cb) (env, ListNil pi) =
  let a = freshTVar ca
      b = freshAVar cb
  in  ( STyList b a
      , Id
      , S.singleton (b, pi)
      , (ca+1,cb+1) )

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
ppSType (STyPair b t1 t2) = "(" ++ (ppSType t1) ++ " ⊗_{" ++ b ++ "} " ++ (ppSType t2) ++ ")"
ppSType (STyList b t1) = "ℒ_{" ++ b ++ "}(" ++ ppSType t1 ++ ")"
ppSType (STyDataType b z) = "\"" ++ z ++ "\"_{" ++ b ++ "}"
ppSType (STyFunc b t1 t2) = "(" ++ (ppSType t1) ++ " --|" ++ b ++ "|-> " ++ (ppSType t2) ++ ")"
ppSType (STyVar a) = a

ppSimpleSubst :: SimpleSubst -> String
ppSimpleSubst Id = "id"
ppSimpleSubst (tv :+->: ty) = "[" ++ tv ++ " +-> " ++ (ppSType ty) ++ "]"
ppSimpleSubst (b1 :+>>: b2) = "[" ++ b1 ++ " +>> " ++ b2 ++ "]"
ppSimpleSubst (a :.: b) = (ppSimpleSubst a) ++ "\n∘ " ++ (ppSimpleSubst b)

ppConstraints :: ConstraintSet -> String
ppConstraints _C = intercalate ", " $ S.toList $ S.map mkString _C
  where mkString (b, pi) = b ++ " ⊇ {" ++ pi ++ "}"
