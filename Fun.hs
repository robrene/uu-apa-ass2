module Fun (
    Const (..)
  , Var
  , Lab
  , Exp (..)
  , Term (..)
  , Op (..)
  )
where

data Const = Bool Bool | Int Int
type Var = String
type Lab = Integer

data Exp = Exp Term Lab

data Term =
    Const Const
  | Var Var
  | Fn Var Exp       -- "regular" function
  | Fun Var Var Exp  -- recursive function
  | App Exp Exp
  | ITE Exp Exp Exp
  | Let Var Exp Exp
  | Op Exp Op Exp
  -- TODO: Add Terms for data structures (lists, pairs, general data types)
  -- TODO: Add Term for case statement

data Op =
    Eq
  | LT
  | LTE
  | GT
  | GTE
  | Plus
  | Minus
  | Times
  | Div
  | Mod
  | And
  | Or
