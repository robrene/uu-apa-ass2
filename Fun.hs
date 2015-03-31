module Fun (
    Const (..)
  , Var
  , Lab
  , Exp (..)
  , Term (..)
  , Op (..)
  )
where

import Data.Hashable

data Const = Bool Bool | Int Int
  deriving (Eq, Show)
type Var = String
type Lab = Integer

data Exp = Exp Term Lab
  deriving (Eq, Show)

data Term =
    Const Const
  | Var Var
  | Fn Var Exp       -- "regular" function
  | Fun Var Var Exp  -- recursive function
  | App Exp Exp
  | ITE Exp Exp Exp
  | Let Var Exp Exp
  | Op Exp Op Exp
  deriving (Eq, Show)
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
  deriving (Eq, Show)

instance Hashable Const where
  hash = hash . show
  hashWithSalt s = hashWithSalt s . show

instance Hashable Exp where
  hash = hash . show
  hashWithSalt s = hashWithSalt s . show

instance Hashable Term where
  hash = hash . show
  hashWithSalt s = hashWithSalt s . show

instance Hashable Op where
  hash = hash . show
  hashWithSalt s = hashWithSalt s . show
