module Fun (
    Exp (..)
  , Const (..)
  , Var
  , Pnt
  , Op (..)
  )
where

data Exp =
    Const Const
  | Var Var
  | Fn Pnt Var Exp
  | Fun Pnt Var Var Exp
  | App Exp Exp
  | ITE Exp Exp Exp
  | Let Var Exp
  | Op Exp Op Exp
  deriving (Eq, Show)

data Const = CInt Int | CBool Bool deriving (Eq, Show)
type Var = String
type Pnt = String

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
