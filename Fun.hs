module Fun (
    Exp (..)
  , Const (..)
  , Var
  , Pnt
  , Op (..)
  , ppExp
  )
where

data Exp =
    Const Const
  | Var Var
  | Fn Pnt Var Exp
  | Fun Pnt Var Var Exp
  | App Exp Exp
  | ITE Exp Exp Exp
  | Let Var Exp Exp
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

ppExp :: Exp -> String
ppExp (Const c) = ppConst c
ppExp (Var x) = x
ppExp (Fn pi x e0) = "(fn_" ++ pi ++ " " ++ x ++ " => " ++ ppExp e0 ++ ")"
ppExp (Fun pi f x e0) = "(fun_" ++ pi ++ " " ++ f ++ " " ++ x ++ " => " ++ ppExp e0 ++ ")"
ppExp (App e1 e2) = ppExp e1 ++ " " ++ ppExp e2
ppExp (ITE e0 e1 e2) = "(if " ++ ppExp e0 ++ " then " ++ ppExp e1 ++ " else " ++ ppExp e2 ++ ")"
ppExp (Let x e1 e2) = "(let " ++ x ++ " = " ++ ppExp e1 ++ " in " ++ ppExp e2 ++ ")"
ppExp (Op e1 op e2) = "(" ++ ppExp e1 ++ " " ++ ppOp op ++ " " ++ ppExp e2 ++ ")"

ppConst :: Const -> String
ppConst (CInt i) = show i
ppConst (CBool b) = show b

ppOp :: Op -> String
ppOp Eq = "=="
ppOp Fun.LT = "<"
ppOp LTE = "<="
ppOp Fun.GT = ">"
ppOp GTE = ">="
ppOp Plus = "+"
ppOp Minus = "-"
ppOp Times = "*"
ppOp Div = "/"
ppOp Mod = "%"
ppOp And = "&&"
ppOp Or = "||"
