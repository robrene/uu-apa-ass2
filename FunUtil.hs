module FunUtil (
    fvExp
  , fvTerm
  )
where

import Fun
import qualified Data.Set as S

fvExp :: Exp -> S.Set Var
fvExp (Exp t l) = fvTerm t

fvTerm :: Term -> S.Set Var
fvTerm (Const c)      = S.empty
fvTerm (Var x)        = S.singleton x
fvTerm (Fn x e)       = S.delete x $ fvExp e
fvTerm (Fun f x e)    = S.delete f $ S.delete x $ fvExp e
fvTerm (App e1 e2)    = S.union (fvExp e1) (fvExp e2)
fvTerm (ITE e0 e1 e2) = S.unions [fvExp e0, fvExp e1, fvExp e2]
fvTerm (Let x e1 e2)  = S.union (fvExp e1) (S.delete x $ fvExp e2)
fvTerm (Op e1 op e2)  = S.union (fvExp e1) (fvExp e2)
