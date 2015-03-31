module AcceptabilityRelation where

import Fun

import qualified Data.Set as S
import qualified Data.Map as M

type AbsVal   = S.Set Term
type AbsEnv   = M.Map Var AbsVal
type AbsCache = M.Map Lab AbsVal

(|=) :: (AbsCache, AbsEnv) -> Exp -> Bool
(|=) (_C, rho) e = undefined
