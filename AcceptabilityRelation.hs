module AcceptabilityRelation where

import Fun

import Data.Hashable
import qualified Data.HashSet as S
import qualified Data.Map as M
import Data.Maybe

-- ref. Nielson Nielson Hankin PoPA p.144
type AbsVal   = S.HashSet Term
type AbsEnv   = M.Map Var AbsVal
type AbsCache = M.Map Lab AbsVal

-- ref. Nielson Nielson Hankin PoPA p.146
-- TODO: Extend for custom Terms.
(|=) :: (AbsCache, AbsEnv) -> Exp -> Bool
(|=) ec@(_C, rho) (Exp t l) = acceptTerm t
  where
    -- [con]:
    acceptTerm (Const c) = True
    -- [var]:
    acceptTerm (Var x) = lookupSet rho x `isSubsetOf` lookupSet _C l
    -- [fn]:
    acceptTerm fn@(Fn x e0) = S.singleton fn `isSubsetOf` lookupSet _C l
    -- [fun]:
    acceptTerm fun@(Fun f x e0) = S.singleton fun `isSubsetOf` lookupSet _C l
    -- [app]:
    acceptTerm (App e1@(Exp t1 l1) e2@(Exp t2 l2)) =
        undefined -- TODO: implement
    -- [if]:
    acceptTerm (ITE e0 e1@(Exp t1 l1) e2@(Exp t2 l2)) =
        (ec |= e0) && (ec |= e1) && (ec |= e2) &&
        lookupSet _C l1 `isSubsetOf` lookupSet _C l &&
        lookupSet _C l2 `isSubsetOf` lookupSet _C l
    -- [let]:
    acceptTerm (Let x e1@(Exp t1 l1) e2@(Exp t2 l2)) =
        (ec |= e1) && (ec |= e2) &&
        lookupSet _C l1 `isSubsetOf` lookupSet rho x &&
        lookupSet _C l2 `isSubsetOf` lookupSet rho x
    -- [op]:
    acceptTerm (Op e1 op e2) = (ec |= e1) && (ec |= e2)

lookupSet :: (Ord k) => M.Map k (S.HashSet v) -> k -> S.HashSet v
lookupSet m k = M.findWithDefault S.empty k m

isSubsetOf :: (Eq a, Hashable a) => S.HashSet a -> S.HashSet a -> Bool
isSubsetOf a b = S.size a == S.size elems
  where elems = S.filter (\x -> S.member x b) a
