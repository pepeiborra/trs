{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE PolymorphicComponents #-}
{-# OPTIONS_GHC -fglasgow-exts #-}

module TRS.Rewriting (
      Rewritable, Match(..), Match2(..), Matchable, match, matchFdefault,
      rewrite1,  reduce,  rewrites,
      rewrite1S, reduceS, rewritesS
    ) where

import Control.Applicative
import Control.Monad (mzero, mplus, MonadPlus)
import Control.Monad.State (MonadState)
import Data.Foldable
import Data.List ((\\))
import Data.Traversable
import Prelude hiding (mapM, concat)
import TypePrelude

import TRS.Term
import TRS.Types hiding (match)
import TRS.Rules
import TRS.Substitutions
import TRS.UMonad
import TRS.Utils hiding (someSubterm)

-----------------------------
-- * Matching
-----------------------------
class (Basic :<: g, Traversable g, Var :<: g, Match g g g g) => MatchableSimple g
instance (Basic :<: g, Traversable g, Var :<: g, Match g g g g) => MatchableSimple g

class    (Var :<: f, Var :<: g, Traversable f, Traversable g, Match f g f g) => Matchable f g
instance (Var :<: f, Var :<: g, Traversable f, Traversable g, Match f g f g) => Matchable f g

class    (Var :<: rf, Traversable rf, rf :<: f, Matchable f f) => Rewritable rf f
instance (Var :<: rf, Traversable rf, rf :<: f, Matchable f f) => Rewritable rf f

class (fs :<: gs, f :<: fs, g :<: gs) => Match f g fs gs where matchF :: Matchable fs gs => f(Term fs) -> g(Term gs) -> Maybe (Subst gs)

instance (f :<: g, (c :+: d) :<: f, Match c a f g, Match d a f g) => Match (c :+: d) a f g where
    matchF (Inl x) y = matchF x y
    matchF (Inr x) y = matchF x y

instance (fs :<: gs, (c :+: d) :<: gs, Match a c fs gs, Match a d fs gs) => Match a (c :+: d) fs gs where
    matchF x (Inl y) = matchF x y
    matchF x (Inr y) = matchF x y

instance (fs :<: gs, Match a c fs gs, Match b c fs gs, Match a d fs gs, Match b d fs gs, (a :+: b) :<: fs, (c :+: d) :<: gs) =>
        Match (a :+: b) (c :+: d) fs gs where
    matchF (Inl x) (Inl y) = matchF x y
    matchF (Inr x) (Inr y) = matchF x y
    matchF (Inl x) (Inr y) = matchF x y
    matchF (Inr x) (Inl y) = matchF x y


class (fs :<: gs, f :<: fs, g :<: gs) => Match2 isVarF f g fs gs where matchF' :: {- Match g g g g => -} Matchable fs gs => isVarF -> f(Term fs) -> g(Term gs) -> Maybe (Subst gs)
instance (Var :<: fs, Var :<: gs, g :<: gs, fs :<: gs) =>
                                            Match2 HTrue Var g fs gs where matchF' _ (Var _ i) t = Just $ mkSubst [(i, inject t)]
instance (Var :<: gs, fs :<: gs, MatchShape f f fs gs, Eq (Term gs)) =>
                                            Match2 HFalse f f fs gs where matchF' _ = matchFdefault
instance (fs :<: gs, f :<: fs, g :<: gs) => Match2 HFalse f g fs gs where matchF' _ _x _y = Nothing

instance (fs :<: gs, Var :<: gs, Var :<: fs) => Match Var Var fs gs where matchF (Var _ i) vj@Var{} = Just$ mkSubst [(i, inject vj)]
instance forall isVar f g fs gs. (TypeEq2 f Var isVar, Match2 isVar f g fs gs) => Match f g fs gs where matchF x y = matchF' (proxy::isVar) x y


matchFdefault :: (Var :<: gs, Matchable fs gs, MatchShape f f fs gs, Eq (Term gs)) => f (Term fs) -> f (Term gs) -> Maybe (Subst gs)
matchFdefault t1 t2 = mergeSubsts =<< (mapM (uncurry match') =<< matchShapeF t1 t2)

match' :: (Matchable f g) => Term f -> Term g -> Maybe (Subst g)
match' (In t) (In u) = {-# SCC "match'" #-} matchF t u

match :: (Matchable f f) => Term f -> Term f -> Maybe (Subst f)
match t u = {-# SCC "match" #-} match' t u

----------------------------------------
-- * Rewriting
----------------------------------------

{-# INLINE rewrite1 #-}
rewrite1 :: (Rewritable rf f, MonadPlus m) => [Rule rf] -> Term f -> m(Term f)
rewrite1 rr t = {-# SCC "rewrite1" #-} evalR ([0..] \\ map varId' (vars t)) $ rewriteStep rr t


-- | Reflexive, Transitive closure
rewrites :: (Rewritable f g, MonadPlus m) => [Rule f] -> Term g -> m (Term g)
rewrites rr t = {-# SCC "rewrites" #-} evalR ([0..] \\ map varId' (vars t)) $ closureMP (rewriteStep rr) t

{-# INLINE rewriteStep #-}
--rewriteStep :: (Matchable f g, Foldable f, MonadFresh m, MonadPlus m) => [Rule f] -> Term g -> m (Term g)
rewriteStep rr t = {-# SCC "rewriteStep" #-} rewriteTop t `mplus` someSubterm (rewriteStep rr) t
    where rewriteTop t = Data.Foldable.msum $ forEach rr $ \r -> do
                          lhs:->rhs <- {-# SCC  "rewriteStep/variant" #-} variant r t
                          case {-# SCC  "rewriteStep/match" #-} match lhs t of
                               Just subst -> return (rhs // subst)
                               Nothing    -> mzero

-- | Reflexive, Transitive closure
rewrites' :: (Rewritable f g, MonadFresh m, MonadPlus m) => [Rule f] -> Term g -> m (Term g)
rewrites' rr = closureMP (rewrite1' rr)

-- | Normal forms
reduce :: (Rewritable f g, MonadPlus1 m) => [Rule f] -> Term g -> m (Term g)
reduce rr   = fixMP (rewrite1 rr)

rewrite1S :: (MatchableSimple f, MonadPlus m) => [Rule Basic] -> Term f -> m (Term f)
rewrite1S = rewrite1
rewritesS :: (MatchableSimple g, MonadPlus m) => [Rule Basic] -> Term g -> m(Term g)
rewritesS = rewrites
reduceS :: (MatchableSimple f, MonadPlus1 m) => [Rule Basic] -> Term f -> m (Term f)
reduceS = reduce

---------------------------------------
-- * Examples
---------------------------------------
{-
x,y :: (Var :<: f) => Term f
x = var 0
y = var 1

(+:) :: (T String :<: f) => Term f -> Term f -> Term f
(+:) = term2 "+"

t :: Term (Var :+: T String)
t = x +: y

t1 :: (T String :<: f) => Term f
t1 = constant "1" +: constant "0"

m1  = match t t1
m1' = match t1 t

m2 :: Maybe (Subst (Var :+: T String))
m2 = match x y

m3 = match x (constant "1") :: Maybe (Subst (Var :+: T String))
-}