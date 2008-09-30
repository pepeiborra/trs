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
      Match(..), Matchable, match, matchFdefault,
      rewrite1, rewrite1', rewrites, rewrites', reduce
    ) where

import Control.Applicative
import Control.Monad (mzero, mplus, MonadPlus)
import Control.Monad.State (MonadState)
import Data.Foldable
import Data.Traversable
import Prelude hiding (mapM, concat)
import TypePrelude

import TRS.Term
import TRS.Types hiding (match)
import TRS.Rules
import TRS.Substitutions
import TRS.Unification
import TRS.Utils hiding (someSubterm)

-----------------------------
-- * Matching
-----------------------------

class (Var :<: f, Traversable f, Match f f f) => Matchable f
instance (Var :<: f, Traversable f, Match f f f) => Matchable f

class Match f h g where matchF :: Match g g g => f(Term g) -> h(Term g) -> Maybe (Subst g)
--instance (Functor a, Functor b, Functor g) => Match a b g where matchF _ _ = Nothing

class Match2 isVarF f h g where matchF' :: Match g g g => isVarF -> f(Term g) -> h(Term g) -> Maybe (Subst g)
instance (Var :<: g, f :<: g) => Match2 HTrue Var f g where matchF' _ (Var _ i) t = Just $ mkSubst [(i, inject t)]
instance (Var :<: g, MatchShape f g) => Match2 HFalse f f g where matchF' _ = matchFdefault
instance Match2 HFalse f g h where matchF' _ _x _y = Nothing

instance (Var :<: g) => Match Var Var g where matchF (Var _ i) vj@Var{} = Just$ mkSubst [(i, inject vj)]
instance forall isVar f h g . (TypeEq2 f Var isVar, Match2 isVar f h g) => Match f h g where matchF x y = matchF' (proxy::isVar) x y

instance ( Match c a g, Match d a g) => Match (c :+: d) a g where
    matchF (Inl x) y = matchF x y
    matchF (Inr x) y = matchF x y

instance (Match a c g, Match a d g) => Match a (c :+: d) g where
    matchF x (Inl y) = matchF x y
    matchF x (Inr y) = matchF x y

instance ( Match a c g, Match b c g, Match a d g, Match b d g, (a :+: b) :<: g) =>
        Match (a :+: b) (c :+: d) g where
    matchF (Inl x) (Inl y) = matchF x y
    matchF (Inr x) (Inr y) = matchF x y
    matchF (Inl x) (Inr y) = matchF x y
    matchF (Inr x) (Inl y) = matchF x y

instance (Eq id, T id :<: g, Var :<: g) => Match (T id) (T id) g where matchF = matchFdefault

matchFdefault :: (Var :<: g, Match g g g, MatchShape f g) => f (Term g) -> f (Term g) -> Maybe (Subst g)
matchFdefault t1 t2 = concatSubst <$> (mapM (uncurry match) =<< matchShapeF t1 t2)

match :: (Match t t t) => Term t -> Term t -> Maybe (Subst t)
match (In t) (In u) = matchF t u


----------------------------------------
-- * Rewriting
----------------------------------------
rewrite1 :: (Matchable f, MonadPlus m) =>
            [Rule f] -> Term f -> m (Term f)
rewrite1 rr t = evalU $ rewrite1' rr t
rewrites :: (MonadPlus m, Matchable f) =>
            [Rule f] -> Term f -> m (Term f)
rewrites rr t = evalU $ rewrites' rr t

rewrite1' :: ( Matchable f, MonadPlus m, Functor m, MonadState (Subst f) m) => [Rule f] -> Term f -> m (Term f)
rewrite1' rr t = rewriteTop t `mplus` someSubterm (rewrite1' rr) t
    where -- rewriteTop :: (MonadPlus m, MonadState (Subst f) m) => Term f -> m (Term f)
          rewriteTop t = Data.Foldable.msum $ flip map rr $ \r -> do
                          lhs:->rhs <- variant r t
                          case match lhs t of
                               Just subst -> return$ applySubst subst rhs
                               Nothing    -> mzero

rewrites' :: (Matchable f, MonadState (Subst f) m, MonadPlus m,  Functor m) => [Rule f] -> Term f -> m (Term f)
rewrites' rr = closureMP (rewrite1' rr)

reduce :: (Matchable f, MonadPlus1 m) => [Rule f] -> Term f -> m (Term f)
reduce rr   = fixMP (rewrite1 rr)

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

m1 = match t t1
m1' = match t1 t

m2 :: Maybe (Subst (Var :+: T String))
m2 = match x y

m3 = match x (constant "1") :: Maybe (Subst (Var :+: T String))
-}