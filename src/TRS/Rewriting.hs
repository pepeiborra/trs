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
      Rewritable, Match(..), MatchL(..), Matchable, match, matchFdefault,
      rewrite1,  reduce,  rewrites,
--      rewrite1S, reduceS, rewritesS,
      (=.=), EqModulo_(..), EqModulo, equal, equalG,
      isNF
    ) where

import Control.Monad (mzero, mplus, MonadPlus, foldM)
import Control.Monad.Logic.Class
import Data.Foldable
import Data.List ((\\))
import Data.Maybe (isJust)
import Data.Monoid
import Data.Traversable
import Prelude hiding (mapM, concat, zipWith)
import TypePrelude

import TRS.Term
import TRS.Types hiding (match, size)
import TRS.Rules
import TRS.Substitutions
import TRS.UMonad
import TRS.MonadFresh
import TRS.Utils hiding (someSubterm)

isNF :: (Rewritable rf f) => [Rule rf] -> Term f -> Bool
isNF = (null.) . rewrite1

-----------------------------
-- * Matching
-----------------------------
class    (Var :<: f, Var :<: g, IsVar g, HashConsed g, Traversable f, Traversable g, MatchL f g) => Matchable f g
instance (Var :<: f, Var :<: g, IsVar g, HashConsed g, Traversable f, Traversable g, MatchL f g) => Matchable f g

class    (IsVar f, HashConsed rf, IsVar rf, Var :<: rf, Traversable rf, rf :<: f, Matchable f f) => Rewritable rf f
instance (IsVar f, HashConsed rf, IsVar rf, Var :<: rf, Traversable rf, rf :<: f, Matchable f f) => Rewritable rf f

class     MatchL f g where matchL :: (Matchable fs g) => f(Term fs) -> g(Term g) -> Maybe (Subst g)
instance (MatchL c a, MatchL d a) => MatchL (c :+: d) a where
    matchL (Inl x) y = matchL x y
    matchL (Inr x) y = matchL x y
instance IsVar g    => MatchL Var g where matchL (Var _ i) t = Just $ mkSubst [(i, In t)]
instance MatchR f g => MatchL f   g where matchL = matchR

class    MatchR f g where matchR :: (Matchable fs gs) => f (Term fs) -> g (Term gs) -> Maybe (Subst gs)
instance (MatchR a c, MatchR a d) => MatchR a (c :+: d) where
    matchR x (Inl y) = matchR x y
    matchR x (Inr y) = matchR x y
instance Match f g => MatchR f g where matchR = matchF

class    Match f g     where matchF :: (Matchable fs gs) => f (Term fs) -> g (Term gs) -> Maybe (Subst gs)
instance MatchShape f => Match f f where matchF = matchFdefault
instance Match f g     where matchF _ _ = Nothing


matchFdefault :: (Matchable fs gs, MatchShape f) => f (Term fs) -> f (Term gs) -> Maybe (Subst gs)
--matchFdefault t1 t2 = mergeSubsts =<< (mapM (uncurry match') =<< matchShapeF t1 t2)
matchFdefault s t = matchShapeF s t >>= foldM matchOne mempty
  where matchOne subst (s,t) = do
          subst' <- match' s (applySubst subst t)
          return (unionSubst subst subst')

match' :: (Matchable f g) => Term f -> Term g -> Maybe (Subst g)
match' (In t) (In u) = {-# SCC "match'" #-} matchL t u

match :: (Matchable f f) => Term f -> Term f -> Maybe (Subst f)
match t u = {-# SCC "match" #-} match' t u

----------------------------------------
-- * Rewriting
----------------------------------------

{-# INLINE rewrite1 #-}
rewrite1 :: (Rewritable rf f, MonadPlus m) => [Rule rf] -> Term f -> m(Term f)
rewrite1 rr t = {-# SCC "rewrite1" #-} evalR ([0..] \\ map varId (vars t)) $ rewriteStep rr t


-- | Reflexive, Transitive closure
rewrites :: (Rewritable f g, MonadPlus m) => [Rule f] -> Term g -> m (Term g)
rewrites rr t = {-# SCC "rewrites" #-} evalR ([0..] \\ map varId (vars t)) $ closureMP (rewriteStep rr) t

{-# INLINE rewriteStep #-}
rewriteStep :: forall f g m. (Rewritable f g, Foldable f, MonadFresh m, MonadPlus m) => [Rule f] -> Term g -> m (Term g)
rewriteStep rr t = {-# SCC "rewriteStep" #-} do
   rr' <- mapM variant rr
   let rewriteTop :: HashConsed g => Term g -> m(Term g)
       rewriteTop t = Data.Foldable.msum $ forEach rr' $ \r -> do
                          lhs:->rhs <- {-# SCC  "rewriteStep/variant" #-} return r
                          case {-# SCC  "rewriteStep/match" #-} match lhs t of
                               Just subst -> return (applySubst subst rhs)
                               Nothing    -> mzero
       go t = rewriteTop t `mplus` someSubterm go t
   go t

-- | Normal forms, starting from leftmost outermost
--   Assumes no extra variables in the rhs are present
reduce :: (Rewritable f g, MonadLogic m) => [Rule f] -> Term g -> m (Term g)
reduce rr t = evalR ([0..] \\ map varId (vars t)) $ fixMP (rewriteStep rr) t


{-
rewrite1S :: (MatchableSimple f, MonadLogic m) => [Rule Basic] -> Term f -> m (Term f)
rewrite1S = rewrite1
rewritesS :: (IsVar g, MatchableSimple g, MonadLogic m) => [Rule Basic] -> Term g -> m(Term g)
rewritesS = rewrites
reduceS :: (MatchableSimple f, MonadLogic m) => [Rule Basic] -> Term f -> m (Term f)
reduceS = reduce
-}

---------------------------------------
-- * Equivalence modulo renaming
---------------------------------------

(=.=) = equal

equal,(=.=) :: (Matchable f f, IsVar f) => Term f -> Term f -> Bool
equal t u | [t'] <- variant' [t] [u] = {-# SCC "equal" #-} isJust (match t' u >> match u t')

equalG :: (Eq (Term f), IsVar f, Matchable f f, Traversable t) => t(Term f) -> t(Term f) -> Bool
equalG t u | t' <- variant' t u = {-# SCC "equalG" #-}
                   size t == size u && isJust ((mergeSubsts . toList =<< zipWithM match t' u) >>
                                               (mergeSubsts . toList =<< zipWithM match u t'))


-- Equality modulo renaming on Terms
type EqModulo f = EqModulo_(Term f)

newtype EqModulo_ a = EqModulo {eqModulo :: a}

instance Functor EqModulo_ where fmap f (EqModulo x) = EqModulo (f x)
deriving instance (Eq (EqModulo_ a), Ord  a) => Ord (EqModulo_ a)
instance Show a => Show (EqModulo_ a) where showsPrec p (EqModulo x) = showsPrec p x

instance (Matchable f f, IsVar f) => Eq (EqModulo f) where EqModulo t1 == EqModulo t2 = t1 `equal` t2

--instance (Var :<: f, Unifyable f) => Eq (Term f) where (==) = equal

---------------------------------------
-- * Examples
---------------------------------------
{-
(+:) :: (T String :<: f, HashConsed f) => Term f -> Term f -> Term f
(+:) = term2 "+"

t :: Term (Var :+: T String)
t = x +: y

t1 :: (T String :<: f, HashConsed f) => Term f
t1 = constant "1" +: constant "0"

m1  = match t t1
m1' = match t1 t

m2 :: Maybe (Subst (Var :+: T String))
m2 = match x y

m3 = match x (constant "1") :: Maybe (Subst (Var :+: T String))
-}