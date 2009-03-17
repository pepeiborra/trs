{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE PolymorphicComponents #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}

module TRS.Rewriting (
      Rewritable, Match(..), MatchL(..), MatchR(..), Matchable,
      match, match', matches,
      rewrite1,  reduce,  rewrites,
--      rewrite1S, reduceS, rewritesS,
      (=.=), EqModulo_(..), EqModulo, equal, equalG,
      isNF, isRootDefined, isNotRootDefined
    ) where

import Control.Applicative
import Control.Monad (mzero, mplus, MonadPlus, foldM)
import Control.Monad.Logic.Class
import Control.Monad.State (evalState)
import Data.Foldable as F
import Data.List ((\\))
import Data.Maybe (isJust)
import Data.Monoid
import Data.Traversable
import Prelude hiding (mapM, concat, zipWith)

import TRS.Term
import TRS.Types hiding (size)
import TRS.Rules
import TRS.Substitutions
import TRS.UMonad
import TRS.MonadFresh
import TRS.Utils hiding (someSubterm)

isNF :: (Rewritable rf f) => [Rule rf] -> Term f -> Bool
isNF = (null.) . rewrite1

isNotRootDefined, isRootDefined :: (Zip f, rf :<: f, HashConsed f) => [Rule rf] -> Term f -> Bool
--isRootDefined rr t = Prelude.any (flip matches t . cap . lhs) rr where
--   cap (In x) = In $ evalState (fzipWith (\_ _ -> var <$> fresh) x x) [0..]

isRootDefined rr (In t) = F.any (\((reinject -> In l) :-> _) -> isJust (fzip t l)) rr

isNotRootDefined rr = not . isRootDefined rr

-----------------------------
-- * Matching
-----------------------------
class    (Var :<: f, Var :<: g, IsVar g, HashConsed g, Zip f, Zip g, Traversable f, Traversable g, MatchL f g f, MatchL g g g) => Matchable f g
instance (Var :<: f, Var :<: g, IsVar g, HashConsed g, Zip f, Zip g, Traversable f, Traversable g, MatchL f g f, MatchL g g g) => Matchable f g

class    (IsVar f, HashConsed rf, IsVar rf, Var :<: rf, Traversable rf, rf :<: f, Matchable f f) => Rewritable rf f
instance (IsVar f, HashConsed rf, IsVar rf, Var :<: rf, Traversable rf, rf :<: f, Matchable f f) => Rewritable rf f

class (f:<:fs) => MatchL f g fs where matchL :: (Matchable g g) => f(Term fs) -> g(Term g) -> Maybe (Subst g)
instance (MatchL c a fs, MatchL d a fs, (c:+:d) :<: fs) => MatchL (c:+:d) a fs where
    matchL (Inl x) y = matchL x y
    matchL (Inr x) y = matchL x y
instance (Var:<:fs, IsVar g)      => MatchL Var g fs where matchL (Var _ i) t = Just $ mkSubst [(i, In t)]
instance (f:<:fs,MatchR f g fs g) => MatchL f   g fs where matchL = matchR

class IsVar fs => MatchR f g fs gs where matchR :: (Matchable gs gs) => f (Term fs) -> g (Term gs) -> Maybe (Subst gs)
instance (MatchR a c fs gs, MatchR a d fs gs, IsVar fs) => MatchR a (c :+: d) fs gs where
    matchR x (Inl y) = matchR x y
    matchR x (Inr y) = matchR x y
instance (f:<:fs, g:<:gs, fs :<: gs, IsVar fs, Match f g) => MatchR f g fs gs where matchR = matchF

class    Match f g     where matchF :: (Matchable gs gs, IsVar fs, f :<: fs, g :<: gs, fs :<: gs) => f (Term fs) -> g (Term gs) -> Maybe (Subst gs)
instance Match f g     where matchF _ _ = Nothing
instance Zip f => Match f f where
  matchF t u = fzip t u >>= F.foldr matchOne (return mempty) where
     matchOne (t,u) mtheta = do
       theta1 <- mtheta
       theta2 <- match (applySubst theta1 t) u
       return (theta1 `mappend` theta2)

match' :: (Matchable pattern f) => Term pattern -> Term f -> Maybe (Subst f)
match' (In t) (In u) = {-# SCC "match'" #-} matchL t u

match :: (Matchable f f) => Term f -> Term f -> Maybe (Subst f)
match t u = {-# SCC "match" #-} match' t u

matches :: (Matchable pattern f) => Term pattern -> Term f -> Bool
matches = (isJust.). match'

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
       rewriteTop t = F.msum $ forEach rr' $ \r -> do
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