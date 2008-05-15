{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}

module TRS.Rewriting (
      Match(..), match, matchFdefault,
      rewrite1, rewrite1', rewrites, rewrites', reduce
    ) where

import Control.Applicative
import Control.Monad (mzero, mplus, MonadPlus)
import Control.Monad.State (MonadState)
import Data.AlaCarte hiding (match)
import Data.Foldable
import Data.Traversable
import Prelude hiding (mapM, concat)

import TRS.Term
import TRS.Types
import TRS.Rules
import TRS.Substitutions
import TRS.Unification
import TRS.Utils hiding (someSubterm)

-----------------------------
-- * Matching
-----------------------------
matchFdefault :: (Var :<: g, Match g g g, MatchShape f g) => f (Term g) -> f (Term g) -> Maybe (Subst g)
matchFdefault t1 t2 = concatSubst <$> (mapM (uncurry match) =<< matchShapeF t1 t2)

class (f :<: g, h :<: g) => Match f h g where matchF :: Match g g g => f(Term g) -> h(Term g) -> Maybe (Subst g)
--instance (Functor a, Functor b, Functor g) => Match a b g where matchF _ _ = Nothing

instance (Var :<: g) => Match Var Var g where matchF (Var i) (Var j) = Just mkSubst [(i,var j)]

instance ( Match a a g, Match b b g, Match a b g, Match b a g, (a :+: b) :<: g) =>
        Match (a :+: b) (a :+: b) g where
    matchF (Inl x) (Inl y) = matchF x y
    matchF (Inr x) (Inr y) = matchF x y
    matchF (Inl x) (Inr y) = matchF x y
    matchF (Inr x) (Inl y) = matchF x y

instance (f :<: g, Var :<: g) => Match Var f g where matchF (Var i) t = Just $ mkSubst [(i, inject t)]

{-
instance (Match c b g, (a :+: b) :<: g ) => Match c (a :+: b) g where
    matchF x (Inr y) = matchF x y
    matchF x _       = Nothing
-}
{-
instance (Var :<: g, MatchShape f g) => Match f f g where
    matchF t1 t2 = concatSubst <$> (mapM (uncurry match) =<< matchShapeF t1 t2)
-}
instance (any :<: g, Var :<: g) => Match any Var g where matchF _ _ = Nothing

instance (T :<: g, Var :<: g) => Match T T g where
    matchF = matchFdefault

{-

instance (f :<: g, Var :<: g) => Match f Var g where matchF t (Var i) = Nothing --Just $ mkSubst [(i, inject t)]

instance (Match a a (a :+: b), Functor b) => Match a (a :+: b) (a :+: b) where
    matchF x (Inl y) = matchF x y
    matchF x (Inr y) = Nothing


{-
instance (Match c b (a :+: b), c :<: a :+: b, Functor a) => Match c (a :+: b) (a :+: b) where
    matchF x (Inr y) = matchF x y
    matchF x (Inl y) = Nothing
-}


instance (Match c b (a :+: b), Functor a, (a :+: b) ~ g, Match c b g, (a :+: b) :<: g
         ) => Match c (a :+: b) g where
    matchF x (Inr y) = matchF x y
    matchF x (Inl y) = Nothing

-- instance (f :<: g, Var :<: g) => Match Var f g where matchF (Var i) t = Just $ mkSubst [(i, inject t)]
-- We want to have the instance above, but with the least priority possible, so that
-- it will not fire until the Functor sum is decomposed completely.
-- E.g. don't fire for match Var (Var :+:T), wait until match Var T
-- The trick is to use an auxiliary class

-}
{-
instance (IsSum g issum, IsVar f isvar, MatchVar isvar issum f g h, f :<: h, g :<: h) => Match f g h where
    matchF = matchVar (undefined::isvar) (undefined::issum)

class    MatchVar isvar issum var sum g where
    matchVar :: isvar -> issum -> var (Term g) -> sum (Term g) -> Maybe (Subst g)
instance (Var :<: g, f :<: g) => MatchVar HTrue  bah    Var f        g where matchVar _ _ (Var i) t = Just $ mkSubst [(i, inject t)]
instance (Match c b (a :+: b) ) => MatchVar HFalse HTrue c  (a :+: b) (a :+: b) where
    matchVar _ _ a (Inr y) = matchF a y
    matchVar _ _ _ _       = Nothing
instance MatchVar HFalse HFalse f   h        g  where matchVar _ _ a b = a `seq` b `seq` Debug.Trace.trace "MatchVar2" Nothing
-}
match :: (Match t t t) => Expr t -> Expr t -> Maybe (Subst t)
match (In t) (In u) = matchF t u


----------------------------------------
-- * Rewriting
----------------------------------------
rewrite1 :: (Traversable f, Match f f f, Var :<: f, MonadPlus m) =>
            [Rule f] -> Term f -> m (Term f)
rewrite1 rr t = evalU $ rewrite1' rr t
rewrites :: (MonadPlus m, Var :<: f, Match f f f, Traversable f) =>
            [Rule f] -> Term f -> m (Term f)
rewrites rr t = evalU $ rewrites' rr t

rewrite1' :: ( Traversable f, Match f f f, Var :<: f
            , Functor m, MonadPlus m, MonadState (Subst f) m) => [Rule f] -> Term f -> m (Term f)
rewrite1' rr t = rewriteTop t `mplus` someSubterm (rewrite1' rr) t
    where -- rewriteTop :: (MonadPlus m, MonadState (Subst f) m) => Term f -> m (Term f)
          rewriteTop t = Data.Foldable.msum $ flip map rr $ \r -> do
                          lhs:->rhs <- variant r t
                          case match lhs t of
                               Just subst -> return$ applySubst subst rhs
                               Nothing    -> mzero

rewrites' ::
  (MonadState (Subst f) m,
   MonadPlus m,
   Functor m,
   Var :<: f,
   Match f f f,
   Traversable f) =>
  [Rule f] -> Term f -> m (Term f)
rewrites' rr = closureMP (rewrite1' rr)

reduce :: (Traversable f, Match f f f, Var :<: f, MonadPlus m, Eq (f(Expr f))) => [Rule f] -> Term f -> m(Term f)
reduce rr x= evalU (reduce1 rr x)

reduce1 ::
  (MonadPlus m,
   Eq (f (Expr f)),
   Var :<: f,
   Match f f f,
   Traversable f) =>
  [Rule f] -> Term f -> m (Term f)
reduce1 rr x = let
  tt = rewrite1 rr x
  in if tt == mzero then return x else msum $ reduce1 rr `map` tt

---------------------------------------
-- * Examples
---------------------------------------
{-
x,y :: (Var :<: f) => Term f
x = var 0
y = var 1

(+:) :: (T :<: f) => Term f -> Term f -> Term f
(+:) = term2 "+"

t :: Term (Var :+: T)
t = x +: y

t1 :: (T :<: f) => Term f
t1 = constant "1" +: constant "0"

m1 = match t t1
m1' = match t1 t

m2 :: Maybe (Subst (Var :+: T))
m2 = match x y

m3 = match x (constant "1") :: Maybe (Subst (Var :+: T))
-}