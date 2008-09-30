{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module TRS.Narrowing where

import Control.Monad
import Control.Monad.State (get, MonadState)
import Data.Traversable

import TRS.Rules
import TRS.Unification
import TRS.Substitutions
import TRS.Context
import TRS.Types
import TRS.Utils

-- The Var and Hole constraints should be made unnecessary
class    (Var :<: f, Hole :<: f, Unifyable f, Traversable f) => Narrowable f
instance (Var :<: f, Hole :<: f, Unifyable f, Traversable f) => Narrowable f

-- narrow1 :: [Rule f] -> Term f -> (Term f, Subst f)
narrow1' ::
  (Narrowable f, MonadPlus m, MonadState (Subst f) m) =>
  [Rule f] -> Term f -> m (Term f)
narrow1' rr t = go (t, emptyC)
    where go (t, ct) = ((ct |>) `liftM` narrowTop t)
                       `mplus`
                       msum [go (t, ct|>ct1) | (t, ct1) <- contexts t]

          narrowTop t = msum$ flip map rr $ \r -> do
                          lhs :-> rhs <- variant r t
                          unify1 lhs t
                          apply rhs

--unify' :: Unify f f f => Term f -> Term f ->  (Subst f)
unify' :: (MonadPlus m, Unifyable f, MonadState (Subst f) m) =>
          Term f -> Term f -> m (Subst f)
unify' t u = unify1 t u >> get

narrow1 :: (Narrowable f, MonadPlus m) => [Rule f] -> Term f -> m (Term f, SubstG (Term f))
narrow1 rr t = runU $ narrow1' rr t

narrow :: (Narrowable f, MonadPlus1 m) =>
          [Rule f] -> Term f -> m (Term f, Subst f)
narrow  rr t = fixMP  (\(t,s) -> narrow1 rr t >>= \(t', s') -> return (t', s `o` s')) (t,emptySubst)

narrows :: (Narrowable f, MonadPlus m) => [Rule f] -> Term f -> m (Term f, Subst f)
narrows rr t = closureMP (\(t,s) -> narrow1 rr t >>= \(t', s') -> return (t', s `o` s')) (t,emptySubst)

-- * Basic Narrowing

narrowsBasic :: (Narrowable f, MonadPlus m) => [Rule f] -> Term f -> m (Term f, Subst f)
narrowsBasic rr = runU . closureMP (narrow1' rr)

--narrowBasic :: (Narrowable f, MonadPlus1 m) => [Rule f] -> Term f -> m (Term f, Subst f)
narrowBasic rr = runU . fixMP (narrow1' rr)

narrowBounded :: (Narrowable f, MonadPlus m) => (Term f -> Bool) -> [Rule f] -> Term f -> m (Term f, Subst f)
narrowBounded pred rr t = go t emptySubst where
  go t s = do
    (t',s') <- narrow1 rr t
    if pred t then go t' (s `o` s') else return (t,s)