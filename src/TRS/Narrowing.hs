{-# LANGUAGE FlexibleContexts #-}

module TRS.Narrowing where

import Control.Applicative
import Control.Monad
import Control.Monad.State (get, MonadState)
import Data.AlaCarte
import Data.Traversable

import TRS.Rules
import TRS.Unification
import TRS.Substitutions
import TRS.Context
import TRS.Types
import TRS.Utils

-- narrow1 :: [Rule f] -> Term f -> (Term f, Subst f)
narrow1' ::
  (Var :<: f,      -- TODO Remove this constraint
   Unify f f f,
   Traversable f,
   Hole :<: f,     -- TODO Remove this constraint
   Functor m,
   MonadPlus m,
   MonadState (Subst f) m) =>
  [Rule f] -> Term f -> m (Term f)
narrow1' rr t = go (t, emptyC)
    where go (t, ct) = ((ct |>) <$> narrowTop t)
                       `mplus`
                       msum [go (t, ct|>ct1) | (t, ct1) <- contexts t]

          narrowTop t = msum$ flip map rr $ \r -> do
                          lhs :-> rhs <- variant r t
                          unify1 lhs t
                          apply rhs

--unify' :: Unify f f f => Term f -> Term f ->  (Subst f)
unify' :: (MonadPlus m, Unify f f f, MonadState (Subst f) m) =>
          Term f -> Term f -> m (Subst f)
unify' t u = unify1 t u >> get

narrow1 :: (Var :<: f, Unify f f f, Traversable f, Hole :<: f, MonadPlus m) =>
           [Rule f] -> Term f -> m (Term f, SubstG (Term f))
narrow1 rr t = runU $ narrow1' rr t

narrow  rr t = fixMP     (\(t,s) -> narrow1 rr t >>= \(t', s') -> return (t', s `o` s')) (t,emptySubst)
narrows rr t = closureMP (\(t,s) -> narrow1 rr t >>= \(t', s') -> return (t', s `o` s')) (t,emptySubst)
