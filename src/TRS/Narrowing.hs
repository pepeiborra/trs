{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

module TRS.Narrowing
-- ( Narrowable, narrow1, narrow, narrows, narrowBounded,
--   narrow1Basic, narrowBasic, narrowsBasic, narrowBasicBounded
-- )
 where

import Control.Applicative
import Control.Arrow
import Control.Monad
import Data.Foldable (Foldable)
import Data.Traversable

import TRS.Term
import TRS.Rules
import TRS.UMonad
import TRS.Unification
import TRS.Substitutions
import TRS.Context
import TRS.Types
import TRS.Utils

-- The Var and Hole constraints should be made unnecessary
class    (Var :<: f, Hole :<: f, Unifyable f, Traversable f, Var :<: rf, Foldable rf, rf :<: f) => Narrowable rf f
instance (Var :<: f, Hole :<: f, Unifyable f, Traversable f, Var :<: rf, Foldable rf, rf :<: f) => Narrowable rf f

-- narrow1 :: [Rule f] -> Term f -> (Term f, Subst f)
narrowStepBasic :: forall rf f m. (Narrowable rf f, MonadPlus m, MonadFresh m, MonadEnv f m) => [Rule rf] -> Term f -> m (Term f)
narrowStepBasic rr t = go (t, emptyC)
    where go (t, ct) = ((ct |>) `liftM` narrowTop t)
                       `mplus`
                       msum [go (t, ct|>ct1) | (t, ct1) <- contexts t]
          narrowTop :: Term f -> m(Term f)
          narrowTop t = msum$ flip map rr $ \r -> do
                          guard (not $ isVar t)
                          lhs :-> rhs <- variant r t
                          unify1 lhs t
                          return rhs

--unify' :: Unify f f f => Term f -> Term f ->  (Subst f)
unify' :: (MonadEnv f m, MonadEnv g m, Unifyable f) => Term f -> Term f -> m (Subst g)
unify' t u = unify1 t u >> getEnv

narrow1 :: (Narrowable rf f, Functor m, MonadPlus m) => [Rule rf] -> Term f -> m (Term f, SubstG (Term f))
narrow1 rr t = second (`restrictTo` vars t) <$> runN (narrowStepBasic rr t >>= apply)

narrow :: (Narrowable rf f, MonadPlus1 m) =>
          [Rule rf] -> Term f -> m (Term f, Subst f)
narrow  rr t = second (`restrictTo` vars t) <$> runN(fixMP(narrowStepBasic rr >=> apply) t)

narrows :: (Narrowable rf f, Functor m, MonadPlus m) => [Rule rf] -> Term f -> m (Term f, Subst f)
narrows rr t = second (`restrictTo` vars t) <$> runN(closureMP (narrowStepBasic rr >=> apply) t)

narrowBounded :: forall rf f m . (Narrowable rf f, Functor m, MonadPlus m) => (Term f -> Bool) -> [Rule rf] -> Term f -> m (Term f, Subst f)
narrowBounded pred rr t = second (`restrictTo` vars t) <$> runN (go t) where
 go :: (MonadFresh m1, MonadEnv f m1) => Term f -> m1(Term f)
 go t = do
    t' <- narrowStepBasic rr t >>= apply
    if pred t' then go t' else return t'

-- * Basic Narrowing
narrow1Basic :: (Narrowable rf f, Functor m, MonadPlus m) => [Rule rf] -> Term f -> m (Term f, SubstG (Term f))
narrow1Basic = narrow1

narrowsBasic :: (Narrowable rf f, MonadEnv f m, MonadPlus m) => [Rule rf] -> Term f -> m (Term f, Subst f)
narrowsBasic rr t = second (`restrictTo` vars t) <$> runN(closureMP (narrowStepBasic rr) t >>= apply)

narrowBasic :: (Narrowable rf f, MonadPlus1 m) => [Rule rf] -> Term f -> m (Term f, Subst f)
narrowBasic rr t = second (`restrictTo` vars t) <$> runN(fixMP (narrowStepBasic rr) t >>= apply)

narrowBasicBounded :: forall rf f m. (Narrowable rf f, Functor m, MonadPlus m) => (Term f -> Bool) -> [Rule rf] -> Term f -> m (Term f, Subst f)
narrowBasicBounded pred rr t = second (`restrictTo` vars t) <$> runN (go t >>= apply) where
    go :: (MonadFresh m1, MonadEnv f m1) => Term f -> m1(Term f)
    go t = do
      t' <- narrowStepBasic rr t
      if pred t' then go t' else return t'