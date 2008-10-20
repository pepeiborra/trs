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
import Control.Monad.Logic
import Data.Foldable (Foldable)
import Data.List ((\\))
import Data.Traversable

import TRS.Term
import TRS.Rules
import TRS.MonadEnv
import TRS.MonadFresh
import TRS.UMonad
import TRS.Unification
import TRS.Substitutions
import TRS.Context
import TRS.Types
import TRS.Utils hiding (interleave)

-- The Var and Hole constraints should be made unnecessary
class    (Hole :<: f, Var :<: f, IsVar f, Unifyable f, Traversable f, Var :<: rf, IsVar rf, Foldable rf, rf :<: f) => Narrowable rf f
instance (Hole :<: f, Var :<: f, IsVar f, Unifyable f, Traversable f, Var :<: rf, IsVar rf, Foldable rf, rf :<: f) => Narrowable rf f

-- narrow1 :: [Rule f] -> Term f -> (Term f, Subst f)
{-# INLINE narrowStepBasic #-}
narrowStepBasic :: forall rf f m. (Narrowable rf f, MonadLogic m, MonadFresh m, MonadEnv f m) => [Rule rf] -> Term f -> m (Term f)
narrowStepBasic rr t = {-# SCC "narrowStepBasic1" #-}
   go (t, emptyC)
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
unify' :: (Unifyable f, MonadEnv f m, MonadEnv g m, MonadPlus m) => Term f -> Term f -> m (Subst g)
unify' t u = unify1 t u >> getEnv

narrow1' :: (Narrowable rf f, Functor m, MonadLogic m) => [Rule rf] -> Term f -> m (Term f, SubstG (Term f))
narrow1' rr t = {-# SCC "narrow1" #-}
               runN ([0..] \\ map varId (vars t)) (narrowStepBasic rr t >>= apply)

narrow' :: (Narrowable rf f, Functor m, MonadLogic m) => [Rule rf] -> Term f -> m (Term f, Subst f)
narrow'  rr t = {-# SCC "narrow" #-}
               runN ([0..] \\ map varId (vars t))
                    (fixMP(\t -> narrowStepBasic rr t >>= apply) t)

narrows' :: (Narrowable rf f, Functor m, MonadLogic m) => [Rule rf] -> Term f -> m (Term f, Subst f)
narrows' rr t = {-# SCC "narrows" #-}
               runN ([0..] \\ map varId (vars t))
                    (closureMP (narrowStepBasic rr >=> apply) t)


narrow1 :: (Narrowable rf f, Functor m, MonadLogic m) => [Rule rf] -> Term f -> m (Term f, Subst f)
narrow1 rr t = {-# SCC "narrow1" #-}
               second (`restrictTo` vars' t) <$> narrow1' rr t

narrow :: (Narrowable rf f, Functor m, MonadLogic m) => [Rule rf] -> Term f -> m (Term f, Subst f)
narrow  rr t = {-# SCC "narrow" #-}
               second (`restrictTo` vars' t) <$> narrow' rr t

narrows :: (Narrowable rf f, Functor m, MonadLogic m) => [Rule rf] -> Term f -> m (Term f, Subst f)
narrows rr t = {-# SCC "narrows" #-}
               second (`restrictTo` vars' t) <$> narrows' rr t

narrowBounded :: forall rf f m . (Narrowable rf f, Functor m, MonadLogic m) => (Term f -> Bool) -> [Rule rf] -> Term f -> m (Term f, Subst f)
narrowBounded pred rr t = {-# SCC "narrowBounded" #-}
                          second (`restrictTo` vars' t) <$> runN ([0..] \\ map varId (vars t)) (go t) where
 go :: (MonadFresh m1, MonadLogic m1, MonadEnv f m1) => Term f -> m1(Term f)
 go t = do
    t' <- narrowStepBasic rr t >>= apply
    if pred t' then go t' else return t'

-- * Basic Narrowing
narrow1Basic :: (Narrowable rf f, Functor m, MonadLogic m) => [Rule rf] -> Term f -> m (Term f, SubstG (Term f))
narrow1Basic = narrow1

narrowsBasic :: (Narrowable rf f, MonadEnv f m, MonadLogic m) => [Rule rf] -> Term f -> m (Term f, Subst f)
narrowsBasic rr t = {-# SCC "narrowsBasic" #-} second (`restrictTo` vars' t) <$> runN ([0..] \\ map varId (vars t)) (closureMP (narrowStepBasic rr) t >>= apply)

narrowBasic :: (Narrowable rf f, Functor m, MonadLogic m) => [Rule rf] -> Term f -> m (Term f, Subst f)
narrowBasic rr t = {-# SCC "narrowBasic" #-} second (`restrictTo` vars' t) <$> runN ([0..] \\ map varId (vars t)) (fixMP (narrowStepBasic rr) t >>= apply)

narrowBasicBounded :: forall rf f m. (IsVar f, Narrowable rf f, Functor m, MonadLogic m) => (Term f -> Bool) -> [Rule rf] -> Term f -> m (Term f, Subst f)
narrowBasicBounded pred rr t = {-# SCC "narrowBasicBounded" #-} second (`restrictTo` vars' t) <$> runN ([0..] \\ map varId (vars t)) (go t >>= apply) where
    go :: (MonadFresh m1, MonadEnv f m1, MonadLogic m1) => Term f -> m1(Term f)
    go t = do
      t' <- narrowStepBasic rr t
      if pred t' then go t' else return t'

vars' :: (Var :<: f, Foldable f) => Term f -> [Term Var]
vars' = map inV . vars