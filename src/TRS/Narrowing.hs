{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

module TRS.Narrowing
 ( Narrowable, isRNF,
   narrow1, narrow, narrows, narrowBounded,
   narrow1', narrow', narrows',
   inn_narrowing, inn_Bnarrowing,
   narrow1Basic, narrowBasic, narrowsBasic, narrowBasicBounded
 )
 where

import Control.Applicative
import Control.Arrow
import Control.Monad.Logic
import Data.Foldable (Foldable)
import Data.List ((\\))
import Data.Traversable (Traversable)

import TRS.Term hiding (vars')
import TRS.Rules
import TRS.MonadEnv
import TRS.MonadFresh
import TRS.UMonad
import TRS.Unification
import TRS.Substitutions
import TRS.Context
import TRS.Types
import TRS.Utils hiding (interleave)

-- | Rigid Normal Form
isRNF :: (Narrowable rf f) => [Rule rf] -> Term f -> Bool
--isRNF rr t = {-# SCC "isRNF" #-} (null . observeMany 1 . narrow1 rr) t
isRNF = \rr -> {-# SCC "isRNF" #-}  \t -> (null . observeMany 1 . narrow1 rr) t


-- The Var and Hole constraints should be made unnecessary
class    (Hole :<: f, Var :<: f, IsVar f, Unifyable f, Traversable f, Var :<: rf, IsVar rf, Foldable rf, rf :<: f) => Narrowable rf f
instance (Hole :<: f, Var :<: f, IsVar f, Unifyable f, Traversable f, Var :<: rf, IsVar rf, Foldable rf, rf :<: f) => Narrowable rf f

-- narrow1 :: [Rule f] -> Term f -> (Term f, Subst f)
{-# INLINE narrowStepBasic #-}
narrowStepBasic :: forall rf f m. (Narrowable rf f, MonadLogic m, MonadFresh m, MonadEnv f m) => [Rule rf] -> Term f -> m (Term f)
narrowStepBasic rr t = {-# SCC "narrowStepBasic1" #-}
   go (t, emptyC)
    where go (t, ct) = ((ct |>) `liftM` narrowTop t)
                       `mplusP`
                       msumP [go (t, ct|>ct1) | (t, ct1) <- contexts t]
          narrowTop :: Term f -> m(Term f)
          narrowTop t = msumP$ flip map rr $ \r -> do
                          guard (not $ isVar t)
                          lhs :-> rhs <- variant r
                          unify1 lhs t
                          return (hashCons rhs)

--unify' :: Unify f f f => Term f -> Term f ->  (Subst f)
unify' :: (Unifyable f, MonadEnv f m, MonadEnv g m, MonadPlus m) => Term f -> Term f -> m (Subst g)
unify' t u = unify1 t u >> getEnv

apply' :: (HashConsed f, MonadEnv f m) => Term f -> m (Term f)
apply' = apply >=> return . hashCons

-- ------------------------------
-- * Narrowing
-- ------------------------------
narrow1 :: (Narrowable rf f, Functor m, MonadLogic m) => [Rule rf] -> Term f -> m (Term f, Subst f)
narrow1 rr t = {-# SCC "narrow1" #-}
               second (`restrictTo` vars' t) <$> narrow1' rr t

narrow :: (Narrowable rf f, Functor m, MonadLogic m) => [Rule rf] -> Term f -> m (Term f, Subst f)
narrow  rr t = {-# SCC "narrow" #-}
               second (`restrictTo` vars' t) <$> narrow' rr t

narrows :: (Narrowable rf f, Functor m, MonadLogic m) => [Rule rf] -> Term f -> m (Term f, Subst f)
narrows rr t = {-# SCC "narrows" #-}
               second (`restrictTo` vars' t) <$> narrows' rr t

-- ** Dirty versions
--  These versions do not trim the substitution before returning

narrow1' :: (Narrowable rf f, Functor m, MonadLogic m) => [Rule rf] -> Term f -> m (Term f, SubstG (Term f))
narrow1' rr t = {-# SCC "narrow1" #-}
               runN ([0..] \\ map varId (vars t)) (narrowStepBasic rr t >>= apply')

narrow' :: (Narrowable rf f, Functor m, MonadLogic m) => [Rule rf] -> Term f -> m (Term f, Subst f)
narrow'  rr t = {-# SCC "narrow" #-}
               runN ([0..] \\ map varId (vars t))
                    (fixMP(\t -> narrowStepBasic rr t >>= apply') t)

narrows' :: (Narrowable rf f, Functor m, MonadLogic m) => [Rule rf] -> Term f -> m (Term f, Subst f)
narrows' rr t = {-# SCC "narrows" #-}
               runN ([0..] \\ map varId (vars t))
                    (closureMP (narrowStepBasic rr >=> apply') t)

------------------------------
-- * Narrowing under Strategies
-- ---------------------------

-- ** Innermost narrowing
inn_narrowing :: (Narrowable rf f, Functor m, MonadLogic m) => [Rule rf] -> Term f -> m (Term f, Subst f)
inn_narrowing rr t = runN ([0..] \\ map varId (vars t)) (fixMP (innStepBasic rr >=> apply') t)

innStepBasic rr t = do
     rr' <- mapM variant rr
     let go (t, ct) = ifte (msumP [go (t, ct|>ct1) | (t, ct1) <- contexts t]) return ((ct |>) `liftM` narrowTop t)
         narrowTop t = msumP $ flip map rr' $ \(lhs:->rhs) -> do
                          guard (not $ isVar t)
                          unify1 lhs t
                          return (hashCons rhs)
     go (t, emptyC)

narrowBounded :: forall rf f m . (Narrowable rf f, Functor m, MonadLogic m) => (Term f -> Bool) -> [Rule rf] -> Term f -> m (Term f, Subst f)
narrowBounded pred rr t = {-# SCC "narrowBounded" #-}
                          second (`restrictTo` vars' t) <$> runN ([0..] \\ map varId (vars t)) (go t) where
 go :: (MonadFresh m1, MonadLogic m1, MonadEnv f m1) => Term f -> m1(Term f)
 go t = do
    t' <- narrowStepBasic rr t >>= apply'
    if pred t' then go t' else return t'

-- ** Basic Narrowing
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

-- ** Innermost Basic Narrowing

inn_Bnarrowing :: (Narrowable rf f, Functor m, MonadLogic m) => [Rule rf] -> Term f -> m (Term f, Subst f)
inn_Bnarrowing rr t =  runN ([0..] \\ map varId (vars t)) (fixMP (innStepBasic rr) t)


-- like vars' in TRS.Term but with less constraints
vars' :: (Var :<: f, Foldable f) => Term f -> [Term Var]
vars' = map inV . vars