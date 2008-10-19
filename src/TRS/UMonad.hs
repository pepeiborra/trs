{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}

module TRS.UMonad ( module TRS.UMonad,
                    module TRS.MonadEnv,
                    module TRS.MonadFresh ) where

import Control.Arrow
import Control.Monad.State
import Control.Monad.Logic.Class

import TRS.MonadEnv
import TRS.MonadFresh
import TRS.Rules
import TRS.Substitutions
import TRS.Types
import TRS.Utils

type RMonadT   m a = GMonadT [Int] m a
type UMonadT f m a = GMonadT (Subst f) m a
type NMonadT f m a = GMonadT (Subst f, [Int]) m a

newtype GMonadT s m a = GMonadT {unU :: StateT s m a}
    deriving (Functor, Monad, MonadPlus, MonadPlus1, MonadLogic, MonadState s, MonadTrans)

instance (Monad m) => MonadFresh (GMonadT (b, [Int]) m) where
    variant r t = withSnd $ variant r t
    fresh       = withSnd fresh

instance (Eq (Term f), Var :<: f, Monad m) => MonadEnv f (GMonadT (Subst f, b) m) where
    varBind t = withFst . varBind t
    apply     = withFst . apply
    getEnv    = withFst get
    readVar   = withFst . readVar

{-# INLINE evalR #-}
{-# INLINE evalG #-}

--evalU acc sigma = evalStateT (unU acc) sigma
runG s acc = runStateT (unU acc) s
evalG s m  = evalStateT (unU m)  s

-- runR :: Monad m => RMonadT m a -> m (a, [Int])
runR = runG
runU :: (Var :<: f, Eq (Term f), Monad m) => UMonadT f m a -> m (a, Subst f)
runU = runG emptySubst
runN :: (Var :<: f, Eq (Term f), Monad m) => [Int] -> NMonadT f m a -> m (a, Subst f)
runN vars = liftM (second fst) . runG (emptySubst, vars)

evalR :: Monad m => [Int] -> RMonadT m a -> m a
evalR = evalG
evalU :: Monad m => UMonadT f m a -> m a
evalU = evalG emptySubst
evalN :: Monad m => [Int] -> NMonadT f m a -> m a
evalN vars = evalG (emptySubst, vars)

execU :: Monad m => UMonadT f m a -> m (Subst f)
execU acc = execStateT (unU acc) emptySubst

applyF  :: (Var :<: f, f:<:fs, MonadState (Subst fs) m) => f(Term fs) -> m (Term fs)
applyF t = get >>= \sigma -> return (applySubstF sigma t)

startingFromTerm m t = m 