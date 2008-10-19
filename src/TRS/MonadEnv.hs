{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
module TRS.MonadEnv where

import Control.Monad
import Control.Monad.State.Class

import TRS.Types
import TRS.Utils
import TRS.Substitutions

class (Functor m, Monad m) => MonadEnv f m | m -> f where
    varBind :: Var (Term g) -> Term f -> m ()
    readVar :: Var (Term g) -> m (Maybe (Term f))
    apply   :: (Var :<: f) => Term f -> m (Term f)
    getEnv  :: m (Subst f)

readVarDefault :: (Var :<: f, MonadEnv f m) => Var (Term g) -> m (Maybe (Term f))
readVarDefault v@(Var n i) = do
  t <- apply (var' n i)
  return $ case match t of
             Just (Var _ i') | i == i' -> Nothing
             otherwise -> Just t

instance (Eq (Term f), Var :<: f, Functor m, MonadState (Subst f) m) => MonadEnv f m where
    varBind t u = {-# SCC "varBind" #-}  modify (insertSubst t u)
    apply t = {-# SCC "apply" #-}  get >>= \sigma -> return (fixEq (applySubst sigma) t)
    getEnv  = get
    readVar = {-# SCC "readVar" #-}  gets . flip lookupSubst

occurs _ _ = True --TODO
