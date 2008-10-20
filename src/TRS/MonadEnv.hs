{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE PatternGuards #-}
module TRS.MonadEnv where

import Control.Monad
import Control.Monad.State.Class

import TRS.Types
import TRS.Utils
import TRS.Substitutions

class (Functor m, Monad m, IsVar f) => MonadEnv f m | m -> f where
    varBind :: (IsVar g, Ppr g) => Term g -> Term f -> m ()
    readVar :: IsVar g => Term g -> m (Maybe (Term f))
    apply   :: (IsVar g, g:<:f) => Term g -> m (Term f)
    getEnv  :: m (Subst f)

readVarDefault :: (IsVar g, IsVar f, g:<:f, MonadEnv f m) => Term g -> m (Maybe (Term f))
readVarDefault v | Just i <- uniqueId v = do
                               t <- apply v
                               return $ case uniqueId t of
                                          Just i' | i == i' -> Nothing
                                          otherwise -> Just t
                 | otherwise = return Nothing


instance (IsVar f, Functor m, MonadState (Subst f) m) => MonadEnv f m where
    varBind t u = {-# SCC "varBind" #-}  modify (insertSubst t u)
    apply t = {-# SCC "apply" #-}  get >>= \sigma -> return (applySubst sigma t)
    getEnv  = get
    readVar = {-# SCC "readVar" #-}  gets . flip lookupSubst

occurs _ _ = True --TODO
