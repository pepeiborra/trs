{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances #-}
module TRS.MonadFresh where

import Control.Applicative
import Control.Monad.State
import Data.Foldable
import Data.List ((\\))
import Prelude hiding (concatMap)

class (Functor m, Monad m) => MonadFresh m where
    fresh   :: m Int
    current :: m Int

  -- The Functor requirement is not necessary, but I find it convenient
  -- Functor should be a siuperclass of Monad

instance (Functor m, MonadState [Int] m) => MonadFresh m where
    fresh = {-# SCC "fresh1" #-} get >>= \(_:x':xs) -> put (x':xs) >> return x'
    current  = head <$> get