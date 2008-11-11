{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances #-}
module TRS.MonadFresh where

import Control.Applicative
import Control.Monad.State
import Data.Foldable
import Data.List ((\\))
import Prelude hiding (concatMap)

import TRS.Types
import TRS.Term
import TRS.Utils
import TRS.Substitutions

class (Functor m, Monad m) => MonadFresh m where
    fresh :: m Int
    variant :: (HashConsed f, Var :<: fs, IsVar fs, Foldable fs, fs :<: f, Var :<: f, IsVar f, Functor t, Foldable t) => t (Term fs) -> m(t (Term f))
  -- The Functor requirement is not necessary, but I find it convenient
  -- Functor should be a siuperclass of Monad

instance (Functor m, MonadState [Int] m) => MonadFresh m where
    fresh = {-# SCC "fresh1" #-} get >>= \(x:xs) -> put xs >> return x
    variant r = {-# SCC "variant1" #-} do
     names <- get
     let vars_r = snub (concatMap vars r)
         (vars', names') = splitAt (length vars_r) names
     put names'
     return $ applySubst (mkSubst (vars_r `zip` map var vars')) <$> r


-- | Takes a term t and a term u and returns a variant of t which is fresh w.r.t. u
variant' :: (Var :<: f, IsVar f, Foldable f, HashConsed f, Functor t, Foldable t) => t(Term f) -> t(Term f) -> t(Term f)
variant' t u = evalState (variant t) ([0..] \\ (varId <$> concatMap vars u))
