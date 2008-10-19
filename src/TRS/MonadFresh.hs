{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances #-}
module TRS.MonadFresh where

import Control.Applicative
import Control.Monad.State.Class
import Control.Monad.Logic.Class
import Data.Foldable

import TRS.Types
import TRS.Term
import TRS.Utils
import TRS.Rules
import TRS.Substitutions

class (Functor m, Monad m) => MonadFresh m where
    fresh :: m Int
    variant :: (f :<: fs, Var :<: f, Var :<: fs, Foldable f, Foldable fs) => Rule f -> Term fs -> m(Rule fs)
  -- The Functor requirement is not necessary, but I find it convenient
  -- Functor should be a siuperclass of Monad

instance (Functor m, MonadState [Int] m) => MonadFresh m where
    fresh = {-# SCC "fresh1" #-} get >>= \(x:xs) -> put xs >> return x
    variant r@(lhs:->rhs) t = {-# SCC "variant1" #-} do
     names <- get
     let vars_r = snub (vars lhs ++ vars rhs)
         (vars', names') = splitAt (length vars_r) names
     put names'
     return $ applySubst (mkSubst (vars_r `zip` map var vars')) <$>  r
