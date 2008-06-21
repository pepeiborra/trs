{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleContexts #-}
module TRS.UMonad where

import Control.Applicative
import Control.Monad.State
import Data.AlaCarte
import Data.Foldable
import Data.List ((\\))

import TRS.Substitutions
import TRS.Types
import TRS.Term
import TRS.Rules

newtype UMonadT g m a = UMonadT {unU :: StateT (Subst g) m a}
    deriving (Functor, Monad, MonadPlus, MonadState (Subst g), MonadTrans)


runU :: StateT (SubstG a1) m a -> m (a, SubstG a1)
runU  m = runStateT  m emptySubst
evalU :: (Monad m) => StateT (SubstG a1) m a -> m a
evalU m = evalStateT m emptySubst
execU :: (Monad m) => StateT (SubstG a1) m a -> m (SubstG a1)
execU m = execStateT m emptySubst


variant ::(Var :<: f, Foldable f, MonadState (Subst f) m) => Rule f -> Term f -> m(Rule f)
variant r@(lhs:->_) t = do
  sigma <- get
  let new_vars = var <$> ([1..] \\ ([i | Var i <- vars t] ++ substDomain sigma))
  return $ applySubst (mkSubst (vars lhs `zip` new_vars)) <$>  r

apply  :: (Var :<: g, MonadState (Subst g) m) => Term g -> m (Term g)
apply t = get >>= \sigma -> return (applySubst sigma t)
