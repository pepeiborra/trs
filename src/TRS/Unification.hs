{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fglasgow-exts #-}

module TRS.Unification (
      UMonadT(..), evalU, execU, runU,
      Unify(..), unify, unify1,
      equal, apply, freshInstance
      ) where

import Control.Applicative
import Control.Monad.State hiding (mapM_)
import Data.AlaCarte
import Data.Foldable
import Data.List
import Prelude hiding (mapM_)
import TypePrelude
import TypeEqGeneric1()

import TRS.Rules
import TRS.Substitutions
import TRS.Term
import TRS.Types

newtype UMonadT g m a = UMonadT {unU :: StateT (Subst g) m a}
    deriving (Functor, Monad, MonadPlus, MonadState (Subst g), MonadTrans)

variant ::(Var :<: f, Foldable f, MonadState (Subst f) m) => Rule f -> Term f -> m(Rule f)
variant r@(lhs:->_) t = do
  sigma <- get
  let new_vars = var <$> ([1..] \\ ([i | Var i <- vars t] ++ substDomain sigma))
  return $ applySubst (mkSubst (vars lhs `zip` new_vars)) <$>  r

apply  :: (Var :<: g, MonadState (Subst g) m) => Term g -> m (Term g)
apply t = get >>= \sigma -> return (applySubst sigma t)

class (Functor f, Functor g, Functor h) => Unify f h g where
    unifyF :: (MonadPlus m, MonadState (Subst g) m, Unify g g g) => f(Term g) -> h(Term g) -> m ()


instance (Var :<: g) => Unify Var Var g where
    unifyF v@(Var i) w@(Var j)
        | i == j    = return ()
        | otherwise = do
              v' <- apply (inject v)
              w' <- apply (inject w)
              case (match v', match w') of
                 (Nothing, Nothing) -> unify1 v' w'
                 (Nothing, Just _)  -> unify1 w' v'  -- TODO: remove unnecessary extra lookup on w
                 (Just v', Nothing)  -> varBind v' w'
                 (Just v'@Var{}, Just Var{}) -> varBind v' w'

instance (IsVar a va, IsVar b vb, IsSum a sa, IsSum b sb, UnifyH va vb sa sb a b g) => Unify a b g where
    unifyF = unifyH (proxy::va) (proxy::vb) (proxy::sa) (proxy::sb)

{-
instance (MatchShape f g) => Unify f f g where
    unifyF t1 t2 = do
      pairs <- maybe mzero return $ matchShapeF t1 t2
      mapM_ (uncurry unify1) pairs
-}
class (a :<: g, b :<: g) => UnifyH a_var b_var a_sum b_sum a b g where
    unifyH :: (MonadPlus m, MonadState (Subst g) m) => a_var -> b_var -> a_sum -> b_sum -> a (Term g) -> b (Term g) -> m ()

instance ((a :+: b) :<: g, Unify a a g, Unify b b g, Unify a b g, Unify b a g) =>
    UnifyH HFalse HFalse HTrue HTrue (a :+: b) (a :+: b) g where 
    unifyH _ _ _ _ (Inl x) (Inl y) = unifyF x y
    unifyH _ _ _ _ (Inr x) (Inr y) = unifyF x y
    unifyH _ _ _ _ (Inl x) (Inr y) = unifyF x y
    unifyH _ _ _ _ (Inr x) (Inl y) = unifyF x y
{-
instance (Unify a a g, Unify b b g, Unify a b g, Unify b a g, (a :+: b) :<: g, a :<: g, Unify g g g) =>
 UnifyH HFalse bleg HTrue HFalse (a :+: b) a g where
    unifyH _ _ _ _ (Inl x) y = unifyF x y
    unifyH _ _ _ _ (Inr x) y = unifyF x y


instance ( Unify a a g, Unify b b g, Unify a b g, Unify b a g, a :<: g, (a :+: b) :<: g, Unify g g g) =>
 UnifyH bleg HFalse HFalse HTrue a (a :+: b) g where
    unifyH _ _ _ _ x (Inl y) = unifyF x y
    unifyH _ _ _ _ x (Inr y) = unifyF x y
-}
instance (Var :<: g, t :<: g) => UnifyH HTrue HFalse HFalse HFalse Var t g where unifyH _ _ _ _ v t = varBind v (inject t)
instance (Var :<: g, t :<: g) => UnifyH HFalse HTrue HFalse HFalse t Var g where unifyH va vb sa sb t v = unifyH vb va sb sa v t

unifyFdefault :: (MonadPlus m, MonadState (Subst g) m, MatchShape f g, Unify g g g) =>
                 f (Term g) -> f (Term g) -> m ()
unifyFdefault t1 t2 = do
      pairs <- maybe mzero return $ matchShapeF t1 t2
      mapM_ (uncurry unify1) pairs

instance (T :<: g) => Unify T T g where unifyF = unifyFdefault

class Functor f => VarBind f where varBind :: (MonadState (Subst g) m, MonadPlus m) => f(Term g) -> Term g -> m ()
instance VarBind Var where
    varBind t u = do guard (occurs t u) >> get >>= \sigma -> put$ insertSubst t u sigma

occurs _ _ = True --TODO

unify1 :: (MonadPlus m, MonadState (Subst f) m, Unify f f f) => Term f -> Term f -> m ()
unify1 (In t) (In u) = unifyF t u

unify :: (MonadPlus m, Unify f f f) => Subst f -> Term f -> Term f -> m (Subst f)
unify sigma (In t) (In u) = execStateT (unU$ unifyF t u) sigma

unify0 :: (MonadPlus m, Unify f f f) => Term f -> Term f -> m (Subst f)
unify0 = unify emptySubst

runU :: StateT (SubstG a1) m a -> m (a, SubstG a1)
runU  m = runStateT  m emptySubst
evalU :: (Monad m) => StateT (SubstG a1) m a -> m a
evalU m = evalStateT m emptySubst
execU :: (Monad m) => StateT (SubstG a1) m a -> m (SubstG a1)
execU m = execStateT m emptySubst
---------------------------------------
-- * Semantic Equality
---------------------------------------

equal :: (Var :<: f, Unify f f f) => Term f -> Term f -> Bool
equal t u = maybe False isRenaming (unify0 t u)


---------------------------------------
-- * Examples
---------------------------------------

x,y :: (Var :<: f) => Term f
x = var 0
y = var 1

(+:) :: (T :<: f) => Term f -> Term f -> Term f
(+:) = term2 "+"

t :: Term (Var :+: T)
t = x +: y

t1 :: (T :<: f) => Term f
t1 = constant "1" +: constant "0"

u1  = unify0 t t1 `asTypeOf` Nothing
u1' = unify0 t1 t `asTypeOf` Nothing

u2 :: Maybe (Subst Var)
u2 = unify0 x y

u3 = unify0 x (constant "1") :: Maybe (Subst (T :+: Var))

e1 = t `equal` (y +: x)
e2 = t `equal` t1
