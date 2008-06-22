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
      Unifyable, unify, unify', unify1, unifyFdefault,
      equal, variant, apply
      ) where

import Control.Monad.State hiding (mapM_)
import Data.AlaCarte
import Data.Foldable
import Prelude hiding (mapM_)
import TypePrelude


import TRS.Substitutions
import TRS.Types
import TRS.UMonad

class Unify f f f => Unifyable f
instance Unify f f f => Unifyable f

class (Functor f, Functor g, Functor h) => Unify f h g where
    unifyF :: (MonadPlus m, MonadState (Subst g) m, Unify g g g) => f(Term g) -> h(Term g) -> m ()

class Unify2 isVarF isVarH f h g where unifyF' :: (MonadPlus m, MonadState (Subst g) m, Unify g g g) => isVarF -> isVarH -> f(Term g) -> h(Term g) -> m ()
instance (Var :<: g, t :<: g) => Unify2 HTrue HFalse Var t g where unifyF' _ _ v t = varBind v (inject t)
instance (Var :<: g, t :<: g) => Unify2 HFalse HTrue t Var g where unifyF' _ _ t v = varBind v (inject t)
instance (Functor a, Functor g, MatchShape a g) => Unify2 HFalse HFalse a a g where unifyF' _ _ = unifyFdefault
instance (Functor a, Functor b, Functor g) => Unify2 HFalse HFalse a b g where unifyF' _ _ _x _y = const mzero (_x,_y)

instance (TypeEq2 f Var isVarF, TypeEq2 h Var isVarH, Unify2 isVarF isVarH f h g
         ,Functor f, Functor g, Functor h) => Unify f h g where unifyF x y = unifyF' (proxy::isVarF) (proxy::isVarH) x y

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

instance ((a :+: b) :<: g, Unify c a g, Unify c b g) => Unify c (a :+: b) g where
    unifyF x (Inl y) = unifyF x y
    unifyF x (Inr y) = unifyF x y

instance ((a :+: b) :<: g, Unify c a g, Unify c b g) => Unify (a :+: b) c g where
    unifyF (Inl y) x = unifyF x y
    unifyF (Inr y) x = unifyF x y

instance (Unify a c g, Unify b d g, Unify a d g, Unify b c g) =>
    Unify (a :+: b) (c :+: d) g where
    unifyF (Inl x) (Inl y) = unifyF x y
    unifyF (Inr x) (Inr y) = unifyF x y
    unifyF (Inl x) (Inr y) = unifyF x y
    unifyF (Inr x) (Inl y) = unifyF x y

instance (Eq id, T id :<: g) => Unify (T id) (T id) g where unifyF = unifyFdefault

unifyFdefault :: (MonadPlus m, MonadState (Subst g) m, MatchShape f g, Unifyable g) =>
                 f (Term g) -> f (Term g) -> m ()
unifyFdefault t1 t2 = do
      pairs <- maybe mzero return $ matchShapeF t1 t2
      mapM_ (uncurry unify1) pairs


class Functor f => VarBind f where varBind :: (MonadState (Subst g) m, MonadPlus m) => f(Term g) -> Term g -> m ()
instance VarBind Var where
    varBind t u = do guard (occurs t u) >> get >>= \sigma -> put$ insertSubst t u sigma

occurs _ _ = True --TODO

unify1 :: (MonadPlus m, MonadState (Subst f) m, Unifyable f) => Term f -> Term f -> m ()
unify1 (In t) (In u) = unifyF t u

unify' :: (MonadPlus m, Unifyable f) => Subst f -> Term f -> Term f -> m (Subst f)
unify' sigma (In t) (In u) = execStateT (unU$ unifyF t u) sigma

unify :: (MonadPlus m, Unifyable f) => Term f -> Term f -> m (Subst f)
unify = unify' emptySubst
---------------------------------------
-- * Semantic Equality
---------------------------------------

equal :: (Var :<: f, Unifyable f) => Term f -> Term f -> Bool
equal t u = maybe False isRenaming (unify t u)


---------------------------------------
-- * Examples
---------------------------------------

x,y :: (Var :<: f) => Term f
x = var 0
y = var 1

(+:) :: (T String :<: f) => Term f -> Term f -> Term f
(+:) = term2 "+"

t :: Term (Var :+: T String)
t = x +: y

t1 :: (T String :<: f) => Term f
t1 = constant "1" +: constant "0"

u1  = unify t t1 `asTypeOf` Nothing
u1' = unify t1 t `asTypeOf` Nothing

u2 :: Maybe (Subst Var)
u2 = unify x y

u3 = unify x (constant "1") :: Maybe (Subst (T String :+: Var))

e1 = t `equal` (y +: x)
e2 = t `equal` t1
