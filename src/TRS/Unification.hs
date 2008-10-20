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
      Unifyable, Unify(..), Unify2(..), unify, unify1, unifyFdefault,
      ) where

import Control.Monad.State hiding (mapM_, zipWithM_)
import Data.Foldable
import Data.Traversable
import Prelude hiding (mapM_)
import TypePrelude

import TRS.Substitutions
import TRS.Types
import TRS.MonadEnv
import TRS.UMonad
import TRS.Utils

class    (IsVar f, Eq (Term f), Unify f f f) => Unifyable f
instance (IsVar f, Eq (Term f), Unify f f f) => Unifyable f

class (f:<:g, h:<:g) => Unify f h g where
    unifyF :: (MonadPlus m, MonadEnv g m, Unifyable g) => f(Term g) -> h(Term g) -> m ()

class Unify2 isVarF isVarH f h g where unifyF' :: (MonadPlus m, MonadEnv g m, Unifyable g) => isVarF -> isVarH -> f(Term g) -> h(Term g) -> m ()
instance (t :<: g) => Unify2 HTrue HFalse Var t g where unifyF' _ _ v t = varBind (inV v) (inject t)
instance (t :<: g) => Unify2 HFalse HTrue t Var g where unifyF' _ _ t v = varBind (inV v) (inject t)
instance (a:<: g, MatchShape a a g g) => Unify2 HFalse HFalse a a g where unifyF' _ _ = unifyFdefault
instance (a:<:g, b:<:g)               => Unify2 HFalse HFalse a b g  where unifyF' _ _ _x _y = const mzero (_x,_y)

instance (TypeEq2 f Var isVarF, TypeEq2 h Var isVarH, Unify2 isVarF isVarH f h g, f:<:g, h:<:g) => Unify f h g where
    unifyF x y = unifyF' (proxy::isVarF) (proxy::isVarH) x y

instance (Var :<: g) =>Unify Var Var g where
    unifyF v@(Var _ i) w@(Var _ j)
        | i == j    = return ()
        | otherwise = do
              mb_t <- readVar (inV v)
              case mb_t of
                Nothing -> varBind (inV v) (inject w)
                Just t ->  unify1 t (inject w)

instance ((a :+: b) :<: g, Unify c a g, Unify c b g) => Unify c (a :+: b) g where
    unifyF x (Inl y) = unifyF x y
    unifyF x (Inr y) = unifyF x y

instance ((a :+: b) :<: g, Unify c a g, Unify c b g) => Unify (a :+: b) c g where
    unifyF (Inl y) x = unifyF x y
    unifyF (Inr y) x = unifyF x y

instance (Unify a c g, Unify b d g, Unify a d g, Unify b c g, (c:+:d) :<: g, (a:+:b) :<: g) =>
    Unify (a :+: b) (c :+: d) g where
    unifyF (Inl x) (Inl y) = unifyF x y
    unifyF (Inr x) (Inr y) = unifyF x y
    unifyF (Inl x) (Inr y) = unifyF x y
    unifyF (Inr x) (Inl y) = unifyF x y

instance (Eq id, T id :<: g) => Unify (T id) (T id) g where unifyF = unifyFdefault

unifyFdefault :: (MonadPlus m, MonadEnv g m, MatchShape f f g g, Unifyable g) =>
                 f (Term g) -> f (Term g) -> m ()
unifyFdefault t1 t2 = do
      pairs <- maybe mzero return $ matchShapeF t1 t2
      mapM_ (uncurry unify1) pairs

unify1 :: (MonadPlus m, MonadEnv f m, Unifyable f) => Term f -> Term f -> m ()
unify1 (In t) (In u) = {-# SCC "unify1" #-} unifyF t u

unify' :: (MonadPlus m, Unifyable f) => Subst f -> Term f -> Term f -> m (Subst f)
unify' sigma (In t) (In u) = {-# SCC "unify" #-} execStateT (unU$ unifyF t u) sigma

unify :: (MonadPlus m, Unifyable f) => Term f -> Term f -> m (Subst f)
unify = unify' emptySubst

---------------------------------------
-- * Examples
---------------------------------------
{-
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
-}