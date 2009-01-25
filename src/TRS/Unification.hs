{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -fglasgow-exts #-}

module TRS.Unification (
      Unifyable, Unify(..), UnifyL(..), UnifyR(..), unify, unify1,
      ) where

import Control.Monad.State hiding (mapM_, zipWithM_)
import Control.Applicative
import Data.Foldable
import Prelude hiding (mapM_)
import TypePrelude

import TRS.Substitutions
import TRS.Term
import TRS.Types
import TRS.MonadEnv
import TRS.UMonad

class    (IsVar f, HashConsed f, UnifyL f f, Ppr f) => Unifyable f
instance (IsVar f, HashConsed f, UnifyL f f, Ppr f) => Unifyable f

class (f :<: g) => UnifyL f g where
    unifyL :: (MonadPlus m, MonadEnv g m) => f (Term g) -> g (Term g) -> m ()
instance (UnifyL a c, UnifyL b c, (a:+:b):<:c) => UnifyL (a :+: b) c where
    unifyL (Inl x) y = unifyL x y
    unifyL (Inr x) y = unifyL x y
instance UnifyR f g g => UnifyL f g where unifyL = unifyR

class (f1 :<: g, f2 :<: g) => UnifyR f1 f2 g where
    unifyR :: (MonadPlus m, MonadEnv g m) => f1 (Term g) -> f2 (Term g) -> m ()
instance (UnifyR c a g, UnifyR c b g, (a:+:b):<:g) => UnifyR c (a :+: b) g where
    unifyR x (Inl y) = unifyR x y
    unifyR x (Inr y) = unifyR x y
instance (f1:<:g, f2:<:g, Unifyable g, Ppr g, Unify f1 f2) => UnifyR f1 f2 g where unifyR = unifyF

class Unify f1 f2 where
  unifyF :: (f1 :<: g, f2:<:g, Unifyable g, Ppr g, MonadPlus m, MonadEnv g m) =>
            f1(Term g) -> f2(Term g) -> m ()

-- meaningful instances
-- --------------------
instance (t :<: g, Var :<: g, Unifyable g) => UnifyR Var t g where
    unifyR v t = is v (\v' -> varBind (inV v') (inject t))
                      (\v' -> unify1 v' (inject t))

instance (t :<: g, Var :<: g, Unifyable g) => UnifyR t Var g where
    unifyR t v = is v (\v' -> varBind (inV v') (inject t))
                      (\v' -> unify1 v' (inject t))

is v isV isT = maybe (isV v) is' =<< readVar (inV v)
  where is' (open -> Just v@Var{}) = is v isV isT
        is' t = isT t

instance (UnifyR Var a g, UnifyR Var b g, (a:+:b) :<: g) => UnifyR Var (a:+:b) g where
    unifyR x (Inl y) = unifyR x y
    unifyR x (Inr y) = unifyR x y

instance (Unifyable g, Var :<: g) => UnifyR Var Var g where
    unifyR v@(Var n i) w@(Var _ j)
        | i == j    = return ()
        | otherwise = is v (\v' -> varBind (inV v) (inject w)) (unify1 (inject w))

instance (Foldable f, Zip f) => Unify f f where unifyF t u = fzipWith_ unify1 t u
instance Unify f g where unifyF _ _ = mzero


unify1 :: (MonadPlus m, MonadEnv f m, Unifyable f) => Term f -> Term f -> m ()
unify1 (In t) (In u) = {-# SCC "unify1" #-} unifyL t u

unify' :: (MonadPlus m, Unifyable f) => Subst f -> Term f -> Term f -> m (Subst f)
unify' sigma (In t) (In u) = {-# SCC "unify" #-} execStateT (unU$ unifyL t u) sigma

unify :: (MonadPlus m, Unifyable f) => Term f -> Term f -> m (Subst f)
unify = unify' emptySubst

---------------------------------------
-- * Examples
---------------------------------------

{-
--(+:) :: (T String :<: f) => Term f -> Term f -> Term f
(+:) = term2 "+"

--t :: Term (Var :+: T String)
t = x +: y

--t1 :: (T String :<: f) => Term f
t1 = constant "1" +: constant "0"

u1  = unify t t1 `asTypeOf` Nothing
u1' = unify t1 t `asTypeOf` Nothing

u2 :: Maybe (Subst Var)
u2 = unify x y

u3 = unify x (constant "1") :: Maybe (Subst Basic)

--e1 = t `equal` (y +: x)
--e2 = t `equal` t1

u,t' :: Term Basic
t' = term3 "f" x x x
u = term3 "f" (constant "a") (constant "b") y
-}