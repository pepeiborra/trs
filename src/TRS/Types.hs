{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts, UndecidableInstances, OverlappingInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE StandaloneDeriving #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  TRS.Types
-- Copyright   :  (c) Pepe Iborra 2006-
--                (c) Universidad Politcnica de Valencia 2006-2007
-- License     :  BSD-style (see LICENSE)
--
-- Maintainer  :  pepeiborra@gmail.org
-- Stability   :  experimental
-- Portability :  portable
--
-- Home for all types and helpers. Internal
-----------------------------------------------------------------------------

module TRS.Types (module Data.AlaCarte, module TRS.Types) where

import Control.Applicative
import Data.AlaCarte hiding (Expr(..), match, inject, reinject)
import Data.Char (isAlpha)
import Data.Foldable as Foldable
import Data.Monoid
import Data.Traversable
import Text.PrettyPrint
import Control.Monad       hiding (msum, mapM)
import Prelude hiding ( all, maximum, minimum, any, mapM_,mapM, foldr, foldl
                      , and, concat, concatMap, sequence, sum, elem, notElem)


import TRS.Utils hiding ( parens )

type Unique = Int

-- --------------------------
-- * A la Carte Terms
-- --------------------------

newtype Term t = In (t (Term t))

deriving instance Eq (f (Term f))  => Eq (Term f)
deriving instance Ord (f (Term f)) => Ord (Term f)

foldTerm :: Functor f => (f a -> a) -> Term f -> a
foldTerm f (In t) = f (fmap (foldTerm f) t)

foldTermM :: (Monad m, Traversable f) => (f a -> m a) -> Term f -> m a
foldTermM f (In t) = f =<< mapM (foldTermM f) t

foldTermTop :: Functor f => (f (Term f) -> f(Term f)) -> Term f -> Term f
foldTermTop f (In t)= In (foldTermTop f `fmap` f t)

inject :: (g :<: f) => g (Term f) -> Term f
inject = In . inj

reinject :: (f :<: g) => Term f -> Term g
reinject = foldTerm inject

reinject' :: (f :<: fs, fs :<: gs) => f (Term fs) -> f (Term gs)
reinject' = fmap reinject

match :: (g :<: f) => Term f -> Maybe (g (Term f))
match (In t) = prj t

-- ------------------
-- Basic stuff
-- ------------------

class Functor f => Ppr f where pprF :: f Doc -> Doc
ppr :: Ppr f => Term f -> Doc
ppr = foldTerm pprF


-- -----------------------------
-- * The first building blocks
-- -----------------------------
type Basic = Var :+: T String

data T id a = T !id [a]   deriving Eq
instance Functor (T id)     where fmap f (T s aa) = T s (map f aa)
instance Traversable (T id) where traverse f (T s tt) = T s <$> traverse f tt
instance Foldable (T id)    where foldMap  f (T s tt) = mconcat $ map f tt

data Var s = Var (Maybe String) Int deriving (Eq, Show)
instance Functor Var     where fmap _ (Var s i) = Var s i
instance Traversable Var where traverse _ (Var s i) = pure (Var s i)
instance Foldable Var    where foldMap = foldMapDefault
instance Ord (Var a) where compare (Var _ a) (Var _ b) = compare a b

var :: (Var :<: s) => Int -> Term s
var = {-# SCC "inject" #-}  inject . Var Nothing

var' :: (Var :<: s) => Maybe String -> Int -> Term s
var' = {-# SCC "inject'" #-} (inject.) . Var

varLabeled l = {-# SCC "varLabeled" #-} inject . Var (Just l)

class Functor f => IsVar f where isVarF :: f Bool -> Bool
instance IsVar Var where isVarF _ = True
instance (IsVar a, IsVar b) => IsVar (a:+:b) where
    isVarF (Inr x) = isVarF x
    isVarF (Inl y) = isVarF y
instance Functor otherwise => IsVar otherwise where isVarF _ = False

isVar :: IsVar f => Term f -> Bool
isVar = {-# SCC "isVar" #-} foldTerm isVarF

varId :: (Var :<: s) => String -> Term s -> Int
varId err t = {-# SCC "varId" #-}
              case match t of
                Just (Var _ i) -> i
                Nothing -> error ("varId/" ++ err ++ ": expected a Var term")

varId' :: Var f -> Int
varId' (Var _ i) = {-# SCC "varId'" #-} i

instance Show id => Ppr (T id) where
    pprF (T n []) = text (show n)
    pprF (T n [x,y]) | not (any isAlpha $ show n) = x <+> text (show n) <+> y
    pprF (T n tt) = text (show n) <> parens (cat$ punctuate comma tt)

instance Ppr (T String) where
    pprF (T n []) = text n
    pprF (T n [x,y]) | not (any isAlpha $ n) = x <+> text n <+> y
    pprF (T n tt) = text n <> parens (cat$ punctuate comma tt)

instance Ppr Var where
    pprF (Var Nothing i)  = text$ showsVar 0 i ""
    pprF (Var (Just l) i) = text l -- <> char '_' <> int i
instance (Ppr a, Ppr b) => Ppr (a:+:b) where
    pprF (Inr x) = pprF x
    pprF (Inl y) = pprF y

instance Ppr f => Show (Term f) where show = render . ppr

instance (Ord id, Ord a) => Ord (T id a) where
    (T s1 tt1) `compare` (T s2 tt2) =
        case compare s1 s2 of
          EQ -> compare tt1 tt2
          x  -> x

-- -----------
-- MatchShape
--------------

class    MatchShape f g f g => MatchShapeable f g
instance MatchShape f g f g => MatchShapeable f g

class (f :<: fs, g :<: gs, fs :<: gs) => MatchShape f g fs gs where matchShapeF :: f(Term fs) -> g(Term gs) -> Maybe [(Term fs, Term gs)]

instance (f :<: g, (c :+: d) :<: f, MatchShape c a f g, MatchShape d a f g) => MatchShape (c :+: d) a f g where
    matchShapeF (Inl x) y = matchShapeF x y
    matchShapeF (Inr x) y = matchShapeF x y

instance (fs :<: gs, (c :+: d) :<: gs, MatchShape a c fs gs, MatchShape a d fs gs) => MatchShape a (c :+: d) fs gs where
    matchShapeF x (Inl y) = matchShapeF x y
    matchShapeF x (Inr y) = matchShapeF x y

instance (fs :<: gs, MatchShape a c fs gs, MatchShape b c fs gs, MatchShape a d fs gs, MatchShape b d fs gs, (a :+: b) :<: fs, (c :+: d) :<: gs) =>
        MatchShape (a :+: b) (c :+: d) fs gs where
    matchShapeF (Inl x) (Inl y) = matchShapeF x y
    matchShapeF (Inr x) (Inr y) = matchShapeF x y
    matchShapeF (Inl x) (Inr y) = matchShapeF x y
    matchShapeF (Inr x) (Inl y) = matchShapeF x y

instance (f :<: fs, g :<: gs, fs :<: gs) => MatchShape f g fs gs where matchShapeF _ _ = Nothing
instance (Eq id, T id :<: fs, T id :<: gs, fs :<: gs) => MatchShape (T id) (T id) fs gs where
    matchShapeF (T s1 tt1) (T s2 tt2) = guard(s1 == s2 && length tt1 == length tt2) >> return (zip tt1 tt2)
matchShape :: (MatchShapeable f g) => Term f -> Term g -> Maybe [(Term f, Term g)]
matchShape (In t) (In u) = {-# SCC "matchShape" #-}
                           matchShapeF t u

-----------------
-- Size measures
-----------------
class Foldable f => Size f where sizeF :: f Int -> Int
instance Foldable f => Size f where sizeF f = 1 + sum f

termSize :: (Functor f, Foldable f) => Term f -> Int
termSize = foldTerm sizeF
