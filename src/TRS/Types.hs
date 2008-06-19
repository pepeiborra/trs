{-# OPTIONS_GHC -fglasgow-exts -cpp #-}
{-# OPTIONS_GHC -fallow-undecidable-instances #-}
{-# OPTIONS_GHC -fallow-overlapping-instances #-}
{-# OPTIONS_GHC -fignore-breakpoints #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  TRS.Types
-- Copyright   :  (c) Pepe Iborra 2006-2007
--                (c) Universidad Politécnica de Valencia 2006-2007
-- License     :  BSD-style (see LICENSE)
--
-- Maintainer  :  pepeiborra@gmail.org
-- Stability   :  experimental
-- Portability :  portable
--
-- Home for all types and helpers. Internal
-----------------------------------------------------------------------------

module TRS.Types where

import Control.Applicative
import Control.Monad.Maybe (MaybeT(..))
import Data.AlaCarte
import Data.Char (isAlpha)
import Data.Foldable as Foldable
import Data.AlaCarte
import Data.Traversable as Traversable
import Text.PrettyPrint
import Control.Monad       hiding (msum, mapM)
import Prelude hiding ( all, maximum, minimum, any, mapM_,mapM, foldr, foldl
                      , and, concat, concatMap, sequence, elem, notElem)

import TypePrelude

import TRS.Utils hiding ( parens )

type Unique = Int

-- --------------------------
-- * A la Carte Terms
-- --------------------------

type Term t = Expr t

class Functor f => Ppr f where pprF :: f Doc -> Doc
ppr :: Ppr f => Term f -> String
ppr = render . foldTerm pprF

class (f :<: g) => MatchShape f g where matchShapeF :: f(Term g) -> f(Term g) -> Maybe [(Term g, Term g)]

--instance (Functor a, Functor b) => MatchShape a (a :+: b)
--instance (Functor a, Functor b) => MatchShape b (a :+: b)
instance (MatchShape a (a :+: b), MatchShape b (a :+: b)) => MatchShape (a :+: b) (a :+: b) where
    matchShapeF (Inl x) (Inl y) = matchShapeF x y
    matchShapeF (Inr x) (Inr y) = matchShapeF x y
    matchShapeF _ _ = Nothing

matchShape :: (MatchShape t t) => Expr t -> Expr t -> Maybe [(Term t, Term t)]
matchShape (In t) (In u) = matchShapeF t u

class Functor f => Children f where childrenF :: f [Term g] -> [Term g]
instance (Children f, Children g) => Children (f :+: g) where
    childrenF (Inl x) = childrenF x
    childrenF (Inr y) = childrenF y

subterms, properSubterms :: (Functor f, Foldable f) => Term f -> [Term f]
subterms t = t : properSubterms t

properSubterms t = foldTerm (concat . toList) t

-- -----------------------------
-- * The first building blocks
-- -----------------------------
type BasicT = Term (Var :+: T String)

data T id a = T !id [a]   deriving Eq
instance Functor (T id)     where fmap f (T s aa) = T s (map f aa)
instance Traversable (T id) where traverse f (T s tt) = T s <$> traverse f tt
instance Foldable (T id)    where foldMap = foldMapDefault

newtype Var s = Var Int deriving (Eq, Show)
instance Functor Var     where fmap _ (Var i) = Var i
instance Traversable Var where traverse _ (Var i) = pure (Var i)
instance Foldable Var    where foldMap = foldMapDefault
instance Ord (Var a) where compare (Var a) (Var b) = compare a b

build :: (g :<: f) => g(Term f) -> Term f
build = inject

foldTerm :: Functor f => (f a -> a) -> Expr f -> a
foldTerm = foldExpr

foldTermM :: (Monad m, Traversable f) => (f a -> m a) -> Expr f -> m a
foldTermM = foldExprM

var :: (Var :<: s) => Int -> Term s
var = inject . Var

isVar :: (Var :<: s) => Term s -> Bool
isVar t | Just (Var{}) <- match t = True
        | otherwise             = False

varId :: (Var :<: s) => String -> Term s -> Int
varId err t = case match t of
                Just (Var i) -> i
                Nothing -> error ("varId/" ++ err ++ ": expected a Var term")

term :: (T id :<: f) => id -> [Term f] -> Term f
term s = inject . T s

term1 :: (T id :<: f) => id -> Term f -> Term f
term1 f t       = term f [t]
term2 :: (T id :<: f) => id -> Term f -> Term f -> Term f
term2 f t t'    = term f [t,t']
term3 :: (T id :<: f) => id -> Term f -> Term f -> Term f -> Term f
term3 f t t' t''= term f [t,t',t'']
constant :: (T id :<: f) => id -> Term f
constant f      = term f []


instance Show id => Ppr (T id) where
    pprF (T n []) = text (show n)
    pprF (T n [x,y]) | not (any isAlpha $ show n) = x <+> text (show n) <+> y
    pprF (T n tt) = text (show n) <+> parens (cat$ punctuate comma tt)
instance Ppr Var         where pprF (Var i) = text$ showsVar 0 i ""
instance (Ppr a, Ppr b) => Ppr (a:+:b) where
    pprF (Inr x) = pprF x
    pprF (Inl y) = pprF y

instance Ppr f => Show (Term f) where show = ppr

instance Children (T id)      where childrenF (T _ s)   = concat s
instance Children Var         where childrenF _         = []

instance (Ord id, Ord a) => Ord (T id a) where
    (T s1 tt1) `compare` (T s2 tt2) =
        case compare s1 s2 of
          EQ -> compare tt1 tt2
          x  -> x

--instance (Var :<: g) => MatchShape Var g where matchShapeF _ _ = Nothing
instance (Eq id, T id :<: g) => MatchShape (T id) g where
    matchShapeF (T s1 tt1) (T s2 tt2) = guard(s1 == s2 && length tt1 == length tt2) >> return (zip tt1 tt2)


------------------------------
-- MaybeT MonadPlus instance
------------------------------
instance Monad m => MonadPlus (MaybeT m) where
    m1 `mplus` m2 = MaybeT$ runMaybeT m1 >>= \t1 ->
                     case t1 of
                       Nothing -> runMaybeT m2
                       _       -> return t1
    mzero = MaybeT (return Nothing)

------------------------------
-- Type Class Programming
------------------------------
class IsSum (a :: * -> *) issum | a -> issum
instance true  ~ HTrue  =>IsSum (a :+: b) true
instance false ~ HFalse => IsSum b false

class IsVar (a :: * -> *) isvar | a -> isvar
instance true  ~ HTrue  => IsVar Var true
instance false ~ HFalse => IsVar b false

