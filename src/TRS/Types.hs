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

module TRS.Types (module Data.AlaCarte, module TRS.Types) where

import Control.Applicative
import Data.AlaCarte hiding (Expr(..), match, inject)
import Data.Char (isAlpha)
import Data.Foldable as Foldable
import Data.Monoid
import Data.Traversable
import Text.PrettyPrint
import Control.Monad       hiding (msum, mapM)
import Prelude hiding ( all, maximum, minimum, any, mapM_,mapM, foldr, foldl
                      , and, concat, concatMap, sequence, elem, notElem)


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

match :: (g :<: f) => Term f -> Maybe (g (Term f))
match (In t) = prj t

-- ------------------
-- Basic stuff
-- ------------------

class Functor f => Ppr f where pprF :: f Doc -> Doc
ppr :: Ppr f => Term f -> String
ppr = render . foldTerm pprF


-- -----------------------------
-- * The first building blocks
-- -----------------------------
type BasicT = Term (Var :+: T String)

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
var = inject . Var Nothing

var' :: (Var :<: s) => Maybe String -> Int -> Term s
var' = (inject.) . Var

varLabeled l = inject . Var (Just l)

isVar :: (Var :<: s) => Term s -> Bool
isVar t | Just (Var{}) <- match t = True
        | otherwise             = False

varId :: (Var :<: s) => String -> Term s -> Int
varId err t = case match t of
                Just (Var _ i) -> i
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
    pprF (T n tt) = text (show n) <> parens (cat$ punctuate comma tt)

instance Ppr (T String) where
    pprF (T n []) = text n
    pprF (T n [x,y]) | not (any isAlpha $ n) = x <+> text n <+> y
    pprF (T n tt) = text n <> parens (cat$ punctuate comma tt)

instance Ppr Var where
    pprF (Var Nothing i)  = text$ showsVar 0 i ""
    pprF (Var (Just l) _) = text l
instance (Ppr a, Ppr b) => Ppr (a:+:b) where
    pprF (Inr x) = pprF x
    pprF (Inl y) = pprF y

instance Ppr f => Show (Term f) where show = ppr

instance (Ord id, Ord a) => Ord (T id a) where
    (T s1 tt1) `compare` (T s2 tt2) =
        case compare s1 s2 of
          EQ -> compare tt1 tt2
          x  -> x

-- -----------
-- MatchShape
--------------

class MatchShape f f => MatchShapeable f
instance MatchShape f f => MatchShapeable f
class (f :<: g) => MatchShape f g where matchShapeF :: f(Term g) -> f(Term g) -> Maybe [(Term g, Term g)]

--instance (Functor a, Functor b) => MatchShape a (a :+: b)
--instance (Functor a, Functor b) => MatchShape b (a :+: b)
instance (MatchShape a (a :+: b), MatchShape b (a :+: b)) => MatchShape (a :+: b) (a :+: b) where
    matchShapeF (Inl x) (Inl y) = matchShapeF x y
    matchShapeF (Inr x) (Inr y) = matchShapeF x y
    matchShapeF _ _ = Nothing

--instance (Var :<: g) => MatchShape Var g where matchShapeF _ _ = Nothing
instance (f :<: g) => MatchShape f g where matchShapeF _ _ = Nothing
instance (Eq id, T id :<: g) => MatchShape (T id) g where
    matchShapeF (T s1 tt1) (T s2 tt2) = guard(s1 == s2 && length tt1 == length tt2) >> return (zip tt1 tt2)
matchShape :: (MatchShapeable t) => Term t -> Term t -> Maybe [(Term t, Term t)]
matchShape (In t) (In u) = matchShapeF t u

subterms, properSubterms :: (Functor f, Foldable f) => Term f -> [Term f]
subterms (In t) = In t : concat (subterms <$> toList t)
properSubterms = tail . subterms
