{-# OPTIONS_GHC -fglasgow-exts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverlappingInstances #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  TRS.Context
-- Copyright   :  (c) Pepe Iborra 2006-2007
--                (c) Universidad Politécnica de Valencia 2006-2007
-- License     :  BSD-style (see LICENSE)
--
-- Maintainer  :  pepeiborra@gmail.org
-- Stability   :  experimental
-- Portability :  portable
--
-- Context-of-a-term management.
-----------------------------------------------------------------------------

module TRS.Context where
import Control.Applicative
import Data.Foldable
import Data.HashTable (hashInt, hashString)
import Data.Traversable
import Text.PrettyPrint

import TRS.Utils hiding (brackets)
import TRS.Types
import TRS.Term

import Prelude hiding ( all, maximum, minimum, any, mapM_,mapM, foldr, foldl
                      , and, concat, concatMap, sequence, notElem, sum)

-- | What is a context? A term with a hole.
--   The hole is represented by the constructor CtxVar
type Context f = Term f

-- A CtxVar carries an index, which must be unique
newtype Hole f = Hole Int deriving (Show, Eq, Ord)

instance Functor Hole     where fmap _ (Hole i) = Hole i
instance Foldable Hole    where foldMap = foldMapDefault
instance Traversable Hole where traverse _ (Hole i) = pure (Hole i)

emptyC :: (Hole :<: f) => Term f
emptyC = hole 0

hole :: (Hole :<: f) => Int -> Term f
hole = inject . Hole

-- | Fill a hole in a context
fill,(|>) :: (Hole :<: f) => Context f -> Term f -> Term f
fill ct t = {-# SCC "fill" #-}
            foldTerm fill' ct
    where fill' ct | Just (Hole 0) <- prj ct = t
                   | Just (Hole i) <- prj ct = hole (i-1)
                   | otherwise = In ct

(|>) = fill

-- | Returns a list of subterms and the corresponding contexts
--   | forall subterm ctx . (subterm, ctx) <- contexts t ==> ctx |> subterm = t
contexts :: (Hole :<: f, Traversable f, HashConsed (Term f)) => Term f -> [(Term f, Context f)]
contexts t@(In f) = {-# SCC "contexts" #-}
     let t' = shiftC 1 t in
             [ (shiftC (-1) t_i, u)
             | i <- [1..size f]
             , (u, t_i) <- updateAt' [i] t' (hole 0) ]

-- | Shift the indexes of the context vars
shiftC :: (Hole :<: t) => Int -> Term t -> Term t
shiftC n t = {-# SCC "shiftC" #-} foldTerm f t
           where f t | Just (Hole i) <- prj t = hole $! (i + n)
                     | otherwise = In t

instance Ppr Hole where pprF (Hole i) = brackets (int i)
instance (Hole :<: fs, Hole :<: gs, fs :<: gs) => MatchShape Hole Hole fs gs where matchShapeF _ _ = Nothing

--instance (Hole :<: g) => Match Hole Hole g where matchF _ _ = Nothing
--instance (Hole :<: g, a :<: g) => Match Hole a g where matchF _ _ = Nothing
-- instance (Hole :<: g, Functor h) => Unify Hole g h where unifyF _ _ = mzero

instance HashTerm   Hole where hashF (Hole i) = hashInt (1001 + i)
--instance HashConsed (Term (Hole :+: Basic)) where ht = newHt