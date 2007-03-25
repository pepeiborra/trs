{-# OPTIONS_GHC -fglasgow-exts #-}
{-# LANGUAGE UndecidableInstances #-}
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
import Control.Arrow
import Data.Foldable
import Data.Maybe
import Data.Traversable
import TRS.Utils
import TRS.Types

import Debug.Trace

import Prelude hiding ( all, maximum, minimum, any, mapM_,mapM, foldr, foldl
                      , and, concat, concatMap, sequence, notElem, sum)


-- | What is a context? A term with a hole.
--   The hole is represented by the constructor CtxVar
type Context s r = GT s r

-- A CtxVar carries an index, which must be unique
emptyC = CtxVar 0

-- | Fill a hole in a context
fill,(|>) :: Traversable t => Context t r -> GT t r -> GT t r
fill (S ct) x = S (fmap fill' ct)
    where fill' (CtxVar 0) = x
          fill' (CtxVar i) = CtxVar (i-1)
          fill' (S t)      = S$ fmap fill' t 
          fill' x          = x
fill CtxVar{} x = --trace ("Warning! " ++ show x)  
                  x
fill x y = --trace ("Warning2! " ++ show x ++ " |> " ++ show y) 
           x
           
(|>) = fill

-- | Returns a list of subterms and the corresponding contexts
--   | forall subterm ctx . (subterm, ctx) <- contexts t ==> ctx |> subterm = t
contexts :: Traversable t => GT t r -> [(GT t r, Context t r)]
contexts (S t) = [contexts i | i <- [1..size t]]
    where 
      shift_t    = shiftC 1 (S t)
      contexts i = first (shiftC (-1)) $ swap$ fromJust$ updateAt' shift_t [i] (CtxVar 0)
      swap (x,y) = (y,x)
contexts _ = []

-- | Shift the indexes of the contexts inside
--shiftC :: Functor t => GT t r -> GT t r
shiftC n (S t) = S$ fmap (shiftC n) t
shiftC n (CtxVar i) = CtxVar $! (i + n)
shiftC _ x = x
