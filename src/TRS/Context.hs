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

type Context s r = GT s r

emptyC = CtxVar 0

fill,(|>) :: (Traversable t) =>
            Context t r -> GT t r -> GT t r
fill (S ct) x = S$ fmap (fill' x (c-1)) ct
    where c = (length . collect_ isCtxVar) (S ct) 
          fill' a i (CtxVar j) | i == j = a
          fill' a i (S t) = S$ fmap (fill' a i) t 
          fill' _ _ x = x
fill CtxVar{} x = --trace ("Warning! " ++ show x)  
                  x
fill x y = --trace ("Warning2! " ++ show x ++ " |> " ++ show y) 
           x

(|>) = fill

contexts :: Traversable t => GT t r -> [(GT t r,Context t r)]
contexts (S t) = --(CtxVar 0, S t) : 
                 catMaybes (map (context (S t) c) [0..size t - 1])
    where c = (length . collect_ isCtxVar) (S t)
          context :: Traversable t =>
                              GT t r -> Int -> Int -> Maybe (GT t r,Context t r)
          context (S t) depth i = let 
             (a, t') = first (msum . toList) . unzipG $
                        fmap (\(j,u)->if i==j && not (isCtxVar u) 
                                       then (Just u, CtxVar depth) 
                                       else (Nothing,u)) 
                             (unsafeZipG [0..] t)
           in a >>= \a'->return (a',S t')
contexts _ = []

{- -- REVIEW these properties
propIdentity x = and [ ct|>y == x | (y,ct) <- contexts x ]
  where types = (x :: [Int])

propIdentity2 x = and [ ct|>y|>y1 == x | (y1,ct1) <- contexts x
                                                 , (y,ct) <- contexts ct1]
  where types = (x :: [Int])
-}