{-# OPTIONS_GHC -fdebugging -fglasgow-exts#-}
{-# LANGUAGE UndecidableInstances  #-}
module TRS.Context where
import Control.Arrow
import Data.Foldable
import Data.Maybe
import Data.Traversable
import TRS.Utils
import {-# SOURCE #-} TRS.Core

import Debug.Trace

import Prelude hiding ( all, maximum, minimum, any, mapM_,mapM, foldr, foldl
                      , and, concat, concatMap, sequence, notElem, sum)

{-
What is demanded from a Context
 a - That it can be applied a substitution
 b - That it admits extracting more contexts from it 
 c - It'd be nice to have a term representing the empty context

Ideas for encodings for contexts:
 (1) Function from the hole-filler to the thing
      type Context t a = a -> t a
 (2) t (Holeable a)
      type Hole = Maybe
      type Context = t (Hole a)
 (3) type Context s r = GT s r
      data GT s r = CtxVar (STRef r s)
                  | ...

Reflexions:
 - Hughes in "The Design of a Pretty Printing library" uses contexts in a 
   different way. Instead of manipulating contexts, it manipulates the 
   hole-fillers. Contexts are used in observations: an observation takes a 
   Sequence and a Context and returns the observation: a List. But Contexts
   are not manipulated. However, Contexts are encoded concretely in a variant
   type: there are several kinds of contexts for Sequences: the unit context 
   (i.e. the empty context), the append-to-right context and its sibling
   the append-to-left context.

   Following that concrete encoding, I could encode my context as t (Holeable a)
   taking advantage of Traversable Functoriality. 
 - s(GT s r) or (GT s r)?
   The latter seems more adequate to handle empty contexts
Issues:
 - (2) isn't adequate for a
 - (1) isn't adequate for b
-}
--type Context t a = a -> t a
type Context s r = GT s r

emptyC = CtxVar 0

fill,(|>) :: (Show (Context t r), Traversable t) =>
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

              
--       a = toList t !! i
--    in (a, context)
{-
propIdentity x = and [ ct|>y == x | (y,ct) <- contexts x ]
  where types = (x :: [Int])

propIdentity2 x = and [ ct|>y|>y1 == x | (y1,ct1) <- contexts x
                                                 , (y,ct) <- contexts ct1]
  where types = (x :: [Int])
-}