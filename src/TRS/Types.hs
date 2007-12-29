{-# OPTIONS_GHC -fglasgow-exts #-}
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

module TRS.Types ( ST, runST, stToIO, RealWorld
		 , STRef, newSTRef, readSTRef, writeSTRef
		 , module TRS.Types) where

import Control.Applicative
import Control.Arrow
import Data.Char (isAlpha)
import Data.Foldable as Foldable
import Data.List (sortBy)
import qualified Data.Map as Map
import Data.Maybe
import Data.Monoid
import Data.Traversable as Traversable
import Text.PrettyPrint
import Control.Monad       hiding (msum, mapM)
import Control.Monad.Error (MonadError, Error(..))
import Control.Monad.Fix
import Control.Monad.Trans
import Control.Monad.State (gets, modify, evalState)
import Control.Monad.ST
import qualified Control.Monad.ST as ST
import Data.STRef
import Test.QuickCheck hiding (collect)
import Prelude hiding ( all, maximum, minimum, any, mapM_,mapM, foldr, foldl
                      , and, concat, concatMap, sequence, elem, notElem)


import TRS.Utils hiding ( parens )

type Unique = Int

-----------------------------
-- * The Class of Match-ables
-----------------------------

class (Traversable s) => TermShape s where
    matchTerm     :: s x -> s x -> Maybe [(x,x)]


-- --------------------------
-- * Basic Shape of Terms
-- --------------------------

data BasicShape a = T !String [a]
    deriving Eq

instance Show a => Show (BasicShape a) where 
    show (T s [])   = s
    show (T s [x,y]) | not (any isAlpha s)
                     = show x ++ ' ':s ++ ' ':show y
    show (T s tt)   = render (text s <> parens( hcat$ punctuate comma (map (text.show) tt)))
--    showList []     = ""
--    showList (t:tt) = show t ++ ' ' : showList tt


instance Ord a => Ord (BasicShape a) where
    (T s1 tt1) `compare` (T s2 tt2) = 
        case compare s1 s2 of
          EQ -> compare tt1 tt2
          x  -> x

instance Traversable BasicShape where
    traverse f (T s tt) = T s <$> traverse f tt
instance Functor BasicShape where
    fmap = fmapDefault
instance Foldable BasicShape where
    foldMap = foldMapDefault

instance TermShape BasicShape where
  matchTerm (T s1 tt1) (T s2 tt2) = if s1==s2 && length tt1 == length tt2
              then Just (zip tt1 tt2)
              else Nothing

{-
-----------------------------------------
-- * The Vars monad
-----------------------------------------

{- | A monad providing variables with identity
     mkVar i == mkVar i
-}
class Monad m => VarMonad m v | m -> v where
  getVar    :: Unique -> m v
  newUnique :: m Unique
  fresh     :: m v
-}
-----------------------
-- * Exceptions
-----------------------
data TRSException = Match (MatchException)
                  | Unify (UnifyException)
                  | Stuck
  deriving (Show,Eq)
data MatchException = GenErrorMatch
                    | ShapeErrorMatch
  deriving (Show,Eq)
#ifdef __HADDOCK__
data UnifyException = 
    GenErrorUnify   |
    ShapeErrorUnify |
    OccursError     
#else
data UnifyException where 
    GenErrorUnify   :: UnifyException
    ShapeErrorUnify :: Show a => a -> a -> UnifyException
    OccursError     :: UnifyException
#endif
instance Show UnifyException where
  show GenErrorUnify = "Unification: general error"
  show OccursError   = "Unification: occurs  error"
  show (ShapeErrorUnify x y) = "Can't unify " ++ show x ++ " and " ++ show y

instance Eq UnifyException where
  GenErrorUnify == GenErrorUnify = True
  OccursError   == OccursError   = True
  ShapeErrorUnify _ _ == ShapeErrorUnify _ _ = True
  _ ==  _ = False

instance Error TRSException where
  noMsg    = Match GenErrorMatch
  strMsg _ = Match GenErrorMatch

genErrorMatch   = Match GenErrorMatch
shapeErrorMatch = Match ShapeErrorMatch

genErrorUnify   = Unify GenErrorUnify
shapeErrorUnify :: Show a => a -> a -> TRSException
shapeErrorUnify = (Unify.) . ShapeErrorUnify
occursError     = Unify OccursError

--------------------------------
-- Other Instances and base operators
--------------------------------
--    showList  = unlines . map show
{-
instance Show(GTE r s) => Show(GT r s) where
    show = show . eqGT  

instance (Functor s, Show(s(GTE r s))) => Show(s(GT r s)) where
    show = show . fmap eqGT 
-}
--instance Arbitrary(GTE r s) => Arbitrary(GT r s) where
--    arbitrary = fmap idGT arbitrary 

