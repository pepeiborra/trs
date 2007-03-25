{-# OPTIONS_GHC -fglasgow-exts -fno-mono-pat-binds -fallow-undecidable-instances -fallow-incoherent-instances -fallow-overlapping-instances -funbox-strict-fields#-}

-----------------------------------------------------------------------------
-- |
-- Module      :  TRS.Terms
-- Copyright   :  (c) Pepe Iborra 2006-2007
--                (c) Universidad Politécnica de Valencia 2006-2007
-- License     :  BSD-style (see LICENSE)
--
-- Maintainer  :  pepeiborra@gmail.org
-- Stability   :  experimental
-- Portability :  portable
--
-- Datatype for Terms, used for testing
-----------------------------------------------------------------------------

module TRS.Terms where
import Control.Applicative
import Control.Monad hiding (mapM, sequence )
import Data.Traversable
import TRS.Types
import TRS.Utils
import Text.PrettyPrint
import Data.Char (isAlpha)
import Data.Foldable
import Prelude hiding ( all, maximum, minimum, any, mapM_,mapM, foldr, foldl
                      , sequence, concat, concatMap )
import GHC.Exts (unsafeCoerce#)

data TermST a = T !String [a]
    deriving Eq

type Term r = GTE TermST r

type RewRule r = Rule TermST r 

term = (s.) . T

instance Ord a => Ord (TermST a) where
    (T s1 tt1) `compare` (T s2 tt2) = 
        case compare s1 s2 of
          EQ -> compare tt1 tt2
          x  -> x

---------------------------------------------------------
-- Instantiation of the generic 'module-like' structure
---------------------------------------------------------

instance Traversable TermST where
    traverse f (T s tt) = T s <$> traverse f tt
instance Functor TermST where
    fmap = fmapDefault
instance Foldable TermST where
    foldMap = foldMapDefault

instance RWTerm TermST where
  matchTerm (T s1 tt1) (T s2 tt2) = if s1==s2 && length tt1 == length tt2
              then Just (zip tt1 tt2)
              else Nothing

---------------------------------
-- Auxiliary code
---------------------------------
{-
instance Eq (Term a) where 
  t1 == t2 = (S t1) `equal` (S t2)
-}

instance Show a => Show (TermST a) where 
    show (T s [])   = s
    show (T s [x,y]) | not (any isAlpha s)
                     = show x ++ ' ':s ++ ' ':show y
    show (T s tt)   = render (text s <> parens( hcat$ punctuate comma (map (text.show) tt)))
--    showList []     = ""
--    showList (t:tt) = show t ++ ' ' : showList tt
 
--sh = text . show


class Outputable a where
  ppr :: a -> Doc

----------------------------------
-- Other stuff looking for a home
----------------------------------

uc = unsafeCoerce#
ucT t = uc t :: GTE TermST r
ucR r = uc r :: Rule TermST r

