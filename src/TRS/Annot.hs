
module TRS.Annot where

import Control.Applicative
import Data.Foldable
import Data.Monoid
import Data.Traversable

import TRS.Types
import TRS.Core

newtype Annot annot termshape t = Annot (termshape t, annot)
  deriving (Eq, Show)

instance Functor termshape => Functor (Annot annot termshape) where
  fmap f (Annot (t, a)) = Annot (fmap f t, a)

instance Foldable termshape => Foldable (Annot annot termshape) where
  foldMap f (Annot (t,a)) = foldMap f t

instance Traversable termshape => Traversable (Annot annot termshape) where
  traverse f (Annot (t,a)) = (\t' -> Annot (t', a)) <$> traverse f t

instance TermShape t => TermShape (Annot annot t) where
  matchTerm (Annot (x,a)) (Annot (y,b)) = matchTerm x y