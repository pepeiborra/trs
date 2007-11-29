{-# OPTIONS_GHC -fallow-undecidable-instances #-}
{-# OPTIONS_GHC -fallow-overlapping-instances #-}

module TRS.Terms where

import Data.Traversable
import TRS.Types
import TRS.Term

instance (TermShape s, Traversable s) => Term (TermStatic_ Int) s 
instance (Term t s, TermShape s) => Eq (t s) 
uc :: a -> b