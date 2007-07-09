module TRS.Terms where

import Data.Traversable
import TRS.Types hiding (Term)
import TRS.Term

instance (TermShape s, Traversable s) => Term (TermStatic_ Int) s 
