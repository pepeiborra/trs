module TRS.Core where

import TRS.Types
import {-# SOURCE #-} TRS.GTerms

import Data.Foldable
import Data.Traversable

class Prune (mode :: *) where prune :: GT_ user mode r s  -> ST r (GT_ user mode r s)
instance Prune Basic
instance Prune Syntactic
instance Prune Semantic

col 	  :: (Prune mode, Traversable s) => GT_ user mode r s  -> ST r (GT_ user mode r s)    
generalize ::(Prune mode, TermShape s) => GT_ user mode r s -> ST r (GT_ user mode r s)
generalizeG::(Prune mode, TermShape s,Traversable f) => 
               f(GT_ user mode r s) -> ST r (f(GT_ user mode r s))

semEq :: (Prune mode, TermShape s) => GT_ user mode r s -> GT_ user mode r s -> ST r Bool
