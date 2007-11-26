module TRS.Core where

import TRS.Types
import {-# SOURCE #-} TRS.GTerms

import Data.Foldable
import Data.Traversable

class Prune (mode :: *) where prune :: GT_ mode r s  -> ST r (GT_ mode r s)
col 	  :: (Prune mode, Traversable s) => GT_ mode r s  -> ST r (GT_ mode r s)    
