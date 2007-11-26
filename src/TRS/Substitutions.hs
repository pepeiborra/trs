{-# OPTIONS_GHC -fallow-undecidable-instances #-}
module TRS.Substitutions where

import Data.Foldable (Foldable)
import Data.Monoid
import Data.Traversable
import qualified Data.Map as Map

import TRS.Types

----------------------
-- * Substitutions
----------------------
newtype SubstG a = Subst {subst::[a]}
   deriving (Foldable, Functor, Traversable)

type SubstM x      = SubstG (Maybe x)

emptyS = Subst mempty

emptySubstM = emptyS :: SubstM a

fromSubst (Subst sub) = sub
mkSubst = Subst

mkSubstM :: [Int] -> [a] -> SubstM a
mkSubstM ii vv = let
    table = Map.fromList (zip ii vv)
  in Subst (map (`Map.lookup` table) [0 .. maximum ii])

