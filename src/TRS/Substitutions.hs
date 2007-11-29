{-# OPTIONS_GHC -fallow-undecidable-instances #-}
module TRS.Substitutions where

import Control.Applicative
import Data.Foldable (Foldable(..))
import Data.Monoid
import Data.Traversable
import qualified Data.Map as Map

import TRS.Types
import TRS.Utils

----------------------
-- * Substitutions
----------------------
newtype SubstG a = Subst {fromSubst::[a]}
   deriving (Foldable, Functor, Traversable, Monoid, Show)

newtype SubstM a = SubstM {fromSubstM :: [Maybe a]}
   deriving (Monoid, Show)

emptyS :: SubstG a
emptyS = mempty
emptySubstM :: SubstM a
emptySubstM = mempty

mkSubst = Subst

mkSubstM :: [Int] -> [a] -> SubstM a
mkSubstM [] _  = mempty
mkSubstM ii vv = let
    table = Map.fromList (zip ii vv)
  in SubstM (map (`Map.lookup` table) [0 .. maximum ii])


instance Traversable SubstM where
    traverse f (SubstM x) = SubstM <$> (traverse .traverse) f x

instance Functor SubstM where 
    fmap f (SubstM x) = SubstM $ map (fmap f) x

instance Foldable SubstM where foldMap = foldMapDefault