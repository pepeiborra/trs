{-# OPTIONS_GHC -fallow-undecidable-instances #-}
module TRS.Rules where

import Control.Applicative
import Data.Foldable
import Data.Traversable

import TRS.Types
import TRS.GTerms

----------
-- * Rules
----------
data RuleG a = a :-> a

type Rule t (s :: * -> *) = RuleG (t s)
type RuleS s        = Rule TermStatic   s
type RuleI r s      = Rule (GT r)       s
type Rule_ mode r s = Rule (GT_ mode r) s

infix 1 :->

instance (Eq (RuleG a),Ord a) => Ord (RuleG a) where
  compare (l1 :-> r1) (l2 :-> r2) = case compare l1 l2 of
                                      EQ -> compare r1 r2
                                      x  -> x

instance Traversable RuleG where
  traverse f (l :-> r) = (:->) <$> f l <*> f r

instance Foldable RuleG where
  foldMap = foldMapDefault

instance Functor RuleG where
  fmap = fmapDefault

--swap :: Rule r s -> Rule r s
swap (lhs:->rhs) = rhs:->lhs


instance Show (a) => Show (RuleG (a)) where
    show (a:->b) = show a ++ " -> " ++ show b
