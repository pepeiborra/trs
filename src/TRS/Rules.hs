{-# OPTIONS_GHC -fallow-undecidable-instances #-}
module TRS.Rules where

import Control.Applicative
import Control.Monad
import Data.Foldable
import Data.Maybe
import Data.Traversable

import TRS.Types
import TRS.Term
import {-#SOURCE#-} TRS.Core hiding (semEq)
----------
-- * Rules
----------
data RuleG a = a :-> a

type Rule t (s :: * -> *) = RuleG (t s)

infix 1 :->

instance (Term t s user, TermShape s) => Eq (RuleG (t s)) where
  (l1:->r1) == (l2:->r2) = (l1 `semEq` l2) && (r1 `semEq` r2)

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


isConstructor rules t 
  | isVar t   = True
  | otherwise = not $ null$ do
                  lhs:->rhs <- rules
                  guard (isJust $ matchTerm lhs =<< contents t)
                  return ()

instance Show (a) => Show (RuleG (a)) where
    show (a:->b) = show a ++ " -> " ++ show b
