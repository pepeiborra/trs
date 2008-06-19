{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module TRS.Rules where

import Control.Applicative
import Control.Monad
import Data.AlaCarte
import Data.Foldable
import Data.Maybe
import Data.Traversable

import TRS.Types
----------
-- * Rules
----------
data RuleG a = a :-> a deriving Eq

type Rule f = RuleG (Term f)

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
swapRule :: RuleG t -> RuleG t
swapRule (lhs:->rhs) = rhs:->lhs

isConstructor :: (MatchShape s s, Var :<: s) => [RuleG (Expr s)] -> Term s -> Bool
isConstructor rules t
  | isVar t   = True
  | otherwise = null$ [ () | lhs:->_ <- rules
                           , isJust $ matchShape lhs t]

isDefined :: (Var :<: s, MatchShape s s) => [RuleG (Expr s)] -> Term s -> Bool
isDefined rules = not . isConstructor rules

instance Show (a) => Show (RuleG (a)) where
    show (a:->b) = show a ++ " -> " ++ show b
