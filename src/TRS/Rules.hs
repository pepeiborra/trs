{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances, UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolymorphicComponents #-}

module TRS.Rules where

import Control.Parallel.Strategies
import Control.Applicative
import Control.Monad
import Data.Foldable
import Data.Maybe
import Data.Traversable

import TRS.Types
----------
-- * Rules
----------
data RuleG a = !a :-> !a deriving Eq

lhs,rhs :: forall t. RuleG t -> t
lhs (l :-> _) = l
rhs (_ :-> r) = r

type Rule f = RuleG (Term f)

infix 1 :->

-- Sort first on lhs, then on rhs
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

instance SizeF f => Size (Rule f) where size = Data.Foldable.sum . fmap size

--swap :: Rule r s -> Rule r s
swapRule :: RuleG t -> RuleG t
swapRule (lhs:->rhs) = rhs:->lhs

instance Show (a) => Show (RuleG (a)) where
    show (a:->b) = show a ++ " -> " ++ show b

instance NFData (f(Term f)) => NFData (Rule f) where rnf (l :-> r) = rnf l `seq` rnf r `seq` ()
