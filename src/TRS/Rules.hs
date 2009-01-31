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

#ifdef HOOD
import Debug.Observe
#endif //HOOD

----------
-- * Rules
----------
data RuleF a = !a :-> !a deriving Eq

lhs,rhs :: forall t. RuleF t -> t
lhs (l :-> _) = l
rhs (_ :-> r) = r

type Rule f = RuleF (Term f)

infix 1 :->

-- Sort first on lhs, then on rhs
instance (Eq (RuleF a),Ord a) => Ord (RuleF a) where
  compare (l1 :-> r1) (l2 :-> r2) = case compare l1 l2 of
                                      EQ -> compare r1 r2
                                      x  -> x

instance Traversable RuleF where
  traverse f (l :-> r) = (:->) <$> f l <*> f r

instance Foldable RuleF where
  foldMap = foldMapDefault

instance Functor RuleF where
  fmap = fmapDefault

instance (Functor f, Foldable f) => Size (Rule f) where size = Data.Foldable.sum . fmap size

--swap :: Rule r s -> Rule r s
swapRule :: RuleF t -> RuleF t
swapRule (lhs:->rhs) = rhs:->lhs

instance Show (a) => Show (RuleF (a)) where
    show (a:->b) = show a ++ " -> " ++ show b

instance NFData (f(Term f)) => NFData (Rule f) where rnf (l :-> r) = rnf l `seq` rnf r `seq` ()

#ifdef HOOD
instance Show a => Observable (RuleF a) where observer = observeBase
#endif //HOOD
