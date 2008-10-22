{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, StandaloneDeriving #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE PatternSignatures #-}

module TRS.Test.Instances where

import Control.Applicative
import Control.Monad
import Test.QuickCheck (Arbitrary(..), quickCheck, oneof, sized, resize, frequency, Gen)
import Test.QuickCheck.Test (quickCheckResult, isSuccess)
import Test.SmallCheck hiding (two, three, four, test)
import qualified Test.SmallCheck     as Small
import qualified Test.LazySmallCheck as LS
import Test.LazySmallCheck ( (*&*) )

import TRS
import TRS.Utils
import TRS.Test.Peano

isValidTRS = all isValidRule
isValidRule (l:->r) = (not.isVar) l && (vars r `subSetOf` vars l) && termSize l - termSize r > 5
    where subSetOf s1 s2 = ( `elem` s2) `all` s1

isValidRule' (l:->r) = LS.lift (not$ isVar l) *&*
                       LS.lift (vars r `subSetOf` vars l) *&*
                       LS.lift (termSize l - termSize r > 5)
    where subSetOf s1 s2 = ( `elem` s2) `all` s1

--QuickCheck
instance Applicative Gen where
    (<*>) = ap
    pure  = return
instance Alternative Gen where
    a <|> b = oneof [a,b]
    empty   = oneof []

instance Arbitrary (f(Term f)) => Arbitrary (Term f) where
    arbitrary = In <$> arbitrary

instance Arbitrary (Hole a) where arbitrary = Hole <$> arbitrary
instance Arbitrary (Var a)  where arbitrary = Var Nothing <$> oneof [return 0, return 1, return 2]

instance Arbitrary a => Arbitrary (T String a) where
    arbitrary = sized $ \size ->
      let half m = resize (size `div` 2) m in
      oneof [ (`T` []) <$> oneof [return "a", return "b"]
            , arbitrary >>= \t1  ->
              (`T` [t1]) <$> oneof [return "f1", return "g1"]
            , arbitrary >>= \t1 -> arbitrary >>= \t2 ->
              (`T` [t1,t2]) <$> oneof [return "f2", return "g2"] ]


instance Arbitrary a => Arbitrary (Peano a) where
    arbitrary = sized $ \size ->
      let half m = resize (size `div` 2) m in
      frequency
        [ (2, liftM2 (:+) (half arbitrary) (half arbitrary))
        , (2, return Zero)
        , (4, Succ <$> arbitrary)]

-- SmallCheck

fromNatural :: Natural -> Int
fromNatural (N i) = fromInteger i

fromBool :: Bool -> Int
fromBool = fromEnum

instance Serial (Var f)  where series = cons1 (Var Nothing . fromBool)
instance Serial (Hole f) where series = cons1 Hole
instance Serial a => Serial (T String a) where series = cons2 T
instance Serial f => Serial (Peano f)    where series = cons2 (:+) \/ cons1 Succ \/ cons0 Zero
instance Serial (f(Term f)) => Serial (Term f)                where series = cons1 In
instance (Serial (f a), Serial (g a)) => Serial ((f :+: g) a) where series = cons1 Inl \/ cons1 Inr
deriving instance Serial (Term f) => Serial (EqModulo f)

-- Lazy SmallCheck

instance LS.Serial (Var f)  where series = LS.cons (Var Nothing) LS.>< (LS.cons abs LS.>< LS.series)
instance LS.Serial (Hole f) where series = LS.cons1 Hole
instance LS.Serial a => LS.Serial (T String a) where series = LS.cons2 T
instance LS.Serial f => LS.Serial (Peano f)    where series = LS.cons2 (:+) LS.\/ LS.cons1 Succ LS.\/ LS.cons0 Zero
instance LS.Serial (f(Term f)) => LS.Serial (Term f)                   where series = LS.cons1 In
instance (LS.Serial (f a), LS.Serial (g a)) => LS.Serial ((f :+: g) a) where series = LS.cons1 Inl LS.\/ LS.cons1 Inr
deriving instance LS.Serial (Term f) => LS.Serial (EqModulo f)

--Constructor Term smallcheck instances


newtype ConstructorPeano f = ConstructorPeano (Peano f) deriving (Functor, Ppr)
type ConstructorPeanoT = Var :+: ConstructorPeano

class Functor f => ConstructorPeanoClass f       where fromConstructorPeano :: f (Term PeanoT) -> Term PeanoT
instance ConstructorPeanoClass ConstructorPeano  where fromConstructorPeano (ConstructorPeano t) = inject t
instance ConstructorPeanoClass Var               where fromConstructorPeano v = inject v
instance (ConstructorPeanoClass a, ConstructorPeanoClass b) => ConstructorPeanoClass (a :+: b) where
    fromConstructorPeano (Inl l) = fromConstructorPeano l
    fromConstructorPeano (Inr r) = fromConstructorPeano r

instance Serial f => Serial (ConstructorPeano f) where series = map ConstructorPeano . (cons1 Succ \/ cons0 Zero)


instance LS.Serial f => LS.Serial (ConstructorPeano f) where
    series = my (ConstructorPeano <$> (Succ <$> myseries
                                      <|> pure Zero))


-- Instances for generating terminating TRSs

{- My Serial instances are now quite useful.
  Initially they would generate interpretations with not rnf rhs's
  producing non terminating TRSs and then everything falls apart.

  A solution would be to allow only constructor terms in rhs's.
  But this is not nearly enough to prevent non terminating equations !! e.g. s0 -> ss0 or s0 -> s0
  Solution: use the 'depth' parameter of smallcheck to enforce that the rhs has smaller depth
            should be piece of cake!
  Hmm well..yes. After playing with the sizes we can avoid nonterminating equations with minus 3 in the rhs.
-}

instance Serial (Term PeanoT) => Serial (Rule PeanoT) where
    series size = map f ( filter (not.isVar) (series size) `zip` series (size - 3))
           where f (lhs :: Term PeanoT, rhs :: Term ConstructorPeanoT) = lhs :-> rhs'
                                   where rhs' = foldTerm fromConstructorPeano rhs

instance Serial (Term PeanoT) => Serial (Rule PeanoTH) where
    series = fmap3 noHoles series

{- With Lazy smallcheck Series it is the same story.
   Here however the series are not observable (or I didn't find a way to see the
   terms generated). After all Lazy smallcheck is supposed to be driven by conditions.
   The problem is of course that termination cannot be expressed as a condition, since it is
   not decidable itself. We should have a notion of size and reason our conditions with it.
   But I feel too tired now to take care of that :S
-}
instance LS.Serial (Term PeanoT) => LS.Serial (Rule PeanoT) where
   series = my rule where
       rule = (:->) <$> myseries <*> My rhs
       rhs size = LS.series (size - 4)


instance LS.Serial (Term PeanoT) => LS.Serial (Rule PeanoTH) where
    series = my (fmap2 noHoles myseries)

noHoles :: Term PeanoT -> Term PeanoTH
noHoles = reinject


-- MySeries Applicative Functor rendition of LS.Series

newtype MySeries a = My{my::LS.Series a}

myseries = My LS.series

instance Functor MySeries where
  fmap f s = My (LS.cons f LS.>< my s)
instance Applicative MySeries where
  pure = My . LS.cons
  f <*> s = My (my f LS.>< my s)
instance Alternative MySeries where
  a <|> b = My (my a LS.\/ my b)
  empty   = My LS.empty