module Test.Peano where

import TRS hiding (s)
import qualified TRS
import TRS.GTerms (GTE)

import Control.Applicative
import Control.Monad
import Data.Foldable
import Data.Traversable
import Test.QuickCheck
------------------------
-- The Terms dataType
------------------------
type PeanoT = TermStatic Peano
type PeanoM r = GTE r Peano 

data Peano a = a :+ a
             | Succ a
             | Pred a
             | Zero
             | a :* a
             | Fact a a
    deriving (Eq, Ord)

prec_succ = 3
prec_pred = prec_succ
prec_mul  = 2
prec_plus = 1
prec_app  = 9

instance Show x => Show (Peano x) where
  showsPrec p (Succ x) = showParen (p>prec_succ) $ 
                         ("s " ++ ) . showsPrec (succ prec_succ) x
  showsPrec p Zero     = ('0' : )
  showsPrec p (a :+ b) = showParen (p>prec_plus) 
                       $ showsPrec (succ prec_plus) a 
                       . (" + " ++) 
                       . showsPrec (succ prec_plus) b
  showsPrec p (a :* b) = showParen (p>prec_mul)
                       $ showsPrec (succ prec_mul) a 
                       . (" * " ++)
                       . showsPrec (succ prec_mul) b
  showsPrec p (Fact a b) = showParen (p>prec_app)
                         $ ("Fact " ++)
                         . showsPrec (succ prec_app) a
                         . (" " ++)
                         . showsPrec (succ prec_app) b
  showsPrec p (Pred a) = showParen (p>prec_pred) 
                       $ ("p " ++) . showsPrec (succ prec_pred) a

instance Enum (PeanoT) where
   succ(x) = s(x)
--   pred(s(Succ x)) = x
   toEnum n = iterate succ z !! n

-- helper constructors
x +: y = TRS.s (x :+ y)
s = TRS.s . Succ
z = TRS.s Zero
x *: y = TRS.s (x :* y)
fact x = TRS.s . Fact x
p = TRS.s . Pred

isSum (Term(x :+ y)) = True
isSum _ = False

instance Traversable Peano where
    traverse f Zero = pure Zero
    traverse f (Succ a) = Succ <$> f a
    traverse f (a :+ b) = (:+) <$> f a <*> f b
    traverse f (a :* b) = (:*) <$> f a <*> f b
    traverse f (Fact a b) = Fact <$> f a <*> f b
    traverse f (Pred a) = Pred <$> f a

instance Functor Peano where
    fmap = fmapDefault
instance Foldable Peano where
    foldMap = foldMapDefault

instance TermShape Peano where 
    matchTerm Zero Zero = Just []
    matchTerm (Succ x) (Succ y) = Just [(x,y)]
    matchTerm (a :+ b) (c :+ d) = Just [(a,c),(b,d)] 
    matchTerm (a :* b) (c :* d) = Just [(a,c),(b,d)] 
    matchTerm (Fact a b) (Fact c d) = Just [(a,c),(b,d)]
    matchTerm (Pred a) (Pred b) = Just [(a,b)]
    matchTerm x y = Nothing


instance Num (TermStatic Peano) where
  fromInteger i = iterate s z !! (fromIntegral i)
  (+) = (+:)
  (*) = (*:)

{-
p (Succ _) = "succ"
p (_ :+ _) = "+"
p Zero     = "0"
-}

instance Arbitrary (PeanoT) where
    arbitrary = sized$ arbitraryPeano (map Var [0..2])
-- instance Shrink PeanoT where
    shrink (Term(a :+ b)) = a : b : [a' +: b' | a' <- shrink a, b' <- shrink b]
    shrink (Term(Succ a)) = [a]
    shrink (Term(Pred a)) = [a]
    shrink (Term(a :* b)) = a : b : [a' *: b' | a' <- shrink a, b' <- shrink b]
    shrink (Term(Fact a b)) = a : b : [fact a' b' | a' <- shrink a, b' <- shrink b]
    shrink x = []

instance CoArbitrary PeanoT where
    coarbitrary (Var i)  = variant 0 . coarbitrary i
    coarbitrary (Term f) = variant 1 . coarbitrary (toList f)


arbitraryPeano [] 0   = return z
arbitraryPeano vars 0 = frequency [(1,return z), (1, elements vars)]
arbitraryPeano vars size | size2 <- size `div` 2 =
  frequency [ (2,liftM2 (+:) (arbitraryPeano vars size2) (arbitraryPeano vars size2))
            , (2,liftM s (arbitraryPeano vars size))]


instance Arbitrary (RuleS Peano) where
  arbitrary = arbitraryRule
  shrink (a :-> b) = (:->) <$> (shrink a) <*> (shrink b)

--arbitraryRule :: (Arbitrary (GT_ eq r s), Eq (GT_ eq r s))
arbitraryRule = do
  l <- arbitrary
  r <- sized$ arbitraryPeano (vars l)
  return (l:->r)
