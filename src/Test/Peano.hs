{-# OPTIONS_GHC -fallow-undecidable-instances #-}
{-# OPTIONS_GHC -fallow-overlapping-instances #-}

module Test.Peano where

import TRS
import Test.TermRef

import Control.Applicative
import Control.Monad hiding ( sequence )
import Data.Foldable
import Data.List
import Data.Maybe
import Data.Traversable
import Test.QuickCheck
import Prelude hiding ( sequence ) 
------------------------
-- The Terms dataType
------------------------
type PeanoT = TermRef Peano
newtype PeanoV = Refs PeanoT 
    deriving (Show, Eq)

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
x +: y   = t (x     :+ y)
x &+: y  = t (Ref x :+ y)
x +:& y  = t (x     :+ Ref y)
x &+:& y = t (Ref x :+ Ref y)
s = t . Succ
z = t Zero
x *: y = t (x :* y)
fact x = t . Fact x
p = t . Pred

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


instance Num (TermRef Peano) where
  fromInteger i = iterate s z !! (fromIntegral i)
  (+) = (+:)
  (*) = (*:)

{-
p (Succ _) = "succ"
p (_ :+ _) = "+"
p Zero     = "0"
-}

instance Arbitrary (PeanoT) where
    arbitrary = sized$ arbitraryPeano (map Var [0..2]) False
-- instance Shrink PeanoT where
    shrink (Term(a :+ b)) = a : b : [a' +: b' | a' <- shrink a, b' <- shrink b]
    shrink (Term(Succ a)) = [a]
    shrink (Term(Pred a)) = [a]
    shrink (Term(a :* b)) = a : b : [a' *: b' | a' <- shrink a, b' <- shrink b]
    shrink (Term(Fact a b)) = a : b : [fact a' b' | a' <- shrink a, b' <- shrink b]
    shrink (Ref t) = [t] ++ (Ref <$> shrink t)
    shrink x = []

instance Arbitrary PeanoV where
    arbitrary = Refs <$> sized (arbitraryPeano (map Var [0..2]) True)
    shrink (Refs t) = Refs <$> shrink t

instance CoArbitrary PeanoT where
    coarbitrary (Var i)  = variant 0 . coarbitrary i
    coarbitrary (Term f) = variant 1 . coarbitrary (toList f)
    coarbitrary (Ref  t) = variant 2 . coarbitrary t

arbitraryPeano [] _ 0   = return z
arbitraryPeano vars _ 0 = frequency [(1,return z), (1, elements vars)]
arbitraryPeano vars refs size | size2 <- size `div` 2 =
  frequency ([ (2,liftM2 (+:) (arbitraryPeano vars refs size2) 
                              (arbitraryPeano vars refs size2))
            , (4,liftM s (arbitraryPeano vars refs (pred size)))] ++
             if not refs 
                then []
                else [(2,liftM ref (arbitraryPeano vars refs size))])

instance Arbitrary (RuleS Peano) where
  arbitrary =  do
      l <- arbitrary
      r <- sized$ arbitraryPeano (vars l) False
      return (l:->r)
  shrink (a :-> b) = (:->) <$> (shrink a) <*> (shrink b)


instance Arbitrary (SubstM PeanoT) where
  arbitrary = do
      tt <- arbitrary
      return $ SubstM (Just <$> [ t | Refs t <- tt, not (isVar t)])
  shrink (SubstM tt) =  (SubstM . filter isJust <$> map shrink tt)
      where isVar Var{} = True
            isVar (Ref Var{}) = True
            isVar _ = False

--arbitraryRule :: (Arbitrary (GT_ eq r s), Eq (GT_ eq r s))
arbitraryRule refs = do
  l <- arbitrary
  r <- sized$ arbitraryPeano (vars l) refs
  return (l:->r)
