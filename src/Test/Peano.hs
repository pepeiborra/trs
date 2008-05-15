{-# OPTIONS_GHC -fallow-undecidable-instances #-}
{-# OPTIONS_GHC -fallow-overlapping-instances #-}
{-# OPTIONS_GHC -fglasgow-exts #-}

module Test.Peano where

import TRS.Types
import TRS.Unification
import Test.TermRef
import TRS.Rewriting
import TRS.Term
import TRS.Substitutions

import Control.Applicative
import Control.Monad hiding ( sequence, mapM )
import qualified Data.AlaCarte as Carte
import Data.AlaCarte hiding ( match )
import Data.Foldable
import Data.List
import Data.Maybe
import Data.Traversable
import Text.PrettyPrint
import Test.QuickCheck
import Prelude hiding ( sequence, mapM )

------------------------
-- The Terms dataType
------------------------
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
{-
instance Enum (Peano f) where
   succ(x) = s(x)
--   pred(s(Succ x)) = x
   toEnum n = iterate succ z !! n
-}

-- helper constructors

(+:)    :: (Peano :<: f) => Term f -> Term f -> Term f
x +: y   = inject (x :+ y)
x &+: y  = ref x +: y
x +:& y  = x +: ref y
x &+:& y = ref x +: ref y

s :: (Peano :<: f) => Term f -> Term f
s x      = inject (Succ x)
z :: (Peano :<: f) => Term f
z        = inject Zero

(*:)   :: (Peano :<: f) => Term f -> Term f -> Term f
x *: y = inject (x :* y)
fact x = inject . Fact x
p x    = inject (Pred x)

isSum t | Just (x :+ y) <- Carte.match t = True
        | otherwise                = False

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

instance (Peano :<: g) => MatchShape Peano g where
    matchShapeF Zero Zero = Just []
    matchShapeF (Succ x) (Succ y) = Just [(x,y)]
    matchShapeF (a :+ b) (c :+ d) = Just [(a,c),(b,d)] 
    matchShapeF (a :* b) (c :* d) = Just [(a,c),(b,d)] 
    matchShapeF (Fact a b) (Fact c d) = Just [(a,c),(b,d)]
    matchShapeF (Pred a) (Pred b) = Just [(a,b)]
    matchShapeF x y = Nothing

instance Ppr Peano where
    pprF Zero = int 0
    pprF (Succ a) = text "s" <+> a
    pprF (a :+ b) = parens (a <+> text "+" <+> b)
    pprF (a :* b) = parens (a <+> text "*" <+> b)
    pprF (Fact a b) = parens(text "Fact" <+> a <+> b)
    pprF (Pred a) = text "p" <+> a

instance Children Peano where
    childrenF (a :+ b) = a ++ b
    childrenF (a :* b) = a ++ b
    childrenF (Succ x) = x
    childrenF (Pred x) = x
    childrenF (Fact a b) = a ++ b
    childrenF _ = []

instance (Var :<: g, Peano :<: g) => Unify Peano Var g where unifyF t v = unifyF v t
instance (Peano :<: g, Functor h) => Unify Peano h g where unifyF t v = mzero


instance (Peano :<: g, Var :<: g) => Match Peano Peano g where matchF = matchFdefault
instance (Peano :<: g, f :<: g) => Match Peano f g where matchF _ _ = Nothing

instance (Eq (Term f), Ppr f, Peano :<: f) => Num (Term f) where
  fromInteger i = iterate s z !! (fromIntegral i)
  (+) = (+:)
  (*) = (*:)


{-
p (Succ _) = "succ"
p (_ :+ _) = "+"
p Zero     = "0"
-}

{-
instance Arbitrary (PeanoT) where
    arbitrary = sized$ arbitraryPeano (map Var [0..2]) False
-- instance Shrink PeanoT where
    shrink (Term(a :+ b)) = a : b : [a' +: b' | a' <- shrink a, b' <- shrink b]
    shrink (Term(Succ a)) = a : shrink a
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
                else [(2,liftM wrapRef (arbitraryPeano vars refs size))])

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
-}