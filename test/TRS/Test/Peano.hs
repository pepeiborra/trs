{-# LANGUAGE UndecidableInstances, OverlappingInstances, FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE TypeOperators, TypeSynonymInstances #-}
module TRS.Test.Peano where

import TRS.Context
import TRS.Types
import TRS.Term
import TRS.Test.TermRef

import Control.Applicative
import qualified Data.AlaCarte as Carte
import Data.Foldable
import Data.HashTable
import Data.Traversable
import Text.PrettyPrint
import Prelude hiding ( sequence, mapM )

type PeanoT  = Var :+: Peano
type PeanoTH = Var :+: Peano :+: Hole
instance HashConsed PeanoT
instance HashConsed PeanoTH

------------------------
-- The Terms dataType
------------------------
data Peano a = a :+ a
             | Succ a
             | Pred a
             | Zero
             | a :* a
             | Fact a a
             | Fib a
    deriving (Eq, Ord)
{-
instance SignatureC [Rule PeanoTH] String where
    getSignature _ = Sig { constructorSymbols = fromList ["s", "0"]
                         , definedSymbols     = fromList ["+","*", "fact"
-}
prec_succ = 3
prec_pred = prec_succ
prec_mul  = 2
prec_plus = 1
prec_app  = 9

instance HashTerm Peano where
    hashF (Succ t) = hashString "Succ" + t
    hashF (x :+ y) = hashString "+:" + x + y
    hashF Zero     = hashString "Zero"
    hashF x = hashString (show x)

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
  showsPrec p (Fib x) = showParen (p>prec_succ) $ 
                         ("fib " ++ ) . showsPrec (succ prec_app) x

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
fib x  = inject (Fib x)

isSum t | Just (x :+ y) <- Carte.match t = True
        | otherwise                = False

instance Traversable Peano where
    traverse f Zero = pure Zero
    traverse f (Succ a) = Succ <$> f a
    traverse f (a :+ b) = (:+) <$> f a <*> f b
    traverse f (a :* b) = (:*) <$> f a <*> f b
    traverse f (Fact a b) = Fact <$> f a <*> f b
    traverse f (Pred a) = Pred <$> f a
    traverse f (Fib a)  = Fib  <$> f a

instance Functor Peano where
    fmap = fmapDefault
instance Foldable Peano where
    foldMap = foldMapDefault

instance MatchShape Peano where
    matchShapeF Zero Zero = Just []
    matchShapeF (Succ x) (Succ y) = Just [(x,y)]
    matchShapeF (a :+ b) (c :+ d) = Just [(a,c),(b,d)] 
    matchShapeF (a :* b) (c :* d) = Just [(a,c),(b,d)] 
    matchShapeF (Fact a b) (Fact c d) = Just [(a,c),(b,d)]
    matchShapeF (Pred a) (Pred b) = Just [(a,b)]
    matchShapeF (Fib a)  (Fib b)  = Just [(a,b)]
    matchShapeF x y = Nothing

instance Ppr Peano where
    pprF Zero = int 0
    pprF (Succ a) = text "s" <+> a
    pprF (a :+ b) = parens (a <+> text "+" <+> b)
    pprF (a :* b) = parens (a <+> text "*" <+> b)
    pprF (Fact a b) = parens(text "Fact" <+> a <+> b)
    pprF (Pred a) = text "p" <+> a
    pprF (Fib  a) = text "fib" <+> parens a

-- instance (Var :<: g, Peano :<: g) => Unify Peano Var g where unifyF t v = unifyF v t
--instance (Peano :<: g, Functor g) => Unify Peano Peano g where unifyF = unifyFdefault


-- instance (Peano :<: g, Var :<: g) => Match Peano Peano g where matchF = matchFdefault
-- instance (Peano :<: g, f :<: g) => Match Peano f g where matchF _x _y = Nothing

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
