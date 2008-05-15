{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fglasgow-exts -fno-mono-pat-binds -fallow-undecidable-instances #-}
{-# OPTIONS_GHC -fallow-overlapping-instances #-}

module Test.TermRef where
import Control.Applicative
import Control.Exception (assert)
import Control.Monad hiding (mapM, sequence )
import Data.AlaCarte
import Data.Traversable
import Text.PrettyPrint
import Data.Char (isAlpha)
import Data.Foldable
import Prelude hiding ( all, maximum, minimum, any, mapM_,mapM, foldr, foldl
                      , sequence, concat, concatMap )
import GHC.Exts (unsafeCoerce#)
import TypePrelude

import TRS.Types
import TRS.Utils

newtype Ref a = Ref a deriving (Ord, Eq)
instance Functor Ref where fmap f (Ref t) = Ref (f t)
instance Foldable Ref where foldMap = foldMapDefault
instance Traversable Ref where traverse f (Ref t) = Ref <$> f t

ref :: (Ref :<: f) => Expr f -> Expr f
ref t | Just (Ref t) <- match t = t
      | otherwise               = inject $ Ref t

instance (Show a) => Show (Ref a) where
  showsPrec p (Ref s)  = ('{' :) . showsPrec p s . ('}' :)

instance Ppr Ref where pprF (Ref r) = braces r
instance (Ref :<: g, MatchShape g g) => MatchShape Ref g where matchShapeF (Ref r) (Ref s) = matchShape r s


class (Functor g, Functor f, f :<: g) => StripRefs f g where stripRefsF :: f(Term g) -> Term g
instance (T :<: g)   => StripRefs T   g where stripRefsF (T s tt) = term s tt
instance (Var :<: g) => StripRefs Var g where stripRefsF (Var t)  = var t
instance (Ref :<: g) => StripRefs Ref g where stripRefsF (Ref t)  = t

instance (StripRefs a (a :+: b), StripRefs b (a :+: b)) => StripRefs (a :+: b) (a :+: b) where
    stripRefsF (Inl x) = stripRefsF x
    stripRefsF (Inr y) = stripRefsF y

stripRefs :: StripRefs f f => Term f -> Term f
stripRefs = foldTerm stripRefsF

------------------------------------

--example :: (Var :<: f, Ref :<: f) => Term f
example :: Term (Var :+: Ref)
example = let x = var 0 in ref x

--example1 :: (Var :<: f) => Term f
example1 = stripRefs example

exPpr = ppr example