{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}

module TRS.Test.TermRef where
import Control.Applicative
import Control.Exception (assert)
import Control.Monad hiding (mapM, sequence )
import Data.Traversable
import Text.PrettyPrint
import Data.Char (isAlpha)
import Data.Foldable
import Prelude hiding ( all, maximum, minimum, any, mapM_,mapM, foldr, foldl
                      , sequence, concat, concatMap )
import TypePrelude

import TRS.Term
import TRS.Types
import TRS.Utils

newtype Ref a = Ref a deriving (Ord, Eq)
instance Functor Ref where fmap f (Ref t) = Ref (f t)
instance Foldable Ref where foldMap = foldMapDefault
instance Traversable Ref where traverse f (Ref t) = Ref <$> f t

ref :: (Ref :<: f) => Term f -> Term f
ref t | Just (Ref t) <- match t = t
      | otherwise               = inject $ Ref t

instance HashConsed (Var :+: Ref)

instance (Show a) => Show (Ref a) where
  showsPrec p (Ref s)  = ('{' :) . showsPrec p s . ('}' :)

instance Ppr Ref where pprF (Ref r) = braces r
instance (Ref :<: g, MatchShapeable g g) => MatchShape Ref Ref g g where matchShapeF (Ref r) (Ref s) = matchShape r s

instance HashTerm (Ref) where hashF (Ref t) = t
--instance HashConsed (Ref :+: Basic) where ht = newHt
--instance HashConsed (Var :+: Ref) where ht = newHt

class (f :<: g, HashConsed g) => StripRefs f g where stripRefsF :: f(Term g) -> Term g
instance (T i :<: g, HashConsed g) => StripRefs (T i) g where stripRefsF (T s tt) = term s tt
instance (Var :<: g, HashConsed g) => StripRefs Var   g where stripRefsF (Var t i)= var' t i
instance (Ref :<: g, HashConsed g) => StripRefs Ref   g where stripRefsF (Ref t)  = t

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