{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}

module TRS.Bottom where

import Control.Applicative
import Data.Foldable (Foldable(..))
import Data.HashTable (hashString)
import Data.Monoid
import Data.Traversable
import Text.PrettyPrint (text)

import TRS.Types
import TRS.Term

type BBasic = Var :+: T String :+: Bottom
instance HashConsed BBasic

data Bottom a = Bottom deriving (Show, Eq, Ord)
instance Functor Bottom  where fmap _ Bottom = Bottom
instance Foldable Bottom where foldMap _ Bottom = mempty
instance Traversable Bottom where traverse _ Bottom = pure Bottom
instance Ppr Bottom      where pprF Bottom  = text "_|_"
instance Zip Bottom      where fzipWith f _ = fail "fzipWith: Bottoms don't zip"
instance HashTerm Bottom where hashF Bottom = hashString "Bottom"

bottom :: (Bottom :<: f) => Term f
bottom = inject Bottom