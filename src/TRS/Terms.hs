{-# OPTIONS_GHC -fglasgow-exts -fno-mono-pat-binds -fallow-undecidable-instances #-}
{-# OPTIONS_GHC -fallow-overlapping-instances #-}
{-# OPTIONS_GHC  -funbox-strict-fields#-}
{-# OPTIONS_GHC  -fignore-breakpoints #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  TRS.Terms
-- Copyright   :  (c) Pepe Iborra 2006-2007
--                (c) Universidad Politécnica de Valencia 2006-2007
-- License     :  BSD-style (see LICENSE)
--
-- Maintainer  :  pepeiborra@gmail.org
-- Stability   :  experimental
-- Portability :  portable
--
-- Datatype for Terms, used for testing
-----------------------------------------------------------------------------

module TRS.Terms where
import Control.Applicative
import Control.Exception (assert)
import Control.Monad hiding (mapM, sequence )
import Data.Traversable
import Text.PrettyPrint
import Data.Char (isAlpha)
import Data.Foldable
import Prelude hiding ( all, maximum, minimum, any, mapM_,mapM, foldr, foldl
                      , sequence, concat, concatMap )
import GHC.Exts (unsafeCoerce#)

import TRS.Rules
import TRS.Types
import TRS.Utils
import TRS.Term

type RuleS s        = Rule TermStatic  s

-- -------------------------------------------
-- * Static Terms
-- --------------------------------------------
-- | The datatype of static terms, terms with no mutable vars
--   A generic term is converted to a static term with @zonkTerm@
--   and the other way around with @instTerm@
data TermStatic_ i s = Term (s (TermStatic_ i s)) | Var i
type TermStatic s = TermStatic_ Int s
type BasicTerm = TermStatic BasicShape
type BasicRule = Rule TermStatic BasicShape

instance (Eq i, TermShape s) => Eq (TermStatic_ i s) where
  Var i  == Var j  = i == j
  Term s == Term t | Just pairs <- matchTerm s t
                   = all (uncurry (==)) pairs
  _      == _      = False 

liftS f (Term t) = Term (f t)
liftS2 (*) (Term t) (Term v) = Term (t*v)

isTermStatic :: TermStatic s -> TermStatic s
isTermStatic = id

instance (Integral i, Show (s(TermStatic_ i s)), Show i) => Show (TermStatic_ i s) where
  showsPrec p (Term s) = showsPrec p s
  showsPrec p (Var i)  = showsVar p i
{-
instance (Show (s (TermStatic s))) => Show (TermStatic s) where
    showsPrec p (Term s) = showsPrec p s
    showsPrec p (Var  i) = showsVar p i 
-}
instance (Eq (TermStatic s), Ord (s(TermStatic s))) => Ord (TermStatic s) where
  compare (Term s) (Term t) = compare s t
  compare Term{} _          = GT
  compare _ Term{}          = LT
  compare (Var i) (Var j)   = compare i j

-- ---------------------------------------
-- TermStatic Term structure
-- ---------------------------------------
instance (TermShape s) => Term (TermStatic_ Int) s user where
  isVar Var{} = True 
  isVar _     = False
  mkVar       = Var 
  varId(Var i)= Just i
  varId _     = Nothing
  contents (Term tt) = Just tt
  contents _         = Nothing
  build              = Term 
