{-# OPTIONS_GHC -fglasgow-exts -fno-mono-pat-binds -fallow-undecidable-instances #-}
{-# OPTIONS_GHC -fallow-overlapping-instances #-}
{-# OPTIONS_GHC  -funbox-strict-fields#-}

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

import TRS.GTerms
import TRS.Rules
import TRS.Types
import TRS.Utils
import TRS.Term

type RuleI user r s = Rule (GT user r) s
type RuleS s        = Rule TermStatic  s

-- -------------------------------------------
-- * Static Terms
-- --------------------------------------------
-- | The datatype of static terms, terms with no mutable vars
--   A generic term is converted to a static term with @zonkTerm@
--   and the other way around with @instTerm@
data TermStatic_ i s = Term (s (TermStatic_ i s)) | Var i
--  deriving (Show)
type TermStatic s = TermStatic_ Int s
type BasicTerm = TermStatic BasicShape


s :: s(TermStatic s) -> TermStatic s
s = Term

liftS f (Term t) = Term (f t)
liftS2 (*) (Term t) (Term v) = Term (t*v)

var  = Var 
constant f = s (T f [])
term = (s.) . T
term1 f t       = s$ T f [t]
term2 f t t'    = s$ T f [t,t']
term3 f t t' t''= s$ T f [t,t',t'']


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
  compare (Var i) (Var j)   = compare i j

-- ---------------------------------------
-- TermStatic Term structure
-- ---------------------------------------
instance (TermShape s) => Term (TermStatic_ Int) s user where
  Var i  `synEq` Var j  = i == j
  Term s `synEq` Term t | Just pairs <- matchTerm s t
                        = all (uncurry synEq) pairs
  _      `synEq` _      = False 
  isVar Var{} = True 
  isVar _     = False
  mkVar       = Var 
  varId(Var i)= Just i
  varId _     = Nothing
  subTerms (Term tt) = Just tt
  subTerms _         = Nothing
  build              = Term 


---------------------------------
-- Auxiliary code
---------------------------------
{-
instance Eq (Term a) where 
  t1 == t2 = (S t1) `equal` (S t2)
-}
 

---------------------------------------------
-- Other stuff for using in the ghci debugger
---------------------------------------------

uc = unsafeCoerce#
ucT t = uc t :: GTE user r BasicShape
--ucR r = uc r :: Rule BasicShape

