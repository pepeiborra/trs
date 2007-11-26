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
import qualified TRS.Term as Class
import qualified TRS.Core as Core
import TRS.Core ( mutableTerm, mutableTermG, generalize, generalizeG
                , noMVars, runL)


term = (s.) . T
term1 f t       = s$ T f [t]
term2 f t t'    = s$ T f [t,t']
term3 f t t' t''= s$ T f [t,t',t'']

var  = Var 
constant f = s (T f [])

-- ---------------------------------------
-- TermStatic Term structure
-- ---------------------------------------
instance (TermShape s, Traversable s) => Class.Term (TermStatic_ Int) s where
  Var i  `synEq` Var j  = i == j
  Term s `synEq` Term t | Just pairs <- matchTerm s t
                        = all (uncurry synEq) pairs
  _      `synEq` _      = False 
  isVar Var{} = True 
  isVar _     = False
  mkVar       = Var 
  varId(Var i)= Just i
  varId _     = Nothing
  subTerms (Term tt) = toList tt
  subTerms _         = []
  fromSubTerms (Term t) tt = Term $ modifySpine t tt
  fromSubTerms t _     = t
  mkGTM mkVar (Term t) = S `liftM` (mkGTM mkVar `mapM` t)
  mkGTM mkVar        x = mkVar x
  fromGTM mkVar (S y)  = Term `liftM` (fromGTM mkVar `mapM` y)
  fromGTM mkVar var    = mkVar var

--instance TermShape s => Eq (TermStatic s) where
instance (Class.Term t s, TermShape s) => Eq (t s) where
  t1 == t2 = runST (do
   [t1',t2'] <- mapM (mutableTerm >=> generalize) [t1,t2]
   return (t1' `synEq` t2'))

instance (Class.Term t s, TermShape s) => Eq (RuleG (t s)) where
  s1 == s2 = runST (do
   [l1:->r1,l2:->r2] <- mapM (mutableTermStatic >=> generalizeG) [s1,s2]
   return (l1 `synEq` l2 && r1 `synEq` r2))
    where
      mutableTermStatic :: forall s r. (Class.Term t s, TermShape s) => RuleG (t s) -> ST r (RuleI r s)
      mutableTermStatic = mutableTermG
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
ucT t = uc t :: GTE r BasicShape
--ucR r = uc r :: Rule BasicShape

