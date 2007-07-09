{-# OPTIONS_GHC -fglasgow-exts -fno-mono-pat-binds -fallow-undecidable-instances #-}
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

import TRS.Term  hiding (Term)
import qualified TRS.Term as Class
import TRS.Types
import qualified TRS.Types (Term)
import TRS.Utils
import qualified TRS.Core as Core
import TRS.Core (col, mutableTerm, mutableTermG, generalize_, generalizeG_
                , noMVars, runL)


term = (s.) . T
term1 f t       = s$ T f [t]
term2 f t t'    = s$ T f [t,t']
term3 f t t' t''= s$ T f [t,t',t'']

var  = Var 
constant f = s (T f [])

instance Ord a => Ord (BasicShape a) where
    (T s1 tt1) `compare` (T s2 tt2) = 
        case compare s1 s2 of
          EQ -> compare tt1 tt2
          x  -> x

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
  varId(Var i)= i
  subTerms (Term tt) = toList tt
  subTerms _         = []
  fromSubTerms (Term t) tt = Term $ modifySpine t tt
  fromSubTerms t _     = t
  mkGTM mkVar (Term t) = S `liftM` (mkGTM mkVar `mapM` t)
  mkGTM mkVar        x = mkVar x
  fromGTM mkVar (S y)  = Term `liftM` (fromGTM mkVar `mapM` y)
  fromGTM mkVar var    = mkVar var

instance TermShape s => Eq (TermStatic s) where
  t1 == t2 = runST (do
   [t1',t2'] <- mapM (mutableTerm >=> generalize_) [t1,t2]
   return (t1' `synEq` t2'))

instance TermShape s => Eq (Rule s) where
  s1 == s2 = runST (do
   [l1:->r1,l2:->r2] <- mapM (mutableTermG >=> generalizeG_) [s1,s2]
   return (l1 `synEq` l2 && r1 `synEq` r2))
   
---------------------------------
-- Auxiliary code
---------------------------------
{-
instance Eq (Term a) where 
  t1 == t2 = (S t1) `equal` (S t2)
-}

instance Show a => Show (BasicShape a) where 
    show (T s [])   = s
    show (T s [x,y]) | not (any isAlpha s)
                     = show x ++ ' ':s ++ ' ':show y
    show (T s tt)   = render (text s <> parens( hcat$ punctuate comma (map (text.show) tt)))
--    showList []     = ""
--    showList (t:tt) = show t ++ ' ' : showList tt
 
--sh = text . show

class Outputable a where
  ppr :: a -> Doc

---------------------------------------------
-- Other stuff for using in the ghci debugger
---------------------------------------------

uc = unsafeCoerce#
ucT t = uc t :: GTE r BasicShape
--ucR r = uc r :: Rule BasicShape

