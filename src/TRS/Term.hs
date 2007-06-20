{-# OPTIONS_GHC -fglasgow-exts #-}
module TRS.Term where

import Control.Applicative
import Control.Monad (replicateM)
import Control.Monad.State (gets, modify, evalState)
import Data.Foldable (toList, Foldable)
import Data.Maybe (fromMaybe)
import Data.Traversable (Traversable, mapM)
import Prelude hiding (mapM)

import TRS.Terms hiding (Term)
import TRS.Types
import TRS.Utils

-- ---------------------------------------
-- * The class of terms
-- ----------------------------------------
class Term t where
        isVar        :: t -> Bool
        subTerms     :: t -> [t]
        fromSubTerms :: t -> [t] -> t
        synEq        :: t -> t -> Bool  -- |syntactic equality

instance (TermShape s, Traversable s) => Term (TermStatic s) where
        Var i  `synEq` Var j  = i == j
        Term s `synEq` Term t | Just pairs <- matchTerm s t
                              = all (uncurry synEq) pairs
        _      `synEq` _      = False 
        isVar Var{} = True 
        isVar _     = False
        subTerms (Term tt) = toList tt
        subTerms _  = []
        fromSubTerms (Term t) tt = Term $ modifySpine t tt
        fromSubTerms t _ = t
       
instance (TermShape s, Foldable s) => Term (GT_ eq s r) where
  {-# SPECIALIZE instance Term (GT_ eq BasicShape r) #-}
  isVar S{}      = False
  isVar _        = True
  subTerms (S x) = toList x
  subTerms _     = []
  synEq (MutVar r1) (MutVar r2) = r1 == r2 
  synEq (GenVar n) (GenVar m)   = m==n
  synEq (CtxVar n) (CtxVar m)   = m==n
  synEq (S x) (S y) | Just pairs <- matchTerm x y 
                    = all (uncurry synEq) pairs 
  synEq _ _ = False
  fromSubTerms (S t) tt = S $ modifySpine t tt
  fromSubTerms t _      = t
        
vars t | [] <- tt  = []
       | otherwise = filter isVar tt ++ concatMap vars tt
 where tt = subTerms t

collect :: Term t => (t -> Bool) -> t -> [t]
collect pred t = [t' | t' <- subTerms t, pred t']

-- | Do not confuse with substitution application. @replace@ makes no 
--   effort at avoiding variable capture
-- 
--   (you could deduce that from the type signature)
replace :: (Eq t, Term t) => [(t,t)] -> t -> t
replace subst t = t `fromSubTerms` [ t' `fromMaybe` lookup t' subst 
                                     | t'' <- subTerms t
                                     , let t' = replace subst t'']

noCVars, noGVars, noMVars :: (TermShape s, Foldable s) => GT_ eq s r -> Bool
noGVars = null . collect isGenVar
noMVars = null . collect isMutVar 
noCVars = null . collect isCtxVar 


mkVarsForTerm :: (TermShape s, Foldable s) => GT_ eq s r -> ST r (Subst_ eq s r)
mkVarsForTerm t | null vars_t = return emptyS
                | otherwise   = do
    newvars <- replicateM (topvar+1) fresh 
    return (Subst newvars)
   where vars_t = vars t
         topvar = maximum [ i | GenVar i <- vars_t ]
