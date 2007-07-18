{-# OPTIONS_GHC -fglasgow-exts #-}
module TRS.Term where

import Control.Applicative
import Control.Arrow (first, second)
import Control.Monad (replicateM, liftM, mplus)
import Control.Monad.State (gets, modify, evalState)
import Control.Monad.Identity (runIdentity)
import Data.List (nub, nubBy, elemIndex)
import Data.Foldable (toList, Foldable)
import Data.Maybe (fromMaybe, fromJust)
import Data.Traversable (Traversable, mapM)
import Prelude hiding (mapM)

import {-# SOURCE#-} TRS.Core (col, Prune)
import TRS.Types hiding (Term)
import TRS.Utils

-- ---------------------------------------
-- * The class of terms
-- ----------------------------------------
class TermShape s => Term t s where
        isVar        :: t s -> Bool
        mkVar        :: Int -> t s
        varId        :: t s -> Int
        subTerms     :: t s -> [t s]
        fromSubTerms :: t s -> [t s] -> t s
        synEq        :: t s -> t s -> Bool  -- |syntactic equality
        mkGT         :: (t s -> GT_ eq r s) -> t s -> GT_ eq r s
        mkGT mkVar t = runIdentity (mkGTM (return . mkVar) t)
        mkGTM        :: Monad m => (t s -> m(GT_ eq r s)) -> t s -> m(GT_ eq r s)
        fromGTM      :: Monad m => (GT_ eq r s -> m(t s)) -> GT_ eq r s -> m(t s)
        fromGT       :: (GT_ eq r s -> t s) -> GT_ eq r s -> t s
        fromGT mkV t = runIdentity (fromGTM (return . mkV) t) 

class Term t s => TRS t s m where
        rewrite      :: [Rule s] -> t s -> m(t s)
        unify        :: t s -> t s -> m(SubstM (t s))
        rewrite1     :: [Rule s] -> t s -> m(t s)
        narrow1      :: [Rule s] -> t s -> m(SubstM(t s), t s)

class Term t s => TRSN t s where
        narrow1'     :: [Rule s] -> t s -> [(SubstM(t s), t s)]
        narrowFull   :: [Rule s] -> t s -> [(SubstM(t s), t s)]
        narrowBasic  :: [Rule s] -> t s -> [(SubstM(t s), t s)]
        narrowFullBounded :: (t s -> Bool) -> [Rule s] -> t s 
                                    -> [(SubstM(t s), t s)]

{-
instance (TermShape s, Traversable s) => Term (s a) where
  isVar _      = False
  subTerms     = toList
  synEq x y    = Just True == (all (uncurry synEq) <$> matchTerm x y)
  fromSubTerms = modifySpine
-}

vars t | isVar t   = [t]
       | otherwise = nubBy synEq (vars =<< tt)
 where tt = subTerms t

collect :: Term t s => (t s -> Bool) -> t s -> [t s] 
collect pred t = nubBy synEq ([t' | t' <- t : subTerms t, pred t'] ++
                              concatMap (collect pred) (subTerms t))
--                 foldr (\t' gg -> collect pred t' ++ gg) [] (subTerms t)

-- * Syntactic equality
newtype SynEqTerm (t :: (* -> *) -> *) s = SynEq {unSynEq::t s} deriving Show
instance Term t s => Eq (SynEqTerm t s) where SynEq t1 == SynEq t2 = t1 `synEq` t2

-- | Do not confuse with substitution application. @replace@ makes no 
--   effort at avoiding variable capture
-- 
--   (you could deduce that from the type signature)
replace :: (Term t s) => [(t s,t s)] -> t s -> t s
replace []    = id
replace subst = fromJust . go (first SynEq <$> subst)
  where 
    go subst t = lookup (SynEq t) subst `mplus`
                 (fromSubTerms t <$> mapM (go subst) (subTerms t))
     

--------------------------------------------------------------------------
-- * Out and back of GT, purely
--------------------------------------------------------------------------
-- | Tries to return a term without mut. vars, fails if it finds any mut var.
zonkTerm :: Term t s => GT_ mode r s -> Maybe (t s)
zonkTerm = fromGTM zonkVar

-- | Replaces any mut. var with its current substitution, or a GenVar if none
zonkTerm' :: (Prune mode, Term (GT_ mode r) s, Term t s) => GT_ mode r s -> ST r (t s)
zonkTerm' t = do
  t' <- col t
  let mvars        = [r | MutVar r <- collect isMutVar t]
      n_gvars      = length$ collect isGenVar t
      f (MutVar r) = do
                v <- readVar r
                case v of 
                  Nothing -> return$ mkVar (fromJust(elemIndex r mvars) + n_gvars)
                  Just x  -> zonkTerm' x
      f v = return$ fromJust (zonkVar v) 
  fromGTM f t'

zonkTermUnsafe t = 
  let mvars        = [r | MutVar r <- collect isMutVar t]
      n_gvars      = length$ collect isGenVar t
      f (MutVar r) = mkVar (fromJust(elemIndex r mvars) + n_gvars)
      f v = fromJust (zonkVar v) 
   in fromGT f t

zonkVar (MutVar r) = Nothing -- error "zonkTerm: No vars" 
zonkVar (GenVar n) = Just $ mkVar n
zonkVar (CtxVar n) = Just $ mkVar n
zonkVar x = seq x $ error "ouch!: zonkVar" 

templateTerm :: Term t s => t s -> GT_ eq r s
templateTerm = mkGT (GenVar . varId)
