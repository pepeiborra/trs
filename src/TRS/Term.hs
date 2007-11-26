{-# OPTIONS_GHC -fglasgow-exts #-}
module TRS.Term where

import Control.Applicative
import Control.Arrow (first, second)
import Control.Monad (replicateM, liftM, mplus, forM, when)
import Control.Monad.State (gets, modify, evalState)
import Control.Monad.Identity (runIdentity)
import Data.List (nub, nubBy, elemIndex)
import Data.Foldable (toList, Foldable)
import Data.Maybe (fromMaybe, fromJust, catMaybes)
import Data.Traversable (Traversable, mapM)
import Prelude hiding (mapM)

import {-# SOURCE#-} TRS.Core (col, Prune)
import {-# SOURCE#-} TRS.GTerms
import TRS.Rules
import TRS.Tyvars
import TRS.Types hiding (Term)
import TRS.Substitutions
import TRS.Utils

-- ---------------------------------------
-- * The class of terms
-- ----------------------------------------
class TermShape s => Term t (s :: * -> *) where
        isVar        :: t s -> Bool
        mkVar        :: Int -> t s
        varId        :: t s -> Maybe Int
        subTerms     :: t s -> [t s]
        fromSubTerms :: t s -> [t s] -> t s
        synEq        :: t s -> t s -> Bool  -- |syntactic equality
        mkGT         :: (t s -> GT_ eq r s) -> t s -> GT_ eq r s
        mkGT mkVar t = runIdentity (mkGTM (return . mkVar) t)
        mkGTM        :: Monad m => (t s -> m(GT_ eq r s)) -> t s -> m(GT_ eq r s)
        fromGTM      :: Monad m => (GT_ eq r s -> m(t s)) -> GT_ eq r s -> m(t s)
        fromGT       :: (GT_ eq r s -> t s) -> GT_ eq r s -> t s
        fromGT mkV t = runIdentity (fromGTM (return . mkV) t) 

applySubst   :: Term t s => SubstM (t s) -> t s -> t s
applySubst sm t = mutateTerm f t where 
     s = fromSubstM sm
     f t' | Just i <- varId t', i`inBounds` s, Just v <- s !! i = v
          | otherwise = mutateTerm f t'

mutateTerm f t  = (fromSubTerms t . map f . subTerms) t
mutateTermM f t = (fmap (fromSubTerms t) . mapM f . subTerms) t

-- TODO: TEST THAT THIS RULE FIRES
{-# RULES "castTerm/identity" castTerm = id #-}
castTerm :: forall t1 t2 s r . (Term t1 s, Term t2 s, Term (GT_ Semantic r) s) => t1 s -> t2 s
castTerm t = zonkTermUnsafe (templateTerm t :: GTE r s)

class Term t s => TRS t s m where
        rewrite      :: Term t1 s => [Rule t1 s] -> t s -> m(t s)
        unify        :: t s -> t s -> m(SubstM (t s))
        rewrite1     :: Term t1 s => [Rule t1 s] -> t s -> m(t s)
        narrow1      :: Term t1 s => [Rule t1 s] -> t s -> m(SubstM(t s), t s)

class Term t s => TRSN t s where
--        narrow1'     :: Term t1 s => [Rule t1 s] -> t s -> [(SubstM(t s), t s)]
        narrowFull   :: Term t1 s => [Rule t1 s] -> t s -> [(SubstM(t s), t s)]
        -- | Basic Narrowing
        narrowBasic  :: Term t1 s => [Rule t1 s] -> t s -> [(SubstM(t s), t s)]
        -- | Full Narrowing restricted by a predicate.
        --   Stops as soon as the predicate is positive or the 
        --   derivation finishes
        narrowFullBounded :: Term t1 s => (t s -> Bool) -> [Rule t1 s] -> t s 
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
newtype SynEqTerm (t :: (* -> *) -> *) s = SynEq {unSynEq::t s} --deriving Show
instance Term t s => Eq (SynEqTerm t s) where SynEq t1 == SynEq t2 = t1 `synEq` t2

instance Show (t s) => Show (SynEqTerm t s) where 
    showsPrec p (SynEq t) = ("SynEqTerm " ++) . showsPrec p t

-- | Replace (syntactically) subterms using the given dictionary
--   Do not confuse with substitution application. @replace@ makes no 
--   effort at avoiding variable capture
--   (you could deduce that from the type signature)
replace :: (Term t s) => [(t s,t s)] -> t s -> t s
replace []    = id
replace dict = fromJust . go 
  where 
    dict' = first SynEq <$> dict
    go t  = lookup (SynEq t) dict' `mplus` mutateTermM go t
     
-- ¿mutateTermM en Maybe no debería fallar con un Nothing? 
-- No falla, porque, viendo un termino como un arbol,
--  go siempre tiene éxito en las hojas, y por induccion en
--  todos los nodos 
--------------------------------------------------------------------------
-- * Out and back of GT, purely
--------------------------------------------------------------------------
-- | Tries to return a term without mut. vars, fails if it finds any mut var.
zonkTerm :: Term t s => GT_ mode r s -> Maybe (t s)
zonkTerm = fromGTM zonkVar

-- | Replaces any mut. var with its current substitution, or a (clean) GenVar if none
zonkTerm' :: (Prune mode, Term (GT_ mode r) s, Term t s) => GT_ mode r s -> ST r (t s)
zonkTerm' t = do
  t' <- col t
  let mvars        = [r | MutVar r <- collect isMutVar t]
      n_gvars      = length$ collect isGenVar t
  mvars_indexes <- catMaybes <$> forM mvars getUnique
  let skolem_offset = n_gvars + maximum mvars_indexes
  forM mvars $ \v -> 
       readVar' v >>= \x -> case x of
            Skolem   -> write v (GenVar $ fromJust(elemIndex v mvars) + 
                                          skolem_offset)
            Empty i  -> write v (GenVar i)
            Mutable{}-> return ()
  let f (MutVar r) = do
                Just v <- readVar r
                zonkTerm' v
      f v = return$ fromJust (zonkVar v) 
  fromGTM f t'

zonkTermUnsafe :: (Term t s, Term (GT_ mode r) s) => GT_ mode r s -> t s
zonkTermUnsafe t = 
  let mvars        = [r | MutVar r <- collect isMutVar t]
      n_gvars      = length$ collect isGenVar t
      f (MutVar r) = mkVar (fromJust(elemIndex r mvars) + n_gvars)
      f v = fromJust (zonkVar v) 
   in fromGT f t

zonkVar :: Term t s => GT_ mode r s -> Maybe (t s)
zonkVar (MutVar r) = Nothing -- error "zonkTerm: No vars" 
zonkVar (GenVar n) = Just $ mkVar n
zonkVar (CtxVar n) = Just $ mkVar n
zonkVar x = seq x $ error "ouch!: zonkVar" 

templateTerm :: Term t s => t s -> GTE r s
templateTerm = mkGT (GenVar . fromJust . varId)

