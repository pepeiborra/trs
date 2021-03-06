{-# LANGUAGE CPP #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, StandaloneDeriving #-}
{-# LANGUAGE NoMonomorphismRestriction  #-}

module TRS.Substitutions (
     (//),
     Subst, SubstG(..), MkSubst(..), emptySubst,
     o, lookupSubst, restrictTo, insertSubst,
     mergeSubst, mergeSubsts, unionSubst,
     applySubst, applySubstF, isRenaming,
     substRange, substDomain,
     variant, variant') where

import Control.Applicative
import Control.Arrow (first)
import Control.Monad.State
import Control.Parallel.Strategies
import Data.List (intersect, (\\))
import Data.Foldable
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Maybe
import Data.Monoid
import Text.PrettyPrint
import Prelude hiding (elem,all, concatMap)

import TRS.Types
import TRS.Term
import TRS.MonadFresh
import TRS.Utils (snub)

#ifdef HOOD
import Debug.Observe
#endif

----------------------
-- * Substitutions
----------------------
(//) :: (IsVar f, f :<: fs, HashConsed fs) => Term f -> Subst fs -> Term fs
(//) = (hashCons.) .flip applySubst

applySubst :: (IsVar f, f :<: fs, HashConsed fs) => Subst fs -> Term f -> Term fs
applySubst s t = {-# SCC "applySubst" #-}
                 foldTerm (applySubstF s) t

applySubstF :: (IsVar f, f :<: fs) => Subst fs -> f (Term fs) -> Term fs
applySubstF s t
  | isNothing uid = inject t -- Can we save some injects here and make this more efficient
  | Just i <- uid = fromMaybe (inject t) $ lookupKey s i
  where uid = uniqueIdF t

lookupSubst :: IsVar g => Subst f -> Term g -> Maybe (Term f)
lookupSubst s t | Just i <- uniqueId t = {-# SCC "lookupSubst" #-}
                  lookupKey s i
                | otherwise = Nothing

type Subst f     = SubstG (Term f)
newtype SubstG a = Subst {fromSubst:: Map.Map Key a} deriving (Eq, Functor)
subst            = normalize . Subst
subst'           = subst . Map.fromList

deriving instance NFData a => NFData (SubstG a)

data Key where KeyTerm :: (Ppr f, IsVar f) => Term f -> Key
               KeyId   :: Int -> Key

instance NFData Key where
  rnf (KeyId i)   = rnf i
  rnf (KeyTerm t) = t `seq` ()

instance Eq Key  where t1 == t2      = unique t1 == unique t2
instance Ord Key where compare k1 k2 = compare (unique k1) (unique k2)
instance Show Key where
    showsPrec _ (KeyId i)   = ("KeyId " ++ ) . (show i ++)
    showsPrec _ (KeyTerm t) = ("KeyTerm " ++ ) . (show t ++)

#ifdef HOOD
instance Observable Key where observer = observeBase
#endif

{-# INLINE unique #-}
unique :: Key -> Int
unique (KeyId i) = i
unique (KeyTerm t) | Just i <- uniqueId t = i
unique (KeyTerm t) = error ("A substitution is binding on something which is not a variable:  " ++ show t)

class MkSubst a f | a -> f where mkSubst :: a -> Subst f
instance (Ppr f, IsVar f, IsVar fs) => MkSubst [(Term f, Term fs)] fs where mkSubst = subst' . map (first (KeyTerm))
instance IsVar fs => MkSubst [(Var h, Term fs)] fs where mkSubst = subst' . map (first (\(Var n i) -> KeyTerm $ hIn $ Var n i))
instance IsVar f  => MkSubst [(Int, Term f)]    f  where mkSubst = subst' . map (first KeyId)
instance Ppr f => Show (Subst f) where
    show (Subst m) = render $ braces $ fsep $ punctuate comma (
                     [ ppr k <+> char '/' <+> ppr t  | (KeyTerm k, t) <- Map.toList m] ++
                     [ ppr (var i :: Term Var) <+> char '/' <+> ppr t  | (KeyId i, t) <- Map.toList m] )

instance (IsVar f, HashConsed f) => Monoid (Subst f) where
    mempty  = emptySubst
    mappend = composeSubst

emptySubst :: SubstG a
emptySubst = Subst mempty

composeSubst,o :: (IsVar f, HashConsed f ) => Subst f -> Subst f -> Subst f
composeSubst (Subst map1) s2@(Subst map2) = {-# SCC "composeSubst" #-}
                                            subst (map2 `mappend` map1')
  where Subst map1' = subst (applySubst s2 <$> map1)

o = composeSubst

-- | Non biased parallel composition, a partial function which, when succeeds, is
--   equivalent to standard biased parallel composition
mergeSubst :: (IsVar f, Eq (Term f), Monad m) => Subst f -> Subst f -> m (Subst f)
mergeSubst s1 s2 | agree     = return (subst s)
                  | otherwise = fail "not mergeable substitutions"
  where s = fromSubst s1 `Map.union` fromSubst s2
        agree = all (\i -> lookupKey s1 i == lookupKey s2 i)
                    (substDomain s1 `intersect` substDomain s2)

mergeSubsts :: (IsVar f, Eq (Term f), HashConsed f, Monad m) => [Subst f] -> m (Subst f)
mergeSubsts ss = {-# SCC "mergeSubsts" #-} foldM mergeSubst mempty ss

unionSubst :: SubstG a -> SubstG a -> SubstG a
unionSubst s1 s2 = Subst (fromSubst s1 `Map.union` fromSubst s2)

insertSubst :: (IsVar g, Ppr g, IsVar fs, HashConsed fs) => Term g -> Term fs -> Subst fs -> Subst fs
insertSubst v t sigma
    | isJust $ uniqueId v
    , t'           <- applySubst sigma t
    , Subst sigma' <- applySubst (mkSubst [(v,t')]) <$> sigma
    ={-# SCC "insertSubst" #-}
     subst (Map.insert (KeyTerm v) t' sigma')
    | otherwise = sigma

restrictTo :: (IsVar vars) => Subst f -> [Term vars] -> Subst f
restrictTo (Subst s) vv = {-# SCC "restrictTo" #-}
                  Subst $ Map.filterWithKey (\k _ -> unique k `elem` indexes) s
    where indexes = [i | Just i <- map uniqueId vv]

substRange :: SubstG t -> [t]
substRange (Subst subst)  = Map.elems subst
substDomain :: SubstG t -> [Int]
substDomain (Subst subst) = map unique $ Map.keys subst

isRenaming :: (IsVar s) => SubstG (Term s) -> Bool
isRenaming subst = {-# SCC "isRenaming" #-}
                   isVar `all` substRange subst

normalize :: IsVar f => Subst f -> Subst f
normalize (Subst map) = Subst $ Map.filterWithKey (\k t -> case uniqueId t of
                                                             Nothing -> True
                                                             Just i  -> i /= unique k)
                                                  map

lookupKey :: Subst f -> Int -> Maybe (Term f)
lookupKey (Subst s) i = Map.lookup (KeyId i) s



variant :: (MonadFresh m, HashConsed f, Var :<: fs, IsVar fs, Foldable fs, fs :<: f, Var :<: f, IsVar f, Functor t, Foldable t) => t (Term fs) -> m(t (Term f))
variant r = {-# SCC "variant1" #-} do
     let vars_r = snub (concatMap vars r)
     vars'  <- replicateM (length vars_r) fresh
     return $ applySubst (mkSubst (vars_r `zip` map var vars')) <$> r


-- | Takes a term t and a term u and returns a variant of t which is fresh w.r.t. u
variant' :: (Var :<: f, IsVar f, Foldable f, Foldable g, Var :<: g, HashConsed f, Functor t, Foldable t) => t(Term f) -> t(Term g) -> t(Term f)
variant' t u = evalState (variant t) ([0..] \\ (varId <$> concatMap vars u))



#ifdef HOOD
-- deriving instance Show a => Observable (SubstG a)
instance Ppr f => Observable (Subst f) where observer = observeBase
#endif
