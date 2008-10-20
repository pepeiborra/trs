{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoMonomorphismRestriction  #-}

module TRS.Substitutions (
     (//),
     Subst, SubstG(..), MkSubst(..), emptySubst,
     o, lookupSubst, restrictTo, insertSubst,
     mergeSubst, mergeSubsts,
     applySubst, applySubstF, isRenaming,
     substRange, substDomain) where

import Control.Applicative
import Control.Arrow (first, second)
import Control.Monad
import Data.List (intersect)
import Data.Foldable
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Maybe
import Data.Monoid
import Text.PrettyPrint
import Prelude hiding (elem,all)

import TRS.Types
import TRS.Utils

----------------------
-- * Substitutions
----------------------
(//) :: (IsVar f, f :<: fs) => Term f -> Subst fs -> Term fs
(//) = flip applySubst

applySubst :: (IsVar f, f :<: fs) => Subst fs -> Term f -> Term fs
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

data Key where KeyTerm :: (Ppr f, IsVar f) => Term f -> Key
               KeyId   :: Int -> Key

instance Eq Key  where t1 == t2      = unique t1 == unique t2
instance Ord Key where compare k1 k2 = compare (unique k1) (unique k2)
instance Show Key where
    showsPrec _ (KeyId i) = ("KeyId" ++ ) . (show i ++)
    showsPrec _ (KeyTerm t) = ("KeyTerm" ++ ) . (show t ++)

{-# INLINE unique #-}
unique (KeyId i) = i
unique (KeyTerm t) | Just i <- uniqueId t = i

type Subst f     = SubstG (Term f)
newtype SubstG a = Subst {fromSubst:: Map.Map Key a} deriving (Eq, Functor)
subst            = normalize . Subst
subst'           = subst . Map.fromList

class MkSubst a f | a -> f where mkSubst :: a -> Subst f
instance (Ppr f, IsVar f, IsVar fs) => MkSubst [(Term f, Term fs)] fs where mkSubst = subst' . map (first (KeyTerm))
instance IsVar fs => MkSubst [(Var h, Term fs)] fs where mkSubst = subst' . map (first (\(Var n i) -> KeyTerm $ In $ Var n i))
instance IsVar f  => MkSubst [(Int, Term f)]    f  where mkSubst = subst' . map (first KeyId)
instance Ppr f => Show (Subst f) where
    show (Subst m) = render $ braces $ fsep $ punctuate comma (
                     [ ppr k <+> char '/' <+> ppr t  | (KeyTerm k, t) <- Map.toList m] ++
                     [ ppr (var i :: Term Var) <+> char '/' <+> ppr t  | (KeyId i, t) <- Map.toList m] )

instance (IsVar f) => Monoid (Subst f) where
    mempty  = emptySubst
    mappend = composeSubst

emptySubst :: SubstG a
emptySubst = Subst mempty

composeSubst,o :: (IsVar f) => Subst f -> Subst f -> Subst f
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

mergeSubsts :: (IsVar f, Eq (Term f), Monad m) => [Subst f] -> m (Subst f)
mergeSubsts ss = {-# SCC "mergeSubsts" #-} foldM mergeSubst mempty ss

insertSubst :: (IsVar g, Ppr g, IsVar fs) => Term g -> Term fs -> Subst fs -> Subst fs
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
