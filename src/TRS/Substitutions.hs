{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

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
(//) :: (Var :<: f, f :<: fs) => Term f -> Subst fs -> Term fs
(//) = flip applySubst

applySubst :: (Var :<: f, f :<: fs) => Subst fs -> Term f -> Term fs
applySubst s t = {-# SCC "applySubst" #-}
                 foldTerm (applySubstF s) t

applySubstF :: (Var :<: f, f :<: fs) => Subst fs -> f (Term fs) -> Term fs
applySubstF (Subst s) t
  | Just v@Var{} <- prj t   = fromMaybe (inject t) $ Map.lookup (Exists v) s
  | otherwise               = inject t  -- Can we save some injects here and make this more efficient

lookupSubst :: Subst f -> Var whatever -> Maybe (Term f)
lookupSubst (Subst s) v = {-# SCC "lookupSubst" #-}
                          Map.lookup (Exists v) s

data ExistsVar where Exists :: Var f -> ExistsVar
instance Eq  ExistsVar where Exists (Var _ i1) == Exists (Var _ i2) = i1 == i2
instance Ord ExistsVar where compare (Exists (Var _ i1)) (Exists (Var _ i2)) = compare i1 i2

newtype SubstG a = Subst {fromSubst:: Map.Map ExistsVar a} deriving (Eq, Functor)

type Subst f = SubstG (Term f)

class MkSubst a f | a -> f where mkSubst :: a -> Subst f
instance MkSubst [(Var(Term f), Term fs)] fs where mkSubst = Subst . Map.fromList . map (first Exists)
instance MkSubst [(Int, Term f)]    f where mkSubst = Subst . Map.fromList . map (first (Exists . Var Nothing))

instance Ppr f => Show (Subst f) where
    show (Subst m) = render $ braces $ fsep $ punctuate comma
                     [ ppr (In(Var n i)) <+> char '/' <+> ppr t  | (Exists (Var n i), t) <- Map.toList m]

instance (Var :<: f) => Monoid (Subst f) where
    mempty  = emptySubst
    mappend = composeSubst

emptySubst :: SubstG a
emptySubst = Subst mempty

composeSubst,o :: (Var :<: f) => Subst f -> Subst f -> Subst f
composeSubst (Subst map1) s2@(Subst map2) = {-# SCC "composeSubst" #-}
                                            Subst (map2 `mappend` ( applySubst s2 <$> map1))

o = composeSubst

-- | Non biased parallel composition, a partial function which, when succeeds, is
--   equivalent to standard biased parallel composition
mergeSubst :: (Var :<: f, Eq (Term f), Monad m) => Subst f -> Subst f -> m (Subst f)
mergeSubst s1 s2 | agree     = return (Subst s)
                  | otherwise = fail "not mergeable substitutions"
  where s = fromSubst s1 `Map.union` fromSubst s2
        agree = all (\(_,i) -> let v = var i :: Term Var in applySubst s1 v == applySubst s2 v)
                    (substDomain s1 `intersect` substDomain s2)

mergeSubsts :: (Var :<: f, Eq (Term f), Monad m) => [Subst f] -> m (Subst f)
mergeSubsts = {-# SCC "mergeSubsts" #-} foldM mergeSubst mempty

insertSubst :: (Var :<: fs) => Var (Term g) -> Term fs -> Subst fs -> Subst fs
insertSubst v t sigma | Subst sigma' <- applySubst (mkSubst [(v,t)]) <$> sigma
   ={-# SCC "insertSubst" #-}
     Subst (Map.insert (Exists v) t sigma')

restrictTo :: (Eq (Term f), Var :<: f) => Subst f -> [Var (Term f)] -> Subst f
restrictTo (Subst m) vv = {-# SCC "restrictTo" #-}
                          Subst $ Map.fromList [ binding | binding@(Exists (Var _ i),t) <- Map.toList m
                                                         , i `elem` indexes]
    where indexes = [i | Var _ i <- vv]

substRange :: SubstG t -> [t]
substRange (Subst subst)  = Map.elems subst
substDomain :: SubstG t -> [(Maybe String, Int)]
substDomain (Subst subst) = [ (n,i) | Exists(Var n i) <- Map.keys subst]
isRenaming :: (IsVar s, Var :<: s) => SubstG (Term s) -> Bool
isRenaming subst = {-# SCC "isRenaming" #-}
                   isVar `all` substRange subst

normalize :: Subst f -> Subst f
normalize (Subst map) = undefined --Map.filterWithKey (/=))