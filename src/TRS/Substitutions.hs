{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE GADTs #-}

module TRS.Substitutions (
     (//),
     Subst, SubstG(..), MkSubst(..), emptySubst,
     o, zonkSubst, restrictTo, concatSubst, insertSubst,
     applySubst, applySubstF, isRenaming,
     substRange, substDomain) where

import Control.Applicative
import Control.Arrow (first, second)
import Data.Maybe
import Text.PrettyPrint

import TRS.Types
import TRS.Utils

----------------------
-- * Substitutions
----------------------
(//) :: (Var :<: f, f :<: fs) => Term f -> Subst fs -> Term fs
(//) = flip applySubst

applySubst :: (Var :<: f, f :<: fs) => Subst fs -> Term f -> Term fs
applySubst s = foldTerm (applySubstF s)

applySubstF :: (Var :<: f, f :<: fs) => Subst fs -> f (Term fs) -> Term fs
applySubstF (Subst s) t
  | Just v@Var{} <- prj t   = fromMaybe (inject t) $ lookup (Exists v) s
  | otherwise               = inject t  -- Can we save some injects here and make this more efficient

data ExistsVar where Exists :: Var f -> ExistsVar
instance Eq  ExistsVar where Exists (Var _ i1) == Exists (Var _ i2) = i1 == i2
instance Ord ExistsVar where compare (Exists (Var _ i1)) (Exists (Var _ i2)) = compare i1 i2

newtype SubstG a = Subst [(ExistsVar, a)]

instance Functor SubstG where fmap f (Subst s) = Subst (map (second f) s)
instance (Eq a) => Eq (SubstG a) where Subst s1 == Subst s2 = s1 == s2

--newtype SubstM a = SubstM {fromSubstM :: [Maybe a]} deriving (Show, Monoid)

type Subst f = SubstG (Term f)

class MkSubst a f | a -> f where mkSubst :: a -> Subst f
--instance MkSubst [(Var g, Term f)]  f where mkSubst dict = Subst [(i,t) | (Var _ i, t) <- dict]
instance MkSubst [(Var(Term f), Term fs)] fs where mkSubst = Subst . map (first Exists)
instance MkSubst [(Int, Term f)]    f where mkSubst = Subst . map (first (Exists . Var Nothing))

instance Ppr f => Show (Subst f) where
    show (Subst s) = render $ braces $ fsep $ punctuate comma
                     [ ppr (In(Var n i)) <+> char '/' <+> ppr t  | (Exists (Var n i), t) <- s]

emptySubst :: SubstG a
emptySubst = Subst []

composeSubst,o :: (Var :<: f) => Subst f -> Subst f -> Subst f
composeSubst (Subst l1) s2@(Subst l2) = Subst (l2 ++ (second (applySubst s2) `map` l1))

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
   = Subst (snubBy (compare `on` fst) ((Exists v, t) : sigma'))

restrictTo :: (Eq (Term f), Var :<: f) => Subst f -> [Var (Term f)] -> Subst f
restrictTo (Subst s) vv = Subst [ binding | binding@(Exists (Var _ i),t) <- s, i `elem` indexes]
    where indexes = [i | Var _ i <- vv]

-- flatten a substitution (pointers are replaced with their values)
zonkSubst :: (Var :<: f, Eq (Term f)) => Subst f -> Subst f
zonkSubst s = fixEq (applySubst s <$>) s

substRange :: SubstG t -> [t]
substRange (Subst subst)  = snd $ unzip subst
substDomain :: SubstG t -> [(Maybe String, Int)]
substDomain (Subst subst) = [ (n,i) | Exists(Var n i) <- fst (unzip subst)]
isRenaming :: (IsVar s, Var :<: s) => SubstG (Term s) -> Bool
isRenaming subst = isVar `all` substRange subst
