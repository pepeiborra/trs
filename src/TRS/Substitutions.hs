{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module TRS.Substitutions (
     Subst, SubstG(..), MkSubst(..), emptySubst,
     o, concatSubst, insertSubst,
     applySubst, isRenaming,
     substRange, substDomain) where

import Control.Arrow (second)
import Data.AlaCarte
import Data.Maybe

import TRS.Types
import TRS.Utils

----------------------
-- * Substitutions
----------------------
newtype SubstG a = Subst {fromSubst::[(Int, a)]}
   deriving (Show)

--newtype SubstM a = SubstM {fromSubstM :: [Maybe a]} deriving (Show, Monoid)

type Subst f = SubstG (Term f)

class MkSubst a f | a -> f where mkSubst :: a -> Subst f
instance MkSubst [(Var g, Term f)]  f where mkSubst dict = Subst [(i,t) | (Var i, t) <- dict]
instance (Var :<: f) => MkSubst [(Term f, Term f)] f where mkSubst dict = Subst [(i,t) | (v, t) <- dict, let Just (Var i) = match v]
instance MkSubst [(Int, Term f)]    f where mkSubst = Subst

emptySubst :: SubstG a
emptySubst = Subst []

composeSubst,o :: (Var :<: f) => Subst f -> Subst f -> Subst f
composeSubst (Subst l1) s2@(Subst l2) = Subst (l2 ++ (second (applySubst s2) `map` l1))

o = composeSubst

concatSubst :: (Var :<: f) => [Subst f] -> Subst f
concatSubst = Prelude.foldl composeSubst (Subst [])

insertSubst :: Var (Term f) -> Term f -> Subst f -> Subst f
insertSubst (Var i) t (Subst sigma) = Subst (snubBy (compare `on` fst) ((i,t) : sigma))

{-
mkSubstM :: [Int] -> [a] -> SubstM a
mkSubstM [] _  = mempty
mkSubstM ii vv = let
    table = Map.fromList (zip ii vv)
  in SubstM (map (`Map.lookup` table) [0 .. maximum ii])

instance Traversable SubstM where
    traverse f (SubstM x) = SubstM <$> (traverse .traverse) f x

instance Functor SubstM where 
    fmap f (SubstM x) = SubstM $ map (fmap f) x

instance Foldable SubstM where foldMap = foldMapDefault

instance Applicative SubstM where
    pure = SubstM . (:[]) . Just
    SubstM f <*> SubstM xx = SubstM (zipWith ap f xx)
-}
applySubst :: (Var :<: f) => Subst f -> Term f -> Term f
applySubst (Subst s) = foldTerm f where
  f t | Just (Var i) <- prj t = fromMaybe (In t) (lookup i s)
      | otherwise             = In t

substRange :: SubstG t -> [t]
substRange (Subst subst)  = snd $ unzip subst
substDomain :: SubstG t -> [Int]
substDomain (Subst subst) = fst $ unzip subst
isRenaming :: (Var :<: s) => SubstG (Term s) -> Bool
isRenaming subst = isVar `all` substRange subst
