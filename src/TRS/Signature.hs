{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE OverlappingInstances,UndecidableInstances, TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE PatternGuards, NamedFieldPuns #-}
{-# LANGUAGE GADTs #-}


module TRS.Signature where

import Data.Foldable (Foldable, sum, toList)
import Data.List ((\\))
import Data.Maybe
import Data.Monoid
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Traversable


#ifdef HOOD
import Debug.Observe
#endif //HOOD

import TRS.Rewriting (Matchable)
import TRS.Rules
import TRS.Term
import TRS.Types
import TRS.Unification
import TRS.Utils

data Signature id = Sig { constructorSymbols :: Set id
                        , definedSymbols     :: Set id
                        , arity              :: Map id Int}
     deriving (Show, Eq)

allSymbols sig = constructorSymbols sig `Set.union` definedSymbols sig

instance Ord id => Monoid (Signature id) where
    mempty  = Sig mempty mempty mempty
    mappend (Sig c1 s1 a1) (Sig c2 s2 a2) = Sig (mappend c1 c2) (mappend s1 s2) (mappend a1 a2)

getSignatureFromRules :: (T id :<: f, Ord id, Foldable f) => (id -> id) -> [Rule f] -> Signature id
getSignatureFromRules mkLabel rules =
      Sig{arity= Map.fromList [(mkLabel f,length tt) | l :-> r <- rules, t <- [l,r]
                                             , Just (T f tt) <- map open (subterms t)]
         , definedSymbols     = Set.fromList dd
         , constructorSymbols = Set.fromList $ map mkLabel $
                                snub[root | l :-> r <- rules, t <- subterms r ++ properSubterms l, Just root <- [rootSymbol t]] \\ dd}
    where dd = snub [ root | l :-> _ <- rules, let Just root = rootSymbol l]

-- instance SignatureC (TRS f) where getSignature TRS{..} = getSignature rules

getArity :: (Show id, Ord id) => Signature id -> id -> Int
getArity Sig{arity} f = fromMaybe (error $ "getArity: symbol " ++ show f ++ " not in signature")
                               (Map.lookup f arity)

class Ord id => SignatureC a id | a -> id where getSignature :: a -> Signature id
instance (Foldable f, Ord id, T id :<: f) => SignatureC [Rule f] id where getSignature = getSignatureFromRules id
instance (Foldable f, Ord id, T id :<: f) => SignatureC (Set (Rule f)) id where getSignature = getSignatureFromRules id . toList

-- ----
-- TRS
-- ----
class (Matchable f f, Unifyable f, IsVar f, AnnotateWithPos f f, Ord (Term f)) => TRSC f
instance (Matchable f f, Unifyable f, IsVar f, AnnotateWithPos f f, Ord (Term f)) => TRSC f

class (Monoid t, SignatureC t id, T id :<: f, TRSC f) => TRS t id f | t -> id f where
    rules :: t -> [Rule f]
    tRS   :: [Rule f] -> t
    sig :: t -> Signature id

instance (TRSC f, Ord id, T id :<: f) => TRS [Rule f] id f where
    rules = id
    tRS   = id

instance (TRSC f, Ord id, T id :<: f) => TRS (Set (Rule f)) id f where
    rules = toList
    tRS   = Set.fromList

data SimpleTRS id f where SimpleTRS :: (Ord id, TRSC f, T id :<: f) => Set (Rule f) -> Signature id -> SimpleTRS id f
instance Ord id => SignatureC (SimpleTRS id f) id where getSignature (SimpleTRS   _ s) = s

instance (T id :<: f, Ord id, TRSC f) => TRS (SimpleTRS id f) id f where
    rules (SimpleTRS r _) = toList r
    tRS rules = SimpleTRS (Set.fromList rules) (sig rules)

instance (Ppr f, TRS t id f) => Show t where show = show . rules
instance (TRS t id f) => Eq t where a == b = rules a == rules b

instance (T id :<: f, Ord id, TRSC f) => Monoid (SimpleTRS id f) where
   mempty = SimpleTRS mempty mempty
   mappend (SimpleTRS r1 _) (SimpleTRS r2 _) = let rr = (r1 `mappend` r2) in SimpleTRS rr (sig rr)

instance (TRS t id f) => Size t where
    size = Data.Foldable.sum . fmap TRS.Types.size . rules


--tRS  rules = SimpleTRS (Set.fromList rules)

isDefined, isConstructor :: (TRS trs id f) => trs -> Term f -> Bool
isConstructor trs t = (`Set.member` constructorSymbols (getSignature trs)) `all` collectIds t
isDefined = (not.) . isConstructor

collectIds :: (T id :<: f) => Term f -> [id]
collectIds = foldTerm f where
    f t | Just (T id ids) <- prj t = id : concat ids
        | otherwise = []

mapRules :: (Rule f -> Rule f) -> SimpleTRS id f -> SimpleTRS id f
mapRules f (SimpleTRS rr sig) = SimpleTRS (Set.map f rr) sig

mapTerms :: (Term f -> Term f) -> SimpleTRS id f -> SimpleTRS id f
mapTerms f (SimpleTRS rr sig) = SimpleTRS (Set.map (fmap f) rr) sig

#ifdef HOOD
instance Observable (SimpleTRS id f) where observer trs@SimpleTRS{} = observeBase trs
#endif HOOD
