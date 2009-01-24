{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances, TypeSynonymInstances #-}
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

import TRS.Rewriting (Matchable)
import TRS.Rules
import TRS.Term hiding (isConstructor, isDefined)
import TRS.Types
import TRS.Unification
import TRS.Utils

data Signature id = Sig { constructorSymbols :: Set id
                        , definedSymbols     :: Set id
                        , arity              :: Map id Int}
     deriving (Show, Eq)

instance Ord id => Monoid (Signature id) where
    mempty  = Sig mempty mempty mempty
    mappend (Sig c1 s1 a1) (Sig c2 s2 a2) = Sig (mappend c1 c2) (mappend s1 s2) (mappend a1 a2)

class SignatureC a id | a -> id where getSignature :: a -> Signature id

instance (T id :<: f, Ord id, Foldable f) => SignatureC [Rule f] id where
    getSignature = getSignatureFromRules id

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


-- ----
-- TRS
-- ----
class (Matchable f f, Unifyable f, AnnotateWithPos f f, Ord (Term f)) => TRSC f
instance (Matchable f f, Unifyable f, AnnotateWithPos f f, Ord (Term f)) => TRSC f

data TRS id f where TRS :: (Ord id, TRSC f, T id :<: f) => Set (Rule f) -> Signature id -> TRS id f

instance Ppr f => Show (TRS id f) where show trs = show $ rules trs
instance Eq (Term f) => Eq (TRS id f) where a == b = rules a == rules b

instance (T id :<: f, Ord id, TRSC f) => Monoid (TRS id f) where
   mempty = TRS mempty mempty
   mappend (TRS r1 _) (TRS r2 _) = let rr = (r1 `mappend` r2) in TRS rr (getSignature rr)

instance SignatureC (TRS id f) id where getSignature = sig
instance (T id :<: f, Ord id, Foldable f) => SignatureC (Set (Rule f)) id where
    getSignature = getSignatureFromRules id . toList

instance SizeF f => Size (TRS id f) where size = Data.Foldable.sum . fmap TRS.Types.size . rules

tRS' :: (T id :<: t, Ord id, TRSC t) => [Rule t] -> TRS id t
rules :: TRS id t -> [Rule t]

tRS  rules = TRS (Set.fromList rules)
tRS' rules = TRS (Set.fromList rules) (getSignature rules)
rules (TRS r _) = toList r; sig (TRS _ s) = s


isDefined, isConstructor :: (T id :<: f, Ord id) => TRS id f -> Term f -> Bool
isConstructor trs t = (`Set.member` constructorSymbols (sig trs)) `all` collectIds t

isDefined = (not.) . isConstructor

collectIds :: (T id :<: f) => Term f -> [id]
collectIds = foldTerm f where
    f t | Just (T id ids) <- prj t = id : concat ids
        | otherwise = []