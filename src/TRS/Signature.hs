{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances, TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE GADTs #-}


module TRS.Signature where

import Data.Typeable
import Data.Generics
import Data.List ((\\))
import Data.Maybe
import Data.Monoid
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Traversable

import TRS.Rules
import TRS.Term
import TRS.Types
import TRS.Unification
import TRS.Utils

data Signature id = Sig { constructorSymbols :: Set id
                     , definedSymbols        :: Set id
                     , arity                 :: Map id Int}
     deriving (Show, Eq)

instance Ord id => Monoid (Signature id) where
    mempty  = Sig mempty mempty mempty
    mappend (Sig c1 s1 a1) (Sig c2 s2 a2) = Sig (mappend c1 c2) (mappend s1 s2) (mappend a1 a2)

class SignatureC a id | a -> id where getSignature :: a -> Signature id

instance SignatureC [Rule Basic] String where
    getSignature = getSignatureDefault id

getSignatureDefault mkLabel rules =
      Sig{arity= Map.fromList [(mkLabel f,length tt) | l :-> r <- rules, t <- [l,r]
                                             , Just (T f tt) <- map match (subterms t)]
         , definedSymbols     = Set.fromList dd
         , constructorSymbols = Set.fromList $ map mkLabel $
                                snub[root | l :-> r <- rules, t <- subterms r ++ properSubterms l, Just root <- [rootSymbol t]] \\ dd}
    where dd = snub [ root | l :-> _ <- rules, let Just root = rootSymbol l]

-- instance SignatureC (TRS f) where getSignature TRS{..} = getSignature rules

getArity :: (Show id, Ord id) => Signature id -> id -> Int
getArity Sig{..} f = fromMaybe (error $ "getArity: symbol " ++ show f ++ " not in signature")
                               (Map.lookup f arity)


-- ----
-- TRS
-- ----
class (Var :<: f, Traversable f, MatchShapeable f f, Unifyable f, Eq (Term f)) => TRSC f
instance (Var :<: f, Traversable f, MatchShapeable f f, Unifyable f, Eq (Term f)) => TRSC f

data TRS id f where TRS :: (Ord id, TRSC f, T id :<: f) => [Rule f] -> Signature id -> TRS id f

instance Ppr f => Show (TRS id f) where show trs = show $ rules trs

instance (Ord id, TRSC f, SignatureC [Rule f] id) => Monoid (TRS id f) where
    mempty = TRS mempty mempty
    mappend (TRS r1 _) (TRS r2 _) = let rr = (r1 `mappend` r2) in TRS rr (getSignature rr)

instance SignatureC (TRS id f) id where getSignature = sig

tRS rules = TRS rules (getSignature rules)
rules (TRS r _) = r; sig (TRS _ s) = s

isConstructor :: (T id :<: f, Ord id) => Term f -> TRS id f -> Bool
isConstructor t trs = (`Set.member` constructorSymbols (sig trs)) `all` collectIds t

collectIds :: (T id :<: f) => Term f -> [id]
collectIds = foldTerm f where
    f t | Just (T id ids) <- prj t = id : concat ids
        | otherwise = []