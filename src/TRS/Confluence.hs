{-# LANGUAGE NoMonomorphismRestriction, FlexibleContexts #-}
module TRS.Confluence (criticalPairs) where

import Control.Applicative
import Control.Monad
import Control.Monad.Logic
import Data.List
import Data.Traversable
import TRS.MonadFresh
import TRS.Rewriting
import TRS.Rules
import TRS.Term
import TRS.Types
import TRS.Substitutions
import TRS.Unification

confluent :: (Rewritable f f, Unifyable f, AnnotateWithPos f f) => [Rule f] -> Bool
confluent rr = (all (joinable rr) . criticalPairs) rr

-- TODO Take advantage of commutativity of substitution to reduce search space
criticalPairs :: (Var :<: f, Traversable f, Unifyable f, HashConsed f, IsVar f, AnnotateWithPos f f) => [Rule f] -> [(Term f, Term f)]
criticalPairs rr = nub $ do
  r@(l1 :-> r1) <- rr
  l2 :-> r2 <- (`variant'` r) <$> rr
  l1_p      <- subterms (annotateWithPos l1)
  guard (not $ isVar l1_p)
  theta     <- unify (dropNote l1_p) l2
  let l1'    = updateAt (note l1_p) l1 r2
  return (r1 // theta, l1' // theta)

joinable :: Rewritable rf f => [Rule rf] -> (Term f, Term f) -> Bool
joinable rr (t,u) = observeAll (reduce rr t) == observeAll(reduce rr u)

-- Example
-- -------
f = term1 "f"
g = term1 "g"

rr = [f (f x) :-> g x, f (f x) :-> g x] :: [Rule Basic]