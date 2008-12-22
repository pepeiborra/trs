{-# LANGUAGE NoMonomorphismRestriction, FlexibleContexts #-}
module TRS.Confluence (criticalPairs) where

import Control.Applicative
import Control.Monad
import Data.List
import Data.Traversable
import TRS.MonadFresh
import TRS.Rules
import TRS.Term
import TRS.Types
import TRS.Substitutions
import TRS.Unification


-- TODO Take advantage of commutativity of substitution to reduce search space
criticalPairs :: (Var :<: f, Traversable f, Unifyable f, HashConsed f, IsVar f, AnnotateWithPos f f) => [Rule f] -> [(Term f, Term f)]
criticalPairs rr = nub $ do
  r@(l1 :-> r1) <- rr
  l2 :-> r2 <- variant' r <$> rr
  l1_p      <- subterms (annotateWithPos l1)
  guard (not $ isVar l1_p)
  theta     <- unify (dropNote l1_p) l2
  let l1'    = updateAt (note l1_p) l1 r2
  return (r1 // theta, l1' // theta)

-- Example
-- -------
f = term1 "f"
g = term1 "g"

rr = [f (f x) :-> g x, f (f x) :-> g x] :: [Rule Basic]