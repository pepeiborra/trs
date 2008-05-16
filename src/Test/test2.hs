module Test.Test2 where

import Data.AlaCarte

import TRS.Rules
import TRS.Types
import TRS.Rewriting
import TRS.Narrowing
import Test.Peano
import TRS.Context

type PeanoT  = Term (Var :+: Peano)
type PeanoTH = Term (Hole :+: Peano :+: Var)

peanoTRS = [ x +: s(y) :-> s(x +: y)
           , y +: z    :-> y         ] :: [RuleG PeanoTH]
opeanoTRS'= [ s x +: y :-> s(x +: y)
            , z   +: y :-> y         ] :: [RuleG PeanoTH]

x :: (Var :<: f) => Term f
x = var 0
y = var 1

--------------------------
-- Testing Reductions
--------------------------

-- Testing rewriting
two   = s(s(z)) :: PeanoTH
five  = s(s(s(two))) :: PeanoTH
seven = two +: five  :: PeanoTH

--seven' :: Monad m => m PeanoTH
seven' = rewrite1 peanoTRS seven :: [PeanoTH]
eight' = rewrite1 peanoTRS (seven +: s(z)) `asTypeOf` Nothing
test1 = TRS.Rewriting.match z (z :: PeanoTH) `asTypeOf` Nothing

narr = fst `map` narrow1 peanoTRS seven

sx = s x :: PeanoTH

sz = s z :: PeanoTH

--v = In $ Inr $ Inr $ Var 0 :: PeanoTH  -- In (Inl (Succ (In (Inr (Inr (Var 0))))))

--h = In $ Inr $ Inl $ Hole 0 :: PeanoTH -- In (Inl (Succ (In (Inl Zero))))