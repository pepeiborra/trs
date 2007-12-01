module TRS.Rules where

data RuleG a = a :-> a

type Rule t (s :: * -> *) = RuleG (t s)
