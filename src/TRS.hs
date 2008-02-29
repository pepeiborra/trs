module TRS ( module TRS.Term
--           , module TRS.Terms
	   , module TRS.Types
           , module TRS.Rules
           , GoodShape
           , module TRS.Substitutions 
           , module TRS)  where

import TRS.Types
import TRS.Rules
import TRS.Substitutions 
import TRS.GTerms
import TRS.Term
import TRS.Terms
import TRS.Core (GoodShape)

type BasicTerm = TermStatic BasicShape
type BasicRule = RuleS BasicShape
type RuleS s   = Rule TermStatic s

