module TRS ( module TRS.Term
           , module TRS.Core
--           , module TRS.Terms
	   , module TRS.Types
           , module TRS.Rules
           , module TRS.Substitutions )  where

import TRS.Types
import TRS.Rules
import TRS.Substitutions 
import TRS.GTerms
import TRS.Term
		
import TRS.Core ( noMVars, GoodShape ) --Omega, OmegaPlus) 
