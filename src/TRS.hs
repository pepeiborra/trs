module TRS ( module TRS.Term
	   , module TRS.Types
           , module TRS.Rules
           , module TRS.Unification
           , module TRS.Substitutions
           , module TRS.Context
           , module TRS.Rewriting
           , module TRS.Narrowing
           , module TRS)  where

import TRS.Types hiding (match)
import TRS.Rules
import TRS.Substitutions
import TRS.Term
import TRS.Unification hiding (unify')
import TRS.Rewriting
import TRS.Narrowing
import TRS.Context