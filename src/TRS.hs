module TRS ( module TRS.Core 
	   , module TRS.Types )  where

import TRS.Types( GTE, s, genVar, isMutVar, isGenVar, isCtxVar
		, Subst
		, Rule, RuleG(..), swap
		, RWTerm(..), Omega, OmegaPlus
		)
		
import TRS.Core ( noMVars, noGVars
--		, Fix(..), toFix, fromFix, toFixG, fromFixG
                , narrow1, narrow1', narrow1V, narrowFull, narrowFullV
                , narrowFullBounded, narrowFullBoundedV
                , rewrite, rewrite1
                , generalize, generalizeG, instan, autoInst, collect
                , runE, runEG, runEGG, runEIO
                , runL, runLG, runLGG, runLIO
                , run, runG, runGG, runIO) 
