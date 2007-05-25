module TRS ( module TRS.Core 
	   , module TRS.Types )  where

import TRS.Types( TermStatic, TermStatic_(..), s, matchStatic
                , GTE, genVar, isMutVar, isGenVar
		, ST, runST, stToIO, readSTRef, writeSTRef
                , Subst
		, Rule, RuleG(..), swap
		, RWTerm(..), Omega, OmegaPlus
                , noMVars, noGVars
		)
		
import TRS.Core ( instTerm, instTermG, zonkTerm, zonkTermG
                , unify
                , narrow1, narrow1', narrow1V, narrowFull, narrowFullV
                , narrowFullBounded, narrowFullBoundedV
                , rewrite, rewrite1
                , generalize, generalizeG, generalizeGG
                , instan, autoInst, collect
                , runE, runEG, runEGG, runEIO
                , runM, runMG, runMGG, runMIO
                , runL, runLG, runLGG, runLIO
                , run, runG, runGG, runIO) 
