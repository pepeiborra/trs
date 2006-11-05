module TRS ( module TRS.Core )  where

import TRS.Core ( GTE, s, genVar
                , isMutVar, isGenVar, isCtxVar, noMVars, noGVars
--		, Fix(..), toFix, fromFix, toFixG, fromFixG
                , Subst
                , Rule, RuleG(..), swap
                , RWTerm(..), Omega, OmegaPlus
                , narrow1, narrow1', narrow1V, narrowFull, narrowFullV
                , narrowFullBounded, narrowFullBoundedV
                , rewrite, rewrite1
                , generalize, generalizeG, instan, autoInst, collect
                , runE, runEG, runEGG, runEIO
                , runL, runLG, runLGG, runLIO
                , run, runG, runGG, runIO) 
