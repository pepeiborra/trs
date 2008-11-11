{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances, FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternGuards #-}
module TRS ( module TRS.Term
	   , module TRS.Types
           , module TRS.Rules
           , module TRS.Unification
           , module TRS.Substitutions
           , module TRS.Context
           , module TRS.Rewriting
           , module TRS.Narrowing
           , module TRS.MonadFresh
           , module TRS.MonadEnv
           , module TRS.UMonad
           , module TRS.Signature
           , module TRS)  where

import TRS.Types hiding (match)
import TRS.Signature hiding (isConstructor, isDefined)
import TRS.Rules hiding (isConstructor, isDefined)
import qualified TRS.Signature as Sig
import qualified TRS.Rules as Rules
import TRS.Substitutions
import TRS.Term
import TRS.Unification
import TRS.Rewriting
import TRS.Narrowing
import TRS.Context
import TRS.MonadFresh
import TRS.MonadEnv
import TRS.UMonad

class IsConstructor trs tf where
    type TermType trs ::(* -> *) -> *
    isConstructor :: trs -> TermType trs tf -> Bool
    isDefined     :: trs -> TermType trs tf -> Bool
    isConstructor = (not.).isDefined
    isDefined     = (not.).isConstructor

instance (IsVar tf, MatchShapeable f tf, Var :<: tf) => IsConstructor [Rule f] tf where
    type TermType [Rule f] = Term
    isConstructor = Rules.isConstructor

instance (T id :<: f, Ord id) => IsConstructor (TRS id f) f where
    type TermType (TRS id f) = Term
    isConstructor = Sig.isConstructor