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
           , module TRS.Signature
           , module TRS)  where

import TRS.Types
import TRS.Signature
import TRS.Rules
import TRS.Substitutions
import TRS.Term
import TRS.Unification
import TRS.Rewriting
import TRS.Narrowing
import TRS.Context
