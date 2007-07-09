{-# OPTIONS_GHC -fglasgow-exts #-}
{-# OPTIONS_GHC -fallow-undecidable-instances #-}
module TRS.Signature where

import Data.Typeable
import Data.Generics

import TRS.Terms
import TRS.Types


data Symbol s = Symbol {name::String, arity::Int} 
                deriving (Eq,Show,Typeable)
data Signature s = Sig {defined::[Symbol s], constructors::[Symbol s]}
                   deriving (Eq,Show,Typeable)