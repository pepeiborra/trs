module TRS.GTerms where

import TRS.Tyvars

type Ptr mode r s = Ptr_ r (GT_ mode r s)

data GT_ (mode :: *)  (r :: *) (s :: * -> *) = 
   S (s(GT_ mode r s))
 | MutVar (Ptr mode r s)
 | GenVar Int
 | CtxVar Int

data Syntactic  -- denotes pure syntactic equality
data Semantic   -- denotes syntactic equality modulo variables
data Basic      -- denotes a Basic Narrowing derivation

type GT r s  = GT_ Syntactic r s
type GTE r s = GT_ Semantic r s

isGenVar, isMutVar, isCtxVar, isTerm :: GT_ eq r s -> Bool