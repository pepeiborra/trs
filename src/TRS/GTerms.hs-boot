module TRS.GTerms where

import Control.Monad.ST
import TRS.Tyvars
import TRS.Types
import {-#SOURCE#-}TRS.Term

type Ptr user mode r s = Ptr_ r (GT_ user mode r s)

data GT_ (user :: *) (mode :: *)  (r :: *) (s :: * -> *) = 
   S (s(GT_ user mode r s))
 | MutVar {note_::Maybe user, ref::Ptr user mode r s}
 | GenVar {note_::Maybe user, unique::Int}
 | CtxVar {unique::Int}
 | Skolem {note_::Maybe user, unique::Int}
 | Top    {note_::Maybe user} 
 | Bottom {note_::Maybe user} 

data Normal
data Basic      -- denotes a Basic Narrowing derivation

type GT user r s  = GT_ user Normal r s

genVar, skolem :: Int -> GT_ user mode r s
isGenVar, isMutVar, isCtxVar, isTerm :: GT_ user mode r s -> Bool
fresh   :: ST r (GT_ user mode r s)
isGT    :: GT user r s -> GT user r s
note    :: GT_ user mode r s -> Maybe user
setNote :: user -> GT_ user mode r s -> GT_ user mode r s


instance TermShape s =>  Term (GT_ user mode r) s user