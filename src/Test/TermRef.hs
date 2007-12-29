{-# OPTIONS_GHC -fglasgow-exts -fno-mono-pat-binds -fallow-undecidable-instances #-}
{-# OPTIONS_GHC -fallow-overlapping-instances #-}

module Test.TermRef where
import Control.Applicative
import Control.Exception (assert)
import Control.Monad hiding (mapM, sequence )
import Data.Traversable
import Text.PrettyPrint
import Data.Char (isAlpha)
import Data.Foldable
import Prelude hiding ( all, maximum, minimum, any, mapM_,mapM, foldr, foldl
                      , sequence, concat, concatMap )
import GHC.Exts (unsafeCoerce#)
import TypePrelude

import TRS
import TRS.GTerms
import TRS.Utils
import TRS.Tyvars
import TRS.Core ( semEq )

type TermRef s = TermRef_ Int s
type BasicTerm = TermRef BasicShape
type RuleS s   = Rule TermRef   s

data TermRef_ i s = Term (s (TermRef_ i s)) | Var i | Ref (TermRef_ i s)

instance (TermShape s, Eq i) => Eq (TermRef_ i s) where
  Var i  == Var j  = i == j
  Term s == Term t | Just pairs <- matchTerm s t
                   = all (uncurry (==)) pairs
  _      == _      = False 


t :: TermShape s => s(TermRef s) -> TermRef s
t      = Term

wrapRef (Ref t) = Ref t
wrapRef t = Ref t

isTermRef :: TermRef s -> TermRef s
isTermRef = id

liftS f (Term t) = Term (f t)
liftS2 (*) (Term t) (Term v) = Term (t*v)

stripRefs :: TermShape s => TermRef_ i s -> TermRef_ i s
stripRefs (Term s) = Term (stripRefs <$> s)
stripRefs t@Var{}  = t
stripRefs (Ref t)  = stripRefs t

instance (Show (s(TermRef_ i s)), Integral i) => Show (TermRef_ i s) where
  showsPrec p (Term s) = showsPrec p s
  showsPrec p (Var i)  = showsVar p i
  showsPrec p (Ref s)  = ('{' :) . showsPrec p s . ('}' :)

{-
instance (Show (s (TermRef s))) => Show (TermRef s) where
    showsPrec p (Term s) = showsPrec p s
    showsPrec p (Var  i) = showsVar p i 
-}
instance (Eq (TermRef s), Ord (s(TermRef s))) => Ord (TermRef s) where
  compare (Term s) (Term t) = compare s t
  compare Term{} _          = GT
  compare (Var i) (Var j)   = compare i j

-- ---------------------------------------
-- TermRef Term structure
-- ---------------------------------------
instance (TermShape s, Traversable s, Eq i, Integral i) => 
    Term (TermRef_ i) s user where
  isVar Var{} = True 
  isVar _     = False
  mkVar       = Var . fromIntegral 
  varId(Var i)= Just (fromIntegral i)
  varId _     = Nothing
  contents (Term tt) = Just tt
  contents (Ref   t) = contents t    -- ???
  contents _         = Nothing
  build              = Term 
  toGTM mkV (Ref t) = do
      t' <- toGTM mkV t
      v  <- fresh Nothing
      sequence(writeVar (TRS.GTerms.ref v) <$> t')
      return2 v
  toGTM mkV t = defaultToGTM mkV t