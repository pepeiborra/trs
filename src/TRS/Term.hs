{-# OPTIONS_GHC -fglasgow-exts #-}
{-# OPTIONS_GHC -fallow-undecidable-instances #-}
{-# OPTIONS_GHC -fallow-overlapping-instances #-}
{-# OPTIONS_GHC -fno-mono-pat-binds #-}

module TRS.Term where

import Control.Arrow ((***))
import Control.Monad hiding ( mapM, sequence, msum)
import qualified Data.AlaCarte
import Data.AlaCarte hiding (match)
import Data.Foldable (toList, Foldable, msum)
import Data.Maybe
import Data.Traversable (Traversable, mapM)
import Prelude hiding (sequence, concatMap, mapM)
import qualified Prelude

import TRS.Types
import TRS.Utils

------------------------------------
-- * Inspecting and modifying terms
------------------------------------

type Position = [Int]

(!) :: Foldable f => Term f -> Position -> Term f
In t ! (i:ii) = (toList t !! i) ! ii
t    ! []     = t

-- | Updates the subterm at the position given
--   Note that this function does not guarantee success. A failure to substitute anything
--   results in the input term being returned untouched
updateAt  :: (Traversable f) =>  Position -> Term f -> (Term f -> Term f)
updateAt [] _ t' = t'
updateAt (0:_) _ _ = error "updateAt: 0 is not a position!"
updateAt (i:ii) t' (In t) = In$ fmap (\(j,st) -> if i==j then updateAt ii t' st else st)
                                (unsafeZipG [1..] t)
updateAt _ _ x = x

updateAt'  :: (Traversable f, MonadPlus m, Functor m) => Position -> Term f -> (Term f -> m (Term f, Term f))
updateAt' pos x x' = go x pos >>= \ (t',a) -> a >>= \v->return (t',v)
  where
    go _      (0:_)  = error "updateAt: 0 is not a position!"
    go (In t) (i:is) = fmap ((In***msum) . unzipG)
                     . mapM  (\(j,u)->if i==j
                                       then go u is
                                       else return (u, mzero))
                     . unsafeZipG [1..]
                     $ t
    go x [] = return (x', return x)

vars :: (Var :<: s, Foldable s, Functor s) => Term s -> [Var (Term s)]
vars t = snub [ v | u <- subterms t, let Just v@Var{} = Data.AlaCarte.match u]

collect :: (Foldable f, Functor f) => (Term f -> Bool) -> Term f -> [Term f]
collect pred t = [ u | u <- subterms t, pred u]

-- | Replace (syntactically) subterms using the given dictionary
--   Do not confuse with substitution application. @replace@ makes no
--   effort at avoiding variable capture
--   (you could deduce that from the type signature)
replace :: (Eq (Term f), Functor f) => [(Term f, Term f)] -> Term f -> Term f
replace []   = id
replace dict = foldTerm f where
    f t = fromMaybe (In t) $ lookup (In t) dict

-- Only 1st level children
someSubterm :: (Traversable f, Functor m, MonadPlus m) => (Term f -> m(Term f)) -> Term f -> m (Term f)
someSubterm f (In x) = msum (In <$$> interleaveM f return x)
