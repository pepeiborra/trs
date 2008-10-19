{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts, UndecidableInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE NoMonoPatBinds, NoMonomorphismRestriction #-}


module TRS.Term where

import Control.Applicative
import Control.Arrow ((***))
import Control.Monad hiding ( mapM, sequence, msum)
import Data.Foldable (toList, Foldable, msum)
import Data.Maybe
import Data.Traversable (Traversable, mapM)
import Text.PrettyPrint
import Prelude hiding (sequence, concatMap, mapM)
import qualified Prelude

import TRS.Types
import TRS.Utils hiding ( parens )


subterms, properSubterms :: (Functor f, Foldable f) => Term f -> [Term f]
subterms (In t) = In t : {-# SCC "subterms" #-}
                  concat (subterms <$> toList t)
properSubterms = {-# SCC "properSubterms" #-}
                 tail . subterms

------------------------------------
-- * Inspecting and modifying terms
------------------------------------

type Position = [Int]

(!) :: Foldable f => Term f -> Position -> Term f
In t ! (i:ii) = {-# SCC "!" #-}  (toList t !! i) ! ii
t    ! []     = t

-- | Updates the subterm at the position given
--   Note that this function does not guarantee success. A failure to substitute anything
--   results in the input term being returned untouched
updateAt  :: (Traversable f) =>  Position -> Term f -> (Term f -> Term f)
updateAt [] _ t' = t'
updateAt (0:_) _ _ = error "updateAt: 0 is not a position!"
updateAt (i:ii) t' (In t) = {-# SCC "updateAt" #-}
                            In$ fmap (\(j,st) -> if i==j then updateAt ii t' st else st)
                                (unsafeZipG [1..] t)

updateAt'  :: (Traversable f, MonadPlus m, Functor m) => Position -> Term f -> (Term f -> m (Term f, Term f))
updateAt' pos x x' = {-# SCC "updateAt'" #-} go x pos >>= \ (t',a) -> a >>= \v->return (t',v)
  where
    go _      (0:_)  = error "updateAt: 0 is not a position!"
    go (In t) (i:is) = fmap ((In***msum) . unzipG)
                     . mapM  (\(j,u)->if i==j
                                       then go u is
                                       else return (u, mzero))
                     . unsafeZipG [1..]
                     $ t
    go x [] = return (x', return x)
{-
findIn :: Term f -> Term f -> [Position]
findIn t = fmap fst . collect (==t) . annotateWithPos
    where annotateWithPos = annotateWithPos
-}

annotateWithPos :: AnnotateWithPos f f => Term f -> Term (WithNote Position f)
annotateWithPos = {-# SCC "annotateWithPos" #-} mergePositions . foldTerm annotateWithPosF where
   mergePositions :: Functor f => Term (WithNote Position f) -> Term (WithNote Position f)
   mergePositions = foldTermTop f
   f (Note (p,t))  = Note (p, fmap (appendPos p) t)
   appendPos p (In (Note (p', t'))) = In (Note (p++p', t'))

class (t :<: f) => AnnotateWithPos t f where annotateWithPosF :: t (Term (WithNote Position f)) -> Term (WithNote Position f)
instance (T id :<: f) => AnnotateWithPos (T id) f where
    annotateWithPosF (T n tt) =
        In$ Note ([], (inj$ T n [In (Note (i:p, t)) | (i, In(Note (p,t))) <- zip [0..] tt]))
instance (t  :<: f) => AnnotateWithPos t f where annotateWithPosF t = In $ Note ([], inj t)
instance ((a :+: b) :<: f, AnnotateWithPos a f, AnnotateWithPos b f) => AnnotateWithPos (a :+: b) f where
    annotateWithPosF (Inr x) = annotateWithPosF x
    annotateWithPosF (Inl y) = annotateWithPosF y

instance (Show note, Ppr t) => Ppr (WithNote note t) where pprF (Note (p,t)) = parens(text (show p) <> comma <> pprF t)

vars :: (Var :<: s, Foldable s, Functor s) => Term s -> [Var (Term s)]
vars t = {-# SCC "vars" #-}
         snub [ v | u <- subterms t, Just v@Var{} <- [TRS.Types.match u]]

collect :: (Foldable f, Functor f) => (Term f -> Bool) -> Term f -> [Term f]
collect pred t = {-# SCC "collect" #-} [ u | u <- subterms t, pred u]

-- | Replace (syntactically) subterms using the given dictionary
--   Do not confuse with substitution application. @replace@ makes no
--   effort at avoiding variable capture
--   (you could deduce that from the type signature)
replace :: (Eq (Term f), Functor f) => [(Term f, Term f)] -> Term f -> Term f
replace []   = id
replace dict = foldTerm f where
    f t = fromMaybe (In t) $ lookup (In t) dict

-- Only 1st level subterms
someSubterm :: (Traversable f, Functor m, MonadPlus m) => (Term f -> m(Term f)) -> Term f -> m (Term f)
someSubterm f (In x) = msum (In <$$> interleaveM f return x)

-- ---------------
-- Creating terms
-- ---------------

term :: (T id :<: f) => id -> [Term f] -> Term f
term s = inject . T s

term1 :: (T id :<: f) => id -> Term f -> Term f
term1 f t       = term f [t]
term2 :: (T id :<: f) => id -> Term f -> Term f -> Term f
term2 f t t'    = term f [t,t']
term3 :: (T id :<: f) => id -> Term f -> Term f -> Term f -> Term f
term3 f t t' t''= term f [t,t',t'']
constant :: (T id :<: f) => id -> Term f
constant f      = term f []

x,y :: (Var :<: f) => Term f
(x,y) = (var 0, var 1)
