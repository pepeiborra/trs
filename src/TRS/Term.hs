{-# LANGUAGE CPP #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE PatternGuards #-}


module TRS.Term where

import Control.Applicative
import Control.Arrow ((***))
import Control.Monad hiding ( mapM, sequence, msum)
import Data.Foldable (toList, Foldable, msum, foldMap)
import Data.Char (isAlpha)
import Data.Maybe
import Data.Monoid
import Data.Traversable (Traversable, mapM, traverse)
import Text.PrettyPrint
import Prelude hiding (sequence, concatMap, mapM)
import qualified Prelude

import TRS.Rules
import TRS.Types
import TRS.Utils hiding ( parens )

#ifdef HOOD
import Debug.Observe
#endif

subterms, properSubterms, directSubterms :: (Functor f, Foldable f) => Term f -> [Term f]
subterms (In t) = hIn t : {-# SCC "subterms" #-}
                  concat (subterms <$> toList t)
properSubterms = {-# SCC "properSubterms" #-}
                 tail . subterms
directSubterms (In t) = toList t

------------------------------------
-- * Inspecting and modifying terms
------------------------------------

rootSymbol :: (T id :<: f) => Term f -> Maybe id
rootSymbol t | Just (T root _) <- open t = Just root
             | otherwise = Nothing


type Position = [Int]

positions :: (Functor f, Foldable f) => Term f -> [Position]
positions = foldTerm f where f x = [] : concat (Prelude.zipWith (\i pp -> map (i:) pp) [1..] (toList x))

(!) :: Foldable f => Term f -> Position -> Term f
In t ! (i:ii) = {-# SCC "!" #-}  (toList t !! (i-1)) ! ii
t    ! []     = t

-- | Updates the subterm at the position given
--   Note that this function does not guarantee success. A failure to substitute anything
--   results in the input term being returned untouched
updateAt  :: (Traversable f, HashConsed f) =>  Position -> Term f -> (Term f -> Term f) -> Term f
updateAt [] t f = f t
updateAt (0:_) _ _ = error "updateAt: 0 is not a position!"
updateAt (i:ii) (In t) f = {-# SCC "updateAt" #-}
                            hIn$ fmap (\(j,st) -> if i==j then updateAt ii st f else st)
                                (unsafeZipG [1..] t)

-- TODO: simplify this code so that the monadPlus constraint does not float out by internally fixing the monad to lists
updateAt'  :: (Traversable f, HashConsed f, Monad m) =>
              Position -> Term f -> (Term f -> Term f) -> m (Term f, Term f)
updateAt' pos x f = {-# SCC "updateAt'" #-}
                     maybe (fail "updateAt': invalid position") return
                        (go x pos >>= \(t',a) -> a >>= \v -> return (t',v))
  where
    go _      (0:_)  = fail "updateAt: 0 is not a position!"
    go (In t) (i:is) = fmap ((hIn***msum) . unzipG)
                     . mapM  (\(j,u)->if i==j
                                       then go u is
                                       else return (u, mzero))
                     . unsafeZipG [1..]
                     $ t
    go x [] = return (f x, return x)
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
   appendPos p (In (Note (p', t'))) = hIn (Note (p++p', t'))

class (t :<: f) => AnnotateWithPos t f where annotateWithPosF :: t (Term (WithNote Position f)) -> Term (WithNote Position f)
instance (T id :<: f) => AnnotateWithPos (T id) f where
    annotateWithPosF (T n tt) =
        hIn$ Note ([], (inj$ T n [hIn (Note (i:p, t)) | (i, In(Note (p,t))) <- zip [1..] tt]))
instance (t  :<: f) => AnnotateWithPos t f where annotateWithPosF t = hIn $ Note ([], inj t)
instance ((a :+: b) :<: f, AnnotateWithPos a f, AnnotateWithPos b f) => AnnotateWithPos (a :+: b) f where
    annotateWithPosF (Inr x) = annotateWithPosF x
    annotateWithPosF (Inl y) = annotateWithPosF y


instance (Functor f, Eq note, Eq (Term f)) => Eq (Term (WithNote note f)) where t1 == t2 = dropNote t1 == dropNote t2
instance (Functor f, Ord note, Ord (Term f)) => Ord (Term (WithNote note f)) where t1 `compare` t2 = compare (dropNote t1) (dropNote t2)
instance (Show note, Ppr t) => Ppr (WithNote note t) where pprF (Note (p,t)) = pprF t <> char '_' <> text (show p)
instance IsVar f => IsVar (WithNote note f) where
    isVarF (Note (_,t)) = isVarF t
    uniqueIdF (Note (_,t)) = uniqueIdF t

instance (Zip f, Monoid note) => Zip (WithNote note f) where
    fzipWith f (Note (n1,x)) (Note (n2,y)) = fzipWith f x y >>= \xy -> return $ Note (n1 `mappend` n2, xy)

note :: Term (WithNote note f) -> note
note (In (Note (note,_))) = note

dropNote :: Functor f => Term (WithNote note f) -> Term f
dropNote = foldTerm f where f (Note (note,t)) = hIn t

isLinear :: (Var :<: s, Foldable s, Functor s) => Term s -> Bool
isLinear t = length(snub vars) == length vars where vars = [ v | u <- subterms t, Just v@Var{} <- [TRS.Types.open u]]

vars :: (Var :<: s, Foldable s, Functor s) => Term s -> [Var (Term s)]
vars t = {-# SCC "vars" #-}
         snub [ v | u <- subterms t, Just v@Var{} <- [TRS.Types.open u]]

vars' :: (IsVar s, Ord (Term s), Foldable s, Functor s) => Term s -> [Term s]
vars' t = {-# SCC "vars" #-}
         snub [ u | u <- subterms t, isVar u]

collect :: (Foldable f, Functor f) => (Term f -> Bool) -> Term f -> [Term f]
collect pred t = {-# SCC "collect" #-} [ u | u <- subterms t, pred u]

-- | Replace (syntactically) subterms using the given dictionary
--   Do not confuse with substitution application. @replace@ makes no
--   effort at avoiding variable capture
--   (you could deduce that from the type signature)
replace :: (Eq (Term f), Functor f, HashConsed f) => [(Term f, Term f)] -> Term f -> Term f
replace []   = id
replace dict = foldTerm f where
    f t = fromMaybe (hIn t) $ lookup (hIn t) dict

-- Only 1st level subterms
someSubterm :: (Traversable f, MonadPlus m) => (Term f -> m(Term f)) -> Term f -> m (Term f)
someSubterm f (In x) = msum ((liftM.liftM) hIn (interleaveM f return x))

-- ---------------
-- Creating terms
-- ---------------

term :: (T id :<: f, Eq id) => id -> [Term f] -> Term f
term s = inject . T s

termHc :: (T id :<: f, Eq id, HashConsed f) => id -> [Term f] -> Term f
termHc s = inject . T s

term1 :: (T id :<: f, Eq id, HashConsed f) => id -> Term f -> Term f
term1 f t       = termHc f [t]
term2 :: (T id :<: f, Eq id, HashConsed f) => id -> Term f -> Term f -> Term f
term2 f t t'    = termHc f [t,t']
term3 :: (T id :<: f, Eq id, HashConsed f) => id -> Term f -> Term f -> Term f -> Term f
term3 f t t' t''= termHc f [t,t',t'']
constant :: (T id :<: f, Eq id, HashConsed f) => id -> Term f
constant f      = termHc f []

x,y :: (Var :<: f) => Term f
x = var 0
y = var 1


-- ----------------------
-- Pretty Printing terms
-- ----------------------

class Functor f => Ppr f where pprF :: f Doc -> Doc
ppr :: Ppr f => Term f -> Doc
ppr = foldTerm pprF

instance Show id => Ppr (T id) where
    pprF (T n []) = text (show n)
    pprF (T n [x,y]) | not (any isAlpha $ show n) = x <+> text (show n) <+> y
    pprF (T n tt) = text (show n) <> parens (hcat$ punctuate comma tt)

instance Ppr (T String) where
    pprF (T n []) = text n
    pprF (T n [x,y]) | not (any isAlpha $ n) = x <+> text n <+> y
    pprF (T n tt) = text n <> parens (hcat$ punctuate comma tt)

instance Ppr Var where
    pprF (Var (Just l) i) = text l -- <> char '_' <> int i
--    pprF (Var _ i)  = text$ showsVar 0 i ""
    pprF (Var _ i)  = char 'v' <> int i
instance (Ppr a, Ppr b) => Ppr (a:+:b) where
    pprF (Inr x) = pprF x
    pprF (Inl y) = pprF y

instance Ppr f => Show (Term f) where show = render . ppr

-- --------------
-- Hood instances
-- --------------
#ifdef HOOD
instance Ppr f => Observable (Term f) where observer = observeBase
#endif HOOD