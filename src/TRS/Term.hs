{-# LANGUAGE MultiParamTypeClasses, ScopedTypeVariables #-}
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
import Data.Traversable (Traversable, mapM, traverse)
import Text.PrettyPrint
import Prelude hiding (sequence, concatMap, mapM)
import qualified Prelude

import TRS.Rules
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

rootSymbol :: (T id :<: f) => Term f -> Maybe id
rootSymbol t | Just (T root _) <- open t = Just root
             | otherwise = Nothing


isConstructor :: (HashConsed s, Zip s, Foldable s, f :<: s, IsVar s) => [Rule f] -> Term s -> Bool
isConstructor rules t
  | isVar t   = True
  | otherwise = all (\(l:->_) -> isNothing $ zipTerm' l t) rules

--isDefined :: (T id :<: f, T id :<: s, IsVar s) => [Rule f] -> Term s -> Bool
isDefined rules = not . isConstructor rules

type Position = [Int]

(!) :: Foldable f => Term f -> Position -> Term f
In t ! (i:ii) = {-# SCC "!" #-}  (toList t !! (i-1)) ! ii
t    ! []     = t

-- | Updates the subterm at the position given
--   Note that this function does not guarantee success. A failure to substitute anything
--   results in the input term being returned untouched
updateAt  :: (Traversable f, HashConsed f) =>  Position -> Term f -> Term f -> Term f
updateAt [] _ t' = t'
updateAt (0:_) _ _ = error "updateAt: 0 is not a position!"
updateAt (i:ii) t' (In t) = {-# SCC "updateAt" #-}
                            hashCons $
                            In$ fmap (\(j,st) -> if i==j then updateAt ii t' st else st)
                                (unsafeZipG [1..] t)

-- TODO: simplify this code so that the monadPlus constraint does not float out by internally fixing the monad to lists
updateAt'  :: (Traversable f, HashConsed f, Monad m) =>
              Position -> Term f -> Term f -> m (Term f, Term f)
updateAt' pos x x' = {-# SCC "updateAt'" #-} 
                     maybe (fail "updateAt': invalid position") return
                        (go x pos >>= \(t',a) -> a >>= \v -> return (hashCons t',v))
  where
    go _      (0:_)  = fail "updateAt: 0 is not a position!"
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
        In$ Note ([], (inj$ T n [In (Note (i:p, t)) | (i, In(Note (p,t))) <- zip [1..] tt]))
instance (t  :<: f) => AnnotateWithPos t f where annotateWithPosF t = In $ Note ([], inj t)
instance ((a :+: b) :<: f, AnnotateWithPos a f, AnnotateWithPos b f) => AnnotateWithPos (a :+: b) f where
    annotateWithPosF (Inr x) = annotateWithPosF x
    annotateWithPosF (Inl y) = annotateWithPosF y


newtype WithNote note f a = Note (note, f a) deriving (Show)
instance Functor f  => Functor (WithNote note f)  where fmap f (Note (p, fx))   = Note (p, fmap f fx)
instance Foldable f => Foldable (WithNote note f) where foldMap f (Note (_p,fx)) = foldMap f fx
instance Traversable f => Traversable (WithNote note f) where traverse f (Note (p, fx)) = (Note . (,) p) <$> traverse f fx
instance (Functor f, Eq note, Eq (Term f)) => Eq (Term (WithNote note f)) where t1 == t2 = note t1 == note t2 && dropNote t1 == dropNote t2
instance (Functor f, Ord note, Ord (Term f)) => Ord (Term (WithNote note f)) where
    t1 `compare` t2 = case compare (note t1) (note t2) of
                        EQ -> compare (dropNote t1) (dropNote t2)
                        x  -> x
instance (Show note, Ppr t) => Ppr (WithNote note t) where pprF (Note (p,t)) = pprF t <> char '_' <> text (show p)
instance IsVar f => IsVar (WithNote note f) where
    isVarF (Note (_,t)) = isVarF t
    uniqueIdF (Note (_,t)) = uniqueIdF t

note :: Term (WithNote note f) -> note
note (In (Note (note,_))) = note

dropNote :: Functor f => Term (WithNote note f) -> Term f
dropNote = foldTerm f where f (Note (note,t)) = In t

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
replace dict = hashCons . foldTerm f where
    f t = fromMaybe (In t) $ lookup (In t) dict

-- Only 1st level subterms
someSubterm :: (Traversable f, Functor m, MonadPlus m) => (Term f -> m(Term f)) -> Term f -> m (Term f)
someSubterm f (In x) = msum (In <$$> interleaveM f return x)

-- ---------------
-- Creating terms
-- ---------------

term :: (T id :<: f, Eq id, HashConsed f) => id -> [Term f] -> Term f
term s = hashCons . inject . T s

term1 :: (T id :<: f, Eq id, HashConsed f) => id -> Term f -> Term f
term1 f t       = term f [t]
term2 :: (T id :<: f, Eq id, HashConsed f) => id -> Term f -> Term f -> Term f
term2 f t t'    = term f [t,t']
term3 :: (T id :<: f, Eq id, HashConsed f) => id -> Term f -> Term f -> Term f -> Term f
term3 f t t' t''= term f [t,t',t'']
constant :: (T id :<: f, Eq id, HashConsed f) => id -> Term f
constant f      = term f []

x,y :: (HashConsed f, Var :<: f) => Term f
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
    pprF (T n tt) = text (show n) <> parens (cat$ punctuate comma tt)

instance Ppr (T String) where
    pprF (T n []) = text n
    pprF (T n [x,y]) | not (any isAlpha $ n) = x <+> text n <+> y
    pprF (T n tt) = text n <> parens (cat$ punctuate comma tt)

instance Ppr Var where
    pprF (Var Nothing i)  = text$ showsVar 0 i ""
    pprF (Var (Just l) i) = text l -- <> char '_' <> int i
instance (Ppr a, Ppr b) => Ppr (a:+:b) where
    pprF (Inr x) = pprF x
    pprF (Inl y) = pprF y

instance Ppr f => Show (Term f) where show = render . ppr
