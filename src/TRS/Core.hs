{-# OPTIONS_GHC -fglasgow-exts #-}
{-# OPTIONS_GHC -fallow-undecidable-instances #-}
{-# OPTIONS_GHC -fallow-overlapping-instances #-}
{-# OPTIONS_GHC -fbang-patterns  #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  TRS.Core
-- Copyright   :  (c) Pepe Iborra 2006-2007
--                (c) Universidad Politécnica de Valencia 2006-2007
-- License     :  All Rights Reserved
--
-- Maintainer  :  pepeiborra@gmail.org
-- Stability   :  experimental
-- Portability :  portable
--
-----------------------------------------------------------------------------


module TRS.Core (
  GoodShape, 
  mutableTerm,
  mutableTermG,
  col,
  Prune(..),
  noMVars, noGVars, noCVars,
  generalize,
  generalizeG,
  generalizeGG,
  narrowFull, narrowFullBounded,
  run, runG, runG', runGG, runIO,
  runE, runEG, runEGG, runEIO,
  runM, runMG, runMGG, runMIO,
  runL, runLG, runLGG, runLIO,
  runSTWithSubst,
  zonkSubst, isRenaming,
  semEq, semEq', semEqG
 -- for testing:
  ,autoInst, autoInstG
  ,dupTermWithSubst
  ,Instan(..)
)
 where

{- TODO
  
  - Why SubstG is the general type and Subst, used only internally,
    is the 'nice' concretization? Nice names should be reserved for 
    public API, in prejudice of internal implementation artifacts
 
-}

import Control.Applicative
import Control.Arrow ( first, second, (>>>), (***))
import Control.Exception (handle)
import Control.Monad hiding (msum, mapM_, mapM, sequence, forM)
import Control.Monad.Error (MonadError(..), ErrorT(..), MonadTrans(..))
import Control.Monad.State (StateT(..), MonadState(..), gets, modify, lift)
import Control.Monad.Fix (MonadFix(..))
import Control.Monad.List (runListT, ListT)
import Control.Monad.Writer (tell, execWriterT, WriterT)
import qualified Control.Monad.LogicT as LogicT hiding (runM)
import qualified Control.Monad.LogicT.SFKT as LogicT
import qualified Control.Monad.LogicT.SVCOT as LogicT'
import Control.Exception (assert)
import qualified Data.Set as Set
import Test.QuickCheck (Arbitrary(..))
import Data.List ((\\), nub, nubBy, elemIndex)
import qualified Data.List as List
import Data.Traversable
import Data.Foldable
import Data.Maybe 
import Data.Monoid
import MaybeT
import Prelude hiding ( all, maximum, minimum, any, mapM_,mapM, foldr, foldl
                      , and, concat, concatMap, sequence, elem, notElem)

import TRS.Substitutions
import TRS.Types hiding (Term)
import qualified TRS.Types
import TRS.Term  hiding (TRS(..), TRSN(..), templateTerm)
import qualified TRS.Term as Term
import {-# SOURCE #-} TRS.Terms
import TRS.Context
import TRS.Utils
import TRS.GTerms
import TRS.Rules
import TRS.Tyvars

import TypePrelude
import TypeCastGeneric

import GHC.Exts (unsafeCoerce#)
import Observe
import qualified Debug.Trace

instance TermShape s => Eq (GT r s) where
  (==) = synEq   -- syntactic equality

instance Eq (GT r s) => Eq (GT_ Basic r s) where
  t == s = idGT t == idGT s

{-# SPECIALIZE prune_ :: GT r BasicShape -> ST r (GT r BasicShape) #-}

type Subst r s = Subst_ Semantic r s
type Subst_ mode r s    = TRS.Substitutions.SubstM (GT_ mode r s)
--type RawSubst mode r s  = TRS.Substitutions.SubstG (GT_ mode r s)
type Rule_ mode r s = Rule (GT_ mode r) s

templateTerm :: Term t s => t s -> GT_ mode r s
templateTerm = freeGT . Term.templateTerm

mutableTerm :: Term t s => t s -> ST r (GT r s)
--mutableTerm = mkGTM . templateTerm  WRONG!
mutableTerm = (snd <$>) . autoInst . templateTerm

mkMutVar :: Term t s => t s -> ST r (GT r s)
mkMutVar = maybe (error "mkMutVar") mutVar . varId

mutableTermG :: (Traversable f, Term t s) => f(t s) -> ST r (f(GT r s))
mutableTermG = fmap snd . autoInstG . fmap templateTerm

noCVars, noGVars, noMVars :: (TermShape s, Foldable s) => GT_ mode r s -> Bool
noGVars = null . collect isGenVar 
noMVars = null . collect isMutVar 
noCVars = null . collect isCtxVar

{- SPECIALIZE rewrite1 :: OmegaPlus Semantic MaybeT r BasicShape => 
              [Rule BasicShape] -> GTE r BasicShape -> MaybeT (ST r) (GTE r BasicShape)#-}
-- |leftmost outermost
rewrite1  :: (Term t s, OmegaPlus Semantic m r s) => 
            [Rule t s] -> GTE r s -> m (ST r) (GTE r s)
rewrite1 rre = rewrite1_ (fixRules rre)

-- |leftmost outermost
rewrite   :: (Term t s, OmegaPlus Semantic m r s) => 
            [Rule t s] -> GTE r s -> m (ST r) (GTE r s)
rewrite  rre = rewrite_ (fixRules rre)

-- |leftmost outermost
narrow1   :: (Term t s, OmegaPlus Semantic m r s) => 
            [Rule t s] -> GTE r s -> 
             m (ST r) (Subst_ Semantic r s, GTE r s)
narrow1 rr = narrow1_ (fixRules rr)

{-
-- |leftmost outermost
narrow1' :: (Term t s, GoodShape s) => 
           [Rule t s] -> GTE r s -> ST r [(Subst r s, GTE r s)]
narrow1' rr = narrow1'_ (fixRules rr)
-}

-- |leftmost outermost, in variables too
narrow1V :: (Term t s, GoodShape s) => 
           [Rule t s] -> GTE r s -> ST r [(Subst r s, GTE r s)]
narrow1V rr = narrow1V_ (fixRules rr)

narrowFull :: (Term t s, GoodShape s) => 
             [Rule t s] -> GTE r s -> 
             ST r [(Subst r s, GTE r s)]
narrowFull rr = narrowFull_ (fixRules rr)

narrowFullV :: (Term t s, GoodShape s) => 
              [Rule t s] -> GTE r s -> ST r [(Subst r s, GTE r s)]
narrowFullV rr = narrowFullV_ (fixRules rr)

narrowBasic :: (Term t s, GoodShape s) => [Rule t s] -> GT_ Basic r s -> 
             ST r [(Subst_ Basic r s, GT_ Basic r s)]
narrowBasic rr term = narrowBasic_ (fixRules rr) 
                            (basicGT$ templateTerm term)

narrowFullBounded  :: (Term t s, GoodShape s) => 
                      (GTE r s -> ST r Bool) -> [Rule t s] -> GTE r s -> 
                      ST r [(Subst r s, GTE r s)]
narrowFullBounded pred rr = narrowFullBounded_ (pred . eqGT) (fixRules rr)

narrowFullBoundedV :: (Term t s, GoodShape s) => 
                      (GTE r s -> ST r Bool) -> [Rule t s] -> GTE r s -> 
                      ST r [(Subst r s, GTE r s)]
narrowFullBoundedV pred rr = narrowFullBoundedV_ (pred . eqGT) (fixRules rr)

-- | generalize builds a sigma type, i.e. a type scheme, by 
--   replacing all mutvars in a term with GenVars
generalize ::(Prune mode, TermShape s) => GT_ mode r s -> ST r (GT_ mode r s)
generalizeG::(Prune mode, TermShape s,Traversable f) => 
               f(GT_ mode r s) -> ST r (f(GT_ mode r s))
generalizeGG::(Prune mode, TermShape s, Traversable f, Traversable f') => 
               f'(f(GT_ mode r s)) -> ST r (f'(f(GT_ mode r s)))


rewrite1_ :: OmegaPlus mode m r s => [Rule_ mode r s] -> GT_ mode r s -> m (ST r) (GT_ mode r s)
rewrite_  :: OmegaPlus mode m r s => [Rule_ mode r s] -> GT_ mode r s -> m (ST r) (GT_ mode r s)
narrow1_  :: OmegaPlus mode m r s => [Rule_ mode r s] -> GT_ mode r s -> 
             m (ST r) (Subst_ mode r s, GT_ mode r s)

--narrow1'_ :: (GoodShape s, Prune mode) => [Rule_ mode r s] -> GT_ mode r s 
--             -> ST r [(Subst_ mode r s, GT_ mode r s)]

-- |leftmost outermost, on variables too (paramodulation)
narrow1V_ :: (GoodShape s, Prune mode) => [Rule_ mode r s] -> GT_ mode r s 
             -> ST r [(Subst_ mode r s, GT_ mode r s)]

-- |Unbounded Full Narrowing
narrowFull_ :: (Prune mode, Eq (GT_ mode r s), GoodShape s) => [Rule_ mode r s] -> GT_ mode r s -> 
             ST r [(Subst_ mode r s, GT_ mode r s)]

-- |Unbounded Full Paramodulation
narrowFullV_ :: (Prune mode, GoodShape s) => 
              [Rule_ mode r s] -> GT_ mode r s -> ST r [(Subst_ mode r s, GT_ mode r s)]

-- | Bounded versions. The first argument is the bound checking predicate
narrowFullBounded_ :: (Prune mode, GoodShape s) =>
                      (GT r s -> ST r Bool) -> [Rule_ mode r s] -> GT_ mode r s -> 
                      ST r [(Subst_ mode r s, GT_ mode r s)]
narrowFullBoundedV_:: (Prune mode, GoodShape s) =>
                      (GT r s -> ST r Bool) -> [Rule_ mode r s] -> GT_ mode r s -> 
                      ST r [(Subst_ mode r s, GT_ mode r s)]

fixRules :: (Term t s, TermShape s, Functor s) => [Rule t s] -> [Rule_ mode r s]
fixRules = fmap2 templateTerm

-- * Basic primitives
{- SPECIALIZE unify :: Omega Semantic MaybeT r BasicShape => 
                            GT_ Semantic r BasicShape -> GT_ Semantic r BasicShape 
                         -> MaybeT (ST r) () #-}
{- SPECIALIZE unify :: Omega Semantic ListT r BasicShape => 
                            GT_ Semantic r BasicShape -> GT_ Semantic r BasicShape 
                         -> ListT (ST r) () #-}
unify	  :: Omega mode m r s => GT_ mode r s -> GT_ mode r s -> m (ST r) ()
match	  :: Omega mode m r s => GT_ mode r s -> GT_ mode r s -> m (ST r) ()

-----------------------------
-- * The machinery
------------------------------

class Prune (mode :: *) where 
    prune :: GT_ mode r s  -> ST r (GT_ mode r s)

instance Prune Basic     where prune x = pruneBasic_ x
instance Prune Syntactic where prune x = prune_ x
instance Prune Semantic  where 
    prune x = prune_ x
instance TypeEq Syntactic mode HTrue => Prune mode where prune x = prune_ x

{-# INLINE prune_ #-}
prune_ :: GT_ mode r s -> ST r (GT_ mode r s)
prune_ (typ @ (MutVar ref)) =
	do { m <- readVar ref
	   ; case m of
	      Just t ->
		do { newt <- prune_ t
		   ; write ref newt
		   ; return newt }
	      Nothing -> return typ}
prune_ x = return x

pruneBasic_ :: GT_ t t1 t2 -> ST t1 (GT_ t t1 t2)
pruneBasic_ (typ @ (MutVar ref)) =
	do { m <- readVar ref               -- One could make this block a one liner: 
	   ; case m of                      -- mapM (prune_ >=> write ref . Just)
	      Just t ->                      --     =<< readVar ref
		do { newt <- pruneBasic_ t       -- return typ
		   ; write ref newt  -- (note the mapM is in the Maybe monad)
		   ; return typ }
	      Nothing -> return typ}
pruneBasic_ x = return x

{-# SPECIALIZE col :: GT_ Syntactic r BasicShape -> ST r (GT_ Syntactic r BasicShape) #-}
{-# SPECIALIZE col :: GT_ Semantic r BasicShape -> ST r (GT_ Semantic r BasicShape) #-}
{-# SPECIALIZE col :: GT_ Basic r BasicShape -> ST r (GT_ Basic r BasicShape) #-}
col :: (Prune mode, Traversable s) => GT_ mode r s  -> ST r (GT_ mode r s)    
col x =
     do { x' <- prune x
	; case x' of
	  (S y) -> 
	    do { t <- (mapM col y) 
	       ; return (S t)} 
	  _     -> return x'}

occurs :: (Prune mode, MonadTrans t, Traversable s, Monad (t (ST r))) =>
         Ptr mode r s -> GT_ mode r s -> t (ST r) Bool
occurs v t =
     do { t2 <- lift$ prune t 
	; case t2 of 
	  S w -> 
	    do { s <- (mapM (occurs v) w) 
	       ; return(foldr (||) False s ) 
	       } 
	  MutVar z -> return (v == z) 
	  _ -> return False } 

unify tA tB = 
     do  t1 <- lift$ prune tA 
	 t2 <- lift$ prune tB 
	 case (t1,t2) of 
	   (MutVar r1,MutVar r2) -> 
	     if r1 == r2 
		then return () 
		else lift$ write r1 t2
	   (MutVar r1,_) -> varBind r1 t2 
	   (_,MutVar r2) -> varBind r2 t1 
	   (GenVar n,GenVar m) -> 
	    if n==m 
		then return () 
		else throwError genErrorUnify
	   (S x,S y) -> 
	     case matchTerm x y of
                Nothing    -> throwError genErrorUnify --(shapeErrorUnify tA tB)
		Just pairs -> 
		  mapM_ (uncurry unify) pairs 
	   (x,y) -> throwError genErrorUnify -- (shapeErrorUnify tA tB)

varBind :: Omega mode m r s => Ptr mode r s -> GT_ mode r s -> m (ST r) ()
varBind r1 t2 = 
     do { b <- occurs r1 t2 
	; if b 
	    then throwError occursError
	    else lift$ write r1 t2 }

match tA tB = 
     do { t1 <- lift$ prune tA 
	; t2 <- lift$ prune tB 
	; case (t1,t2) of 
	  (MutVar r1,_) -> 
	    lift$ write r1 t2
	  (GenVar n,GenVar m) -> 
	    if n==m 
		then return () 
		else throwError genErrorMatch
	  (S x,S y) -> 
	    case matchTerm x y of 
		Nothing -> throwError genErrorMatch
		Just pairs -> 
		  mapM_ (uncurry match) pairs 
	  (_,_) -> throwError shapeErrorMatch 
	} 

class Instan term subst monad | term -> monad where 
  instan :: subst -> term -> monad term

{-  
instance (Prune mode, Traversable s) => Instan (GT_ mode r s) (Subst_ mode r s) (ST r) where
  {- SPECIALIZE instance Instan (GT_ Syntactic r BasicShape) (Subst_ Syntactic r BasicShape) (ST r) #-}
  instan sub t = do --prune >=> instan sub . DontCol >=> col . unDontCol  
      t1 <- prune t
      DontCol t2 <- instan sub (DontCol t1)
      col t2
-}
newtype DontCol a = DontCol {unDontCol::a}
instance (Prune mode, Traversable s) => Instan (DontCol(GT_ mode r s)) (Subst_ mode r s) (ST r) where
  instan s (DontCol x) = DontCol <$> instanDontCol x
    where
     sub = fromSubstM s
     instanDontCol x = do
         { case x of 
	    GenVar n | n `atLeast` sub, Just val <- sub !! n -> return val
	    S x -> S <$> mapM instanDontCol x 
            _ -> return x
	 } 

{-
instance (Prune mode, Traversable s) => Instan (GT_ mode r s) (SubstI mode r s) (ST r) where
  instan s x = do
    let sub = fromSubstM s
    x' <- prune x
    case x' of
      GenVar n | Just val <- lookup n sub -> col $! val
      S x -> S <$> (instan s `mapM` x)
      _   -> return x'
-}
instance (Prune mode, Traversable s) => 
    Instan (GT_ mode r s) (Subst_ mode r s) (ST r) where
  instan sub x = 
      do { let vv = fromSubstM sub
         ; x' <- prune x 
	 ; case x' of 
	    GenVar n | n `atLeast` vv
                     , Just val <- vv !! n -> col $! val
	    S x -> S <$> mapM (instan sub) x
            _ -> return x'
	 } 
  

--generalize_ x | trace ("generalize " ++ show x ) False = undefined
generalize x = do
           x' <- col x
           let gvars = collect isGenVar x'
               mvars = collect isMutVar x'
               tot   = length gvars + length mvars
               new_gvars = map GenVar
                               ([0..tot]\\[j|GenVar j <- gvars])
           let x'' = replace (zip mvars new_gvars) x'
           assert (noMVars x'') (return ())
           return x''

generalizeG x = do
  x' <- mapM col x
  let gvars = nubSyntactically $ concat (toList (collect isGenVar <$> x'))
      mvars = nubSyntactically $ concat (toList (collect isMutVar <$> x'))
      tot   = length gvars + length mvars
      new_gvars = map GenVar ([0..tot]\\[j|GenVar j <- gvars])
      x''   = replace (zip mvars new_gvars) <$> x'
  assert (all noMVars x'') (return ())
  return x''

generalizeGG x = do
           x' <- mapM2 col x
           let gvars = nubSyntactically $ concat2 (toList2 (fmap2 (collect isGenVar) x'))
               mvars = nubSyntactically $ concat2 (toList2 (fmap2 (collect isMutVar) x'))
               tot   = length gvars + length mvars
               new_gvars = map GenVar
                               ([0..tot]\\[j|GenVar j <- gvars])
           let x'' = fmap2 (replace (zip mvars new_gvars)) x'
           assert (all (and . fmap noMVars) x'') (return ())
           return x''

nubSyntactically :: (Term t s) => [t s] -> [t s]
nubSyntactically = map unSynEq . nub . map SynEq

-- | autoInst instantitates a type scheme with fresh mutable vars
--   Returns the instantiated term together with the new MutVars 
--  (you need these to apply substitutions) 
{-# SPECIALIZE autoInst :: GT_ Syntactic r BasicShape -> 
                        ST r (SubstM (GT_ Syntactic r BasicShape), GT_ Syntactic r BasicShape) #-}
{-# SPECIALIZE autoInst :: GT_ Semantic r BasicShape -> 
                        ST r (SubstM (GT_ Semantic r BasicShape), GT_ Semantic r BasicShape) #-}
{-# SPECIALIZE autoInst :: GT_ Basic r BasicShape -> 
                        ST r (SubstM (GT_ Basic r BasicShape), GT_ Basic r BasicShape) #-}
autoInst :: (Prune mode, TermShape s) => 
            GT_ mode r s -> ST r (Subst_ mode r s, GT_ mode r s)       
autoInst x@MutVar{} = return (mempty, x)
autoInst x
    | null vv = return (mempty, x)
    | otherwise  = do
           subst <- mkSubstM vv <$> mapM mutVar vv
           x'    <- instan subst x
           assert (noGVars x') (return ())
           x' `seq` return (subst, x')
    where vv = nub [ i | GenVar i <- vars x]

autoInstG:: (Traversable s, Traversable f, TermShape s, Prune mode) =>
               f(GT_ mode r s) -> ST r (Subst_ mode r s, f(GT_ mode r s))
autoInstG xx | null vv = return (mempty, xx)
              | otherwise = do
  subst <- mkSubstM vv <$> mapM mutVar vv
  xx' <- instan subst `mapM` xx
  assert (all noGVars xx') (return ())
  return (subst, xx')
    where vv = snub [ i | GenVar i <- concatMap vars xx]


autoInstGG ::  (Instan (GT_ t r s) (Subst_ mode r s1) (ST r),
                 Traversable f,TermShape s) =>
               f [GT_ t r s] -> ST r (Subst_ mode r s1, f [GT_ t r s])
autoInstGG xx | null vv = return (mempty, xx)
              | otherwise = do
  subst <- mkSubstM vv <$> mapM mutVar vv
  xx'   <- instan subst `mapM2` xx
  return (subst, xx')
    where vv = snub [ i | GenVar i <- concatMap2 vars xx]

-- |Semantic equality (equivalence up to renaming of vars) 
semEq :: (Prune mode, TermShape s) => GT_ mode r s -> GT_ mode r s -> ST r Bool
semEq x y = do
    (_,x') <- autoInst x
    (_,y') <- autoInst y
    let xy_vars = collect isMutVar x' ++ collect isMutVar y'
    unified <- runMaybeT (unify x' y' >> return ())
    if isNothing unified 
       then return False
       else do
         mapM col xy_vars
         andM [ (maybe True isVar <$> readVar v)
                       | MutVar v <- xy_vars]

-- TODO Rewrite as in semEq
semEqG :: (Applicative f, Prune mode, Traversable f, TermShape s) =>
         f (GT_ mode r s) -> f (GT_ mode r s) -> ST r (f Bool)
semEqG x y = do
    [x',y'] <- mapM (autoInstG >=> (generalizeG . snd)) [x,y]
    return (synEq <$> x' <*> y')

-- isRenaming :: Subst_ mode r s -> ST r Bool
isRenaming :: (Term t s, GoodShape s) => SubstM (t s) -> Bool
isRenaming vv = all isVar [v | Just v <- fromSubstM vv]
--semEqG x y = return$ synEq x y

---------------------------------------------------------------
-- * Pure (partial) Semantic Equality for GTE 
--       (based on zonking to an equivalent TermStatic)
---------------------------------------------------------------
{-
instance TermShape s => Eq (GTE r s) where
  (==) = semEq'
-}
-- | Fails for terms with mutvars
---  TODO: I don't think this is very efficient
semEq' :: TermShape s => GT_ mode r s -> GT_ mode r s -> Bool
semEq' s t = fromMaybe False $ runST (runMaybeT $ do
  s' <- MaybeT$ (fmap join . sequence . fmap2 zonkTermS . fmap mutableTerm . zonkTermS) s
  t' <- MaybeT$ (fmap join . sequence . fmap2 zonkTermS . fmap mutableTerm . zonkTermS) t
  assert (noMVars s) $ assert (noMVars t) $ 
   return(s' `synEq` t'))

zonkTermS :: TermShape s => GT_ mode r s -> Maybe (TermStatic s)
zonkTermS = zonkTerm

zonkTermS' :: TermShape s => GT_ mode r s -> (TermStatic s)
zonkTermS' = zonkTermUnsafe

{-----------------------------------------------------
-- IDEAS FOR EFFICIENCY
-- Many-to-one matching algorithm (see SPJ87, Maranget2001)
-- Fuse autoInst and matching in a single pass
-- User the ATerm library from INRIA Nancy and the ELAN group
-----------------------------------------------------}

--rewrite1_ rr (S t) | trace ("rewrite " ++ show t ++ " with " ++  (show$ length rr) ++ " rules ") False = undefined
--rewrite1_ _ t | assert (noMVars t) False = undefined
rewrite1_ rules (S t)
      | otherwise
      = rewriteTop (S t) `mplus` (S <$> someSubterm (rewrite1_ rules) t) 
        where rewriteTop t = msum$ forEach rules $ \r@(lhs:->rhs) -> do
	        (freshv, lhs') <- lift$ autoInst lhs
	        match lhs' t
                lift$ instan freshv rhs

rewrite1_ _ t = mzero

rewrite_ rules = fixM (rewrite1_ rules)

--narrow1_ _ t | trace ("narrow1 " ++ show t) False = undefined
narrow1_ [] t = mzero -- fail1 "narrow1: empty set of rules"
narrow1_ _ t | assert (noMVars t) False = undefined
narrow1_ rules t@S{} = go (t, emptyC)
    where go (t, ct) = 
              narrowTop rules ct t
             `mplus` 
              msum [go (t, ct|>ct1) | (t, ct1) <- contexts t]
narrow1_ rules _ = mzero -- fail "narrow1: No Narrowing at vars"

narrowTop, narrowTopV :: OmegaPlus mode m r s =>
             [Rule_ mode r s] -> GT_ mode r s -> GT_ mode r s
          -> m (ST r) (Subst_ mode r s, GT_ mode r s)
narrowTop  rules ct t = assert (all noMVars [t, ct])$ unsafeNarrowTop rules ct t
narrowTopV rules ct t = assert (all noMVars [t, ct])$ unsafeNarrowTopV rules ct t

unsafeNarrowTop, unsafeNarrowTopV :: OmegaPlus mode m r s =>
                  [Rule_ mode r s] -> GT_ mode r s -> GT_ mode r s
                -> m (ST r) (Subst_ mode r s, GT_ mode r s)
unsafeNarrowTop   = unsafeNarrowTopG narrowTop1
unsafeNarrowTopV  = unsafeNarrowTopG narrowTop1V

unsafeNarrowTopG ::(Prune mode, TermShape s, MonadTrans t, MonadPlus (t (ST r))) =>
                  (GT_ mode r s -> a -> t (ST r) (GT_ mode r s))
                 -> [a] -> GT_ mode r s -> GT_ mode r s
                 -> t (ST r) (Subst_ mode r s, GT_ mode r s)
-- unsafeNarrowTopG _ _ _ t | trace ("unsafeNarrowTop " ++ show t) False = undefined
unsafeNarrowTopG narrowTop1 rules ct t = msum$ forEach rules $ \r -> do
               (vars, [t',ct']) <- lift$ autoInstG [t,ct]
               t''              <- narrowTop1 t' r
               return (vars, ct'|>t'')

narrowTop1, narrowTop1V :: OmegaPlus mode m r s => GT_ mode r s -> Rule_ mode r s 
                        -> m (ST r) (GT_ mode r s)
narrowTop1V t r@(lhs:->rhs) = do
               assert (noGVars t) (return ())
               assert (noMVars lhs) (return ())
               assert (noMVars rhs) (return ())
               assert (vars (idGT rhs) `isSubsetOf` vars (idGT lhs)) (return ())
               (lhsv, lhs') <- lift$ autoInst lhs
               unify lhs' t
               trace ("narrowing fired: t=" ++ st t ++ ", rule=" ++ sr r
--                   ++   ", rho= " ++ show (zonkTermS lhsv)
                      )(return ()) 
               rhs'  <- lift$ instan lhsv rhs
               rhs'' <- lift$ col rhs'      -- OPT: col here might be unnecesary
--             assert (noGVars rhs'') (return ())
               return rhs''
narrowTop1 t@S{} r = narrowTop1V t r
narrowTop1 _ _     = mzero -- throwError "No narrowing at vars"

-------------------------------
-- * The Full Narrowing Framework
-------------------------------
--narrow1'_ = narrowFullBase narrowTop'  (const (return True)) 
narrow1V_ = narrowFullBase narrowTopV' (const (return True)) 

narrowFull_  = narrowFullBounded_ (const (return False))
narrowBasic_ rules = narrowFull_ (fmap2 basicGT rules) . basicGT

narrowFullV_ = narrowFullBoundedV_ (const (return False))
narrowFullBounded_  = narrowFullBase narrowTop'
narrowFullBoundedV_ = narrowFullBase narrowTopV'

newtype Ind = Ind Int deriving (Num,Enum, Eq)
instance Show Ind where show (Ind i) = " (" ++ show i ++ ") "

narrowFullBase :: (Prune mode, Show (s (TermStatic s)), TermShape s) =>
                 ([t] -> Context mode r s -> Subst_ mode r s -> GT_ mode r s
                  -> LogicT.SFKT (ST r) (Subst_ mode r s, GT_ mode r s))
               -> (GT r s -> ST r Bool) -> [t] -> GT_ mode r s 
               -> ST r [(Subst_ mode r s, GT_ mode r s)]

--narrowFullBase _ done [] t = -- trace ("narrowFull " ++ show t ++ " with empty TRS")$ 
--                           return []
narrowFullBase narrowTop1base done rules t = do 
     assert (noMVars t) (return ())
     (subst0,t0) <- autoInst t
     -- nubByM (semEq `at` snd) =<< 
     LogicT.runM Nothing (search (Ind 0) (subst0, t0))
  where   
--   search :: (Subst r s, GT r s) -> LogicT'.SR r1 (ST r) (T2(Subst r s) (GT r s))
   search !ind (subst,t) = trace ("narrowFull search: " ++ show ind  ++ st t) $ 
       LogicT.ifte  (step emptyC subst t)
                    (\x@(sub',t') -> trace ("branch " ++ show ind ++ st t') $ 
                               lift (done (idGT t)) >>- \isDone -> 
                               if isDone 
                                then trace ("done" ++ st t') $
                                     return (sub',t') 
                                else 
                                   search (succ ind) x)
                    (trace ("leaf" ++ show ind ++ st t) $ 
                    return (subst,t))
   step cs subst t = trace ("narrowFull step: " ++ st cs ++ brackets (st t)) $
                   (narrowTop1base rules cs subst t
             `LogicT.interleave`
                   msum' (forEach (contexts t) $ \(ts,cs1) ->
                     step (cs|>cs1) subst ts))

{-
narrowTop', narrowTopV' :: OmegaPlus Syntactic m r s => 
                          [RuleI r s] -> Context r s
                        -> Subst r s -> GT r s
                        -> m (ST r) (Subst r s, GT r s)
-}

narrowTop' :: OmegaPlus mode m r s =>
             [Rule_ mode r s] -> GT_ mode r s -> Subst_ mode r s -> GT_ mode r s
           -> m (ST r) (Subst_ mode r s, GT_ mode r s)

narrowTop'  = narrowTopBase narrowTop1

narrowTopV' :: OmegaPlus mode m r s =>
              [Rule_ mode r s] -> GT_ mode r s -> Subst_ mode r s -> GT_ mode r s
            -> m (ST r) (Subst_ mode r s, GT_ mode r s)

narrowTopV' = narrowTopBase narrowTop1V

-- narrowTopBase' _ _ _ _  t | trace ("NarrowTop' " ++ show t) False = undefined
{-
narrowTopBase :: (Prune mode, MonadTrans t, MonadPlus (t (ST r)), TermShape s) =>
                (GT_ mode r s -> a -> t (ST r) (GT_ mode r s))
              -> [a] -> GT_ mode r s -> SubstG (GT_ mode r s) -> GT_ mode r s
              -> t (ST r) (SubstG (GT_ mode r s), GT_ mode r s)
-}
narrowTopBase _ _ ct _ t | assert(noGVars t) False = undefined
narrowTopBase _ _ ct _ t | assert(noGVars ct) False = undefined
narrowTopBase narrowTop1 rules ct subst t = msum$ forEach rules $ \r -> do
               (subst', [ct'], t') <- lift$ dupTermWithSubst subst [ct] t
               t'' <- narrowTop1 t' r
               ct'' <- lift$ col ct'
               return (subst', ct''|>t'')

--------------------------------
-- * Duplication of Terms
--------------------------------

-- TODO Repasar esta parte y arreglar para que trabaje con SubstM

dupVar :: STRef s a -> ST s (STRef s a)
dupVar sr = readSTRef sr >>= newSTRef
dupTerm :: (Traversable s) => GT_ eq r s -> ST r (GT_ eq r s)
dupTerm (MutVar r) = fmap MutVar (dupVar r)
dupTerm (S t) = fmap S $ mapM dupTerm t
dupTerm x = return x

dupTermWithSubst :: (Functor subst,  TermShape s) =>
                   subst(GT_ eq r s) -> [GT_ eq r s] -> GT_ eq r s
                -> ST r (subst(GT_ eq r s), [GT_ eq r s], GT_ eq r s)

--dupTermWithSubst subst tt x | trace "dupTermWithSubst" False = undefined
dupTermWithSubst subst tt t@MutVar{} = do
    t'        <- dupTerm t
    let dict   = [(t,t')]
        subst' = fmap (replace dict) subst
        tt'    = fmap (replace dict) tt
    return (subst', tt', t')

dupTermWithSubst subst tt t@S{} = do
    let mutvars= collect isMutVar t
    newvars   <- mapM dupTerm mutvars
    let dict   = zip mutvars newvars
        t'     = replace dict t
        tt'    = fmap (replace dict) tt
        subst' = fmap (replace dict) subst
    return (subst', tt', t')

dupTermWithSubst subst tt x = return (subst, tt, x)


------------------------------
-- * Obtaining the results
------------------------------
run :: (TermShape s, Show (s (GTE r s)), Term t s) => (forall r.ST r (GTE r s)) -> t s
run c | Just x <- runST (fmap zonkTerm c) = x
      | otherwise = error "A mutable variable was found in the result"

runG :: (TermShape s, Show (s (GTE r s)), Traversable f, Term t s) =>
         (forall r.ST r (f(GTE r s))) -> f(t s)
runG c | Just x <- sequence$ runST (fmap2 zonkTerm c) = x
       | otherwise = error "A mutable variable was found in the result"

runG' :: (TermShape s, Show (s (GTE r s)), Traversable f, Term t s) =>
         (forall r.ST r (f(GTE r s))) -> f(t s)
runG' c = runST (c >>= mapM zonkTerm') 


runGG :: (TermShape s, Show (s (GTE r s)), Traversable f, Traversable f1, Term t s) =>
         (forall r.ST r (f(f1(GTE r s)))) -> f(f1(t s))
runGG c | Just x <- sequence2$ runST ( (fmap3 zonkTerm c)) = x
        | otherwise = error "A mutable variable was found in the result"

runIO :: ST RealWorld a -> IO a
runIO = stToIO


runE :: (Omega Semantic (ErrorT (TRSException)) r s, Term t s) => 
        (forall r. ErrorT (TRSException) (ST r) (GTE r s)) -> t s
runE c | Just x <- runST ( either (error.show) id <$>
                              runErrorT (zonkTerm <$> c)) = x
       | otherwise = error "A mutable variable was found in the result"  

runEG :: (Omega Semantic (ErrorT (TRSException)) r s, Traversable f, Term t s) =>
         (forall r. ErrorT (TRSException) (ST r) (f(GTE r s))) -> f(t s)
runEG c | Just x <- sequence$ runST (either (error.show) id <$>
                                    (runErrorT (fmap2 zonkTerm c))) = x
        | otherwise = error "A mutable variable was found in the result"

runEGG :: (Omega Semantic (ErrorT (TRSException)) r s, Traversable f, Traversable f1, Term t s) =>
         (forall r. ErrorT (TRSException) (ST r) (f(f1(GTE r s)))) -> f(f1(t s))
runEGG c | Just x <- sequence2$ runST (either (error.show) id <$>
                                    (runErrorT (fmap3 zonkTerm c))) = x

runEIO :: ErrorT (TRSException) (ST RealWorld) a -> IO a
runEIO = fmap (either (error. show) id) . stToIO . runErrorT

-- runMaybeT = fmap (either (const Nothing) Just) . runErrorT

runM :: (Omega Semantic MaybeT r s, Term t s) => 
        (forall r. MaybeT (ST r) (GTE r s)) -> Maybe (t s)
runM c | Just x <- sequence$ runST (runMaybeT (fmap zonkTerm c)) = x

runMG :: (Omega Semantic MaybeT r s, Traversable f, Term t s) =>
         (forall r. MaybeT (ST r) (f(GTE r s))) -> Maybe (f(t s))
runMG c | Just x <- sequence2 $ runST(runMaybeT (fmap2 zonkTerm c)) = x

runMGG :: (Omega Semantic MaybeT r s, Traversable f, Traversable f1, Term t s)=>
         (forall r. MaybeT (ST r) (f(f1(GTE r s)))) -> Maybe (f(f1(t s)))
runMGG c | Just x <- sequence3$ runST(runMaybeT (fmap3 zonkTerm c)) = x

runMIO :: MaybeT (ST RealWorld) a -> IO (Maybe a)
runMIO = stToIO . runMaybeT



runL :: (Term t s, Omega Semantic (ListT') r s) => (forall r. ListT' (ST r) (GTE r s)) -> [t s]
runL c | Just x <- sequence$ runST (runListT' (fmap zonkTerm c)) = x

runLG :: (Omega Semantic (ListT') r s, Traversable f, Term t s) =>
         (forall r. ListT' (ST r) (f(GTE r s))) -> [f(t s)]
runLG c | Just x <- sequence2$ runST (runListT' (fmap2 zonkTerm c)) = x

runLGG :: (Omega Semantic (ListT') r s, Traversable f, Traversable f1, Term t s) =>
         (forall r. ListT' (ST r) (f(f1(GTE r s)))) -> [f(f1(t s))]
runLGG c | Just x <- sequence3$ runST (runListT' (fmap3 zonkTerm c)) = x

runLIO :: ListT' (ST RealWorld) a -> IO [a]
runLIO = stToIO . runListT'

-- ---------------------------------------------------
-- TRS instances
-- ---------------------------------------------------
instance (Term t s, GoodShape s) => Term.TRS t s [] where
  {-# SPECIALIZE instance Term.TRS (TermStatic_ Int) BasicShape [] #-}
  rewrite  rr t    = runL (rewrite rr (templateTerm t))
  rewrite1 rr t    = runL (rewrite1 rr (templateTerm t))
  narrow1  rr t    = runLWithSubst (narrow1 rr (templateTerm t))
  unify t t'       = runLG (manualUnify (templateTerm t) (templateTerm t'))

instance (Term t s, GoodShape s) => Term.TRSN t s where
--  narrow1'    rr t = runSTWithSubst (narrow1' rr (templateTerm t))
  narrowBasic rr t = runSTWithSubst ((fmap freeGT *** freeGT) `fmap2` 
                                        narrowBasic rr (templateTerm t))
  narrowFull rr t  = runSTWithSubst (narrowFull rr (templateTerm t))
  narrowFullBounded pred rr t = 
      let pred' = return . pred <=< zonkTerm' <=< dupTerm in
      runSTWithSubst (narrowFullBounded pred' rr (templateTerm t))  

instance (Term t s, GoodShape s) => Term.TRS t s Maybe where
  {-# SPECIALIZE instance Term.TRS (TermStatic_ Int) BasicShape Maybe #-}
  unify t t'       = runMG (manualUnify (templateTerm t) (templateTerm t'))
  rewrite  rr t    = runM (rewrite rr (templateTerm t))
  rewrite1 rr t    = runM (rewrite1 rr (templateTerm t))
  narrow1  rr t    = runMWithSubst (narrow1    rr (templateTerm t))

instance OmegaPlus Semantic t r s => 
    Term.TRS (GT_ Semantic r) s (t (ST r)) where
  {- SPECIALIZE instance Term.TRS (GT_ Semantic r) BasicShape (ListT (ST r)) #-}
  {- SPECIALIZE instance Term.TRS (GT_ Semantic r) BasicShape (MaybeT (ST r)) #-}
  unify t t'    = manualUnify' (templateTerm t) (templateTerm t')
  rewrite       = rewrite
  rewrite1      = rewrite1
  narrow1    rr = narrow1 rr

runSTWithSubst :: (Term t s, Omega Semantic (ListT') r s) =>
                          (forall r. ST r [(Subst r s, GTE r s)])
                      -> [(SubstM (t s), t s)]
runSTWithSubst m = runST (mapM (biM zonkSubst zonkTerm') =<< m)

runLWithSubst :: (Term t s, Omega Semantic (ListT') r s) =>
                          (forall r. ListT' (ST r) (Subst r s, GTE r s))
                      -> [(SubstM (t s),t s)]
runLWithSubst m = runST (runListT' (runWithSubst m))

runMWithSubst :: (Term t s, Omega Semantic MaybeT r s) =>
                          (forall r. MaybeT (ST r) (Subst r s, GTE r s))
                      -> Maybe (SubstM (t s),t s)
runMWithSubst m = runST (runMaybeT (runWithSubst m))

runWithSubst ::  (Term t s, Omega mode m r s) =>
                          (m (ST r) (Subst r s, GT_ mode r s))
                        -> m (ST r) (SubstM (t s),t s)
runWithSubst m = lift . biM zonkSubst zonkTerm' =<< m

zonkSubst :: (Prune mode, Term t s) =>
             (Subst_ mode r s) -> ST r (SubstM (t s))
zonkSubst = fmap SubstM . fmap2(>>= zonkTerm) . mapM2 col . fromSubstM

manualUnify :: Omega mode m r s => 
               GT_ mode r s -> GT_ mode r s -> m (ST r) (Subst_ mode r s)
manualUnify t u = do
  (subst, [t',u']) <- lift$ autoInstG [t,u]
  unify t' u'
  return subst

-- I know, I'm going to burn in hell...
manualUnify' :: Omega mode m r s => 
               GT_ mode r s -> GT_ mode r s -> m (ST r) (Subst_ mode r s)
manualUnify' t u = do
  (_,[t',u']) <- lift$ autoInstG [t,u]
  let mvars = [ v | MutVar v <- collect isMutVar t, t <- [t',u']]
  mvars_indexes <- lift$ catMaybes <$> forM mvars getUnique
  let skolem_offset = maximum (0 : mvars_indexes)
  unify t' u'
  indexes <- lift$ forM mvars $ \v -> 
             readVar' v >>= \x -> 
             return$ case x of
               Skolem  -> fromJust(elemIndex v mvars) + skolem_offset
               Empty i -> i
               Mutable (Just i) _ -> i
               Mutable Nothing  _ -> fromJust(elemIndex v mvars) + skolem_offset
  return (mkSubstM indexes (map MutVar mvars))

--------------------------------------
-- * The Omega type class and friends
--------------------------------------
-- |"Omega is just a Type Class constraint synonym" 
class (TermShape s, Show (s (TermStatic s))) => GoodShape s
instance (TermShape s, Show (s (TermStatic s))) => GoodShape s

#ifdef __HADDOCK__
class ( MonadError (TRSException) (t (ST r)), MonadTrans t, Monad (t (ST r)), Functor (t (ST r)), TermShape s, Prune mode) => Omega mode t r s
#else
class ( MonadError (TRSException) (t (ST r)), MonadTrans t, Monad (t (ST r)), Functor (t (ST r)), TermShape s, Prune mode) => 
    Omega mode (t :: (* -> *) -> * -> *) r (s :: * -> *)
#endif
class (Omega mode t r s, MonadPlus (t (ST r)), GoodShape s) => 
    OmegaPlus mode t r s 

instance ( MonadError (TRSException) (t (ST r)), MonadTrans t, Monad (t (ST r)), Functor (t (ST r)), TermShape s, Prune mode) => Omega mode t r s
instance ( Omega mode t r s, MonadPlus (t (ST r)), Show (s (TermStatic s))) => OmegaPlus mode t r s

----------------
-- Other stuff
----------------

someSubterm :: (Traversable t, MonadPlus m) => (a -> m a) -> t a -> m (t a)
someSubterm f x = msum$ interleave f return x

instance Show (GT_ eq r s) => Observable (GT_ eq r s) where
    observer = observeBase


{-# INLINE fail1 #-}
fail1 :: Monad m => String -> m a 
--fail1 msg = trace msg $ fail msg
fail1 = fail

-- TODOs:
-- - Float pruning to the type

st :: (TermShape s, Show (s (TermStatic s))) => GT_ mode r s -> String 
st = show . zonkTermS'
sr ::  (Functor f, TermShape s, Show (f (TermStatic s))) =>
      f (GT_ mode r s) -> String
sr = show . fmap zonkTermS'

brackets text = '[' : text ++ "]"