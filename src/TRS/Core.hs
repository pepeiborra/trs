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
  semEq, semEq'
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
import Control.Arrow ( first, second, (***))
import Control.Exception (handle)
import Control.Monad hiding (msum, mapM_, mapM, sequence, forM)
import Control.Monad.Error (MonadError(..), ErrorT(..), MonadTrans(..))
import Control.Monad.State (StateT(..), MonadState(..), gets, modify, lift)
import Control.Monad.Fix (MonadFix(..))
import Control.Monad.List (runListT, ListT)
import Control.Monad.Writer (tell, execWriterT, WriterT(..))
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

import TRS.Term hiding (TRS(..), TRSN(..), templateTerm, replace, semEq)
import qualified TRS.Term as TRS
import TRS.Substitutions
import TRS.Rules
import TRS.Types
import TRS.Terms
import TRS.Context
import TRS.Utils
import TRS.GTerms
import TRS.Tyvars

import TypePrelude
import TypeCastGeneric

import GHC.Exts (unsafeCoerce#)
import Observe
import qualified Debug.Trace

{-# SPECIALIZE prune_ :: GT user r BasicShape -> ST r (GT user r BasicShape) #-}

type Subst user r s       = Subst_ user Normal r s
type Subst_ user mode r s = SubstM (GT_ user mode r s)
--type RawSubst mode r s  = TRS.SubstG (GT_ user mode r s)
type Rule_ user mode r s  = Rule (GT_ user mode r) s

templateTerm :: Term t s user => t s -> GT_ user mode r s
templateTerm = freeGT . TRS.templateTerm

mutableTerm :: Term t s user => t s -> ST r (GT user r s)
--mutableTerm = mkGTM . templateTerm  WRONG!
mutableTerm = return . snd <=< autoInst <=< templateTerm'

mkMutVar :: Term t s user => t s -> ST r (GT user r s)
mkMutVar = maybe (fresh Nothing) (mutVar Nothing) . varId

mutableTermG :: (Traversable f, Term t s user) => f(t s) -> ST r (f(GT user r s))
mutableTermG = return . snd <=< autoInstG <=< mapM templateTerm'

{- SPECIALIZE rewrite1 :: OmegaPlus Normal MaybeT r BasicShape => 
              [Rule BasicShape] -> GT user r BasicShape -> MaybeT (ST r) (GT user r BasicShape)#-}
-- |leftmost outermost
rewrite1  :: (Term t s user, OmegaPlus Normal m r s) => 
            [Rule t s] -> GT user r s -> m (ST r) (Subst_ user Normal r s, GT user r s)
rewrite1 rre t = lift(fixRules rre) >>= \rr' -> rewrite1_ rr' t

-- |leftmost outermost
rewrite   :: (Term t s user, OmegaPlus Normal m r s) => 
            [Rule t s] -> GT user r s -> m (ST r) (Subst_ user Normal r s, GT user r s)
rewrite  rre t = lift(fixRules rre) >>= \rr' -> rewrite_ rr' t

-- |leftmost outermost
narrow1   :: (Term t s user, OmegaPlus Normal m r s) => 
            [Rule t s] -> GT user r s -> 
             m (ST r) (Subst_ user Normal r s, GT user r s)
narrow1 rr t = lift(fixRules rr) >>= \rr' -> narrow1_ rr' t

{-
-- |leftmost outermost
narrow1' :: (Term t s user, GoodShape s) => 
           [Rule t s] -> GT user r s -> ST r [(Subst user r s, GT user r s)]
narrow1' rr = narrow1'_ (fixRules rr)
-}

-- |leftmost outermost, in variables too
narrow1V :: (Term t s user, GoodShape s) => 
           [Rule t s] -> GT user r s -> ST r [(Subst user r s, GT user r s)]
narrow1V rr t = fixRules rr >>= \rr' -> narrow1V_ rr' t

narrowFull :: (Term t s user, GoodShape s) => 
             [Rule t s] -> GT user r s -> 
             ST r [(Subst user r s, GT user r s)]
narrowFull rr t = fixRules rr >>= \rr' ->  narrowFull_ rr' t

narrowFullV :: (Term t s user, GoodShape s) => 
              [Rule t s] -> GT user r s -> ST r [(Subst user r s, GT user r s)]
narrowFullV rr t =  fixRules rr >>= \rr' -> narrowFullV_ rr' t

narrowBasic :: (Term t s user, GoodShape s) => [Rule t s] -> GT_ user Basic r s -> 
             ST r [(Subst_ user Basic r s, GT_ user Basic r s)]
narrowBasic rr term =  fixRules rr >>= \rr' -> 
                         narrowBasic_ rr'
                            =<<  templateTerm' term

narrowFullBounded  :: (Term t s user, GoodShape s) => 
                      (GT user r s -> ST r Bool) -> [Rule t s] -> GT user r s -> 
                      ST r [(Subst user r s, GT user r s)]
narrowFullBounded pred rr t =  fixRules rr >>= \rr' ->
                               narrowFullBounded_ (pred) rr' t

narrowFullBoundedV :: (Term t s user, GoodShape s) => 
                      (GT user r s -> ST r Bool) -> [Rule t s] -> GT user r s -> 
                      ST r [(Subst user r s, GT user r s)]
narrowFullBoundedV pred rr t = fixRules rr >>= \rr' ->
                               narrowFullBoundedV_ (pred) rr' t

-- | generalize builds a sigma type, i.e. a type scheme, by 
--   replacing all mutvars in a term with GenVars
generalize ::(Prune mode, TermShape s) => GT_ user mode r s -> ST r (GT_ user mode r s)
generalizeG::(Prune mode, TermShape s,Traversable f) => 
               f(GT_ user mode r s) -> ST r (f(GT_ user mode r s))
generalizeGG::(Prune mode, TermShape s, Traversable f, Traversable f') => 
               f'(f(GT_ user mode r s)) -> ST r (f'(f(GT_ user mode r s)))


rewrite1_ :: OmegaPlus mode m r s => 
             [Rule_ user mode r s] -> GT_ user mode r s -> 
                                      m (ST r) (Subst_ user mode r s, GT_ user mode r s)
rewrite_  :: OmegaPlus mode m r s => 
             [Rule_ user mode r s] -> GT_ user mode r s -> 
                                      m (ST r) (Subst_ user mode r s, GT_ user mode r s)
narrow1_  :: OmegaPlus mode m r s => [Rule_ user mode r s] -> GT_ user mode r s -> 
             m (ST r) (Subst_ user mode r s, GT_ user mode r s)

--narrow1'_ :: (GoodShape s, Prune mode) => [Rule_ user mode r s] -> GT_ user mode r s 
--             -> ST r [(Subst_ user mode r s, GT_ user mode r s)]

-- |leftmost outermost, on variables too (paramodulation)
narrow1V_ :: (GoodShape s, Prune mode) => [Rule_ user mode r s] -> GT_ user mode r s 
             -> ST r [(Subst_ user mode r s, GT_ user mode r s)]

-- |Unbounded Full Narrowing
narrowFull_ :: (Prune mode, Eq (GT_ user mode r s), GoodShape s) => [Rule_ user mode r s] -> GT_ user mode r s -> 
             ST r [(Subst_ user mode r s, GT_ user mode r s)]

-- |Unbounded Full Paramodulation
narrowFullV_ :: (Prune mode, GoodShape s) => 
              [Rule_ user mode r s] -> GT_ user mode r s -> ST r [(Subst_ user mode r s, GT_ user mode r s)]

-- | Bounded versions. The first argument is the bound checking predicate
narrowFullBounded_ :: (Prune mode, GoodShape s) =>
                      (GT user r s -> ST r Bool) -> [Rule_ user mode r s] -> GT_ user mode r s -> 
                      ST r [(Subst_ user mode r s, GT_ user mode r s)]
narrowFullBoundedV_:: (Prune mode, GoodShape s) =>
                      (GT user r s -> ST r Bool) -> [Rule_ user mode r s] -> GT_ user mode r s -> 
                      ST r [(Subst_ user mode r s, GT_ user mode r s)]

fixRules :: (Term t s user, TermShape s, Functor s) => 
            [Rule t s] -> ST r [Rule_ user Normal r s]
fixRules = mapM2 templateGT' >=> generalizeGG

-- * Basic primitives
{- SPECIALIZE unify :: Omega Normal MaybeT r BasicShape => 
                            GT_ user Normal r BasicShape -> GT_ user Normal r BasicShape 
                         -> MaybeT (ST r) () #-}
{- SPECIALIZE unify :: Omega Normal ListT r BasicShape => 
                            GT_ user Normal r BasicShape -> GT_ user Normal r BasicShape 
                         -> ListT (ST r) () #-}
unify	  :: Omega mode m r s => GT_ user mode r s -> GT_ user mode r s -> m (ST r) ()
match	  :: Omega mode m r s => GT_ user mode r s -> GT_ user mode r s -> m (ST r) ()

-----------------------------
-- * The machinery
------------------------------

class Prune (mode :: *) where 
    prune :: GT_ user mode r s  -> ST r (GT_ user mode r s)

instance Prune Basic  where prune x = pruneBasic_ x
instance TypeCast Normal mode => Prune mode where prune x = prune_ x

{-# INLINE prune_ #-}
prune_ :: GT_ user mode r s -> ST r (GT_ user mode r s)
prune_ (typ@MutVar{ref=ref}) =
	do { m <- readVar ref
	   ; case m of
	      Just t ->
		do { newt <- prune_ t
		   ; writeVar ref newt
		   ; return newt }
	      Nothing -> return typ}
prune_ x = return x

pruneBasic_ :: GT_ user t t1 t2 -> ST t1 (GT_ user t t1 t2)
pruneBasic_ (typ@MutVar{ref=ref}) =
	do { m <- readVar ref
	   ; case m of
	      Just t ->
		do { newt <- pruneBasic_ t
		   ; writeVar ref newt
		   ; return typ }
	      Nothing -> return typ}
pruneBasic_ x = return x

{-# INLINE col #-}
{-# SPECIALIZE col :: GT_ user Normal r BasicShape -> ST r (GT_ user Normal r BasicShape) #-}
{-# SPECIALIZE col :: GT_ user Basic r BasicShape -> ST r (GT_ user Basic r BasicShape) #-}
col :: (Prune mode, Traversable s) => GT_ user mode r s  -> ST r (GT_ user mode r s)    
col x =
     do { x' <- prune x
	; case x' of
	  (S y) -> 
	    do { t <- (mapM col y) 
	       ; return (S t)} 
	  _     -> return x'}

occurs :: (Prune mode, MonadTrans t, Traversable s, Monad (t (ST r))) =>
         Ptr user mode r s -> GT_ user mode r s -> t (ST r) Bool
occurs v t =
     do { t2 <- lift$ prune t 
	; case t2 of 
	  S w -> 
	    do { s <- (mapM (occurs v) w) 
	       ; return(foldr (||) False s ) 
	       } 
	  MutVar{ref=z} -> return (v == z) 
	  _ -> return False } 

unify tA tB = 
     do  t1 <- lift$ prune tA 
	 t2 <- lift$ prune tB 
	 case (t1,t2) of
           (Top{},Top{})       -> return ()
           (Bottom{},Bottom{}) -> return ()
           (Top{}, S x)        -> mapM (unify t1) x >> return ()
           (S x, Top{})        -> mapM (unify t2) x >> return ()
	   (MutVar{ref=r1},MutVar{ref=r2}) -> 
	     if r1 == r2 
		then return () 
		else lift$ writeVar r1 t2
	   (MutVar{ref=r1},_)  -> varBind r1 t2 
	   (_,MutVar{ref=r2})  -> varBind r2 t1 
	   (GenVar{unique=n},GenVar{unique=m}) -> 
	    if n==m 
		then return () 
		else throwError genErrorUnify
	   (S x,S y) -> 
	     case matchTerm x y of
                Nothing        -> throwError genErrorUnify --(shapeErrorUnify tA tB)
		Just pairs     -> 
		  mapM_ (uncurry unify) pairs 
	   (x,y)               -> throwError genErrorUnify -- (shapeErrorUnify tA tB)

varBind :: Omega mode m r s => Ptr user mode r s -> GT_ user mode r s -> m (ST r) ()
varBind r1 t2 = 
     do { b <- occurs r1 t2 
	; if b 
	    then throwError occursError
	    else lift$ writeVar r1 t2 }

match tA tB = 
     do { t1 <- lift$ prune tA 
	; t2 <- lift$ prune tB 
	; case (t1,t2) of 
          (Top{},Top{})        -> return ()
          (Bottom{}, Bottom{}) -> return ()
          (Top{}, S x)         -> return () -- Is this right ?
          (S x, Top{})         -> mapM (match t2) x >> return ()
	  (MutVar{ref=r1},_)   -> 
	    lift$ writeVar r1 t2
	  (GenVar{unique=n},GenVar{unique=m}) -> 
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
instance (Prune mode, Traversable s) => Instan (GT_ user mode r s) (Subst_ mode r s) (ST r) where
  {- SPECIALIZE instance Instan (GT_ user Normal r BasicShape) (Subst_ Normal r BasicShape) (ST r) #-}
  instan sub t = do --prune >=> instan sub . DontCol >=> col . unDontCol  
      t1 <- prune t
      DontCol t2 <- instan sub (DontCol t1)
      col t2
-}
newtype DontCol a = DontCol {unDontCol::a}
instance (Prune mode, Traversable s) => 
    Instan (DontCol(GT_ user mode r s)) (Subst_ user mode r s) (ST r) where
  instan s (DontCol x) = DontCol <$> instanDontCol x
    where
     sub = fromSubstM s
     instanDontCol x = do
         { case x of 
	    GenVar{unique=n} | n `atLeast` sub, Just val <- sub !! n -> return val
	    S x -> S <$> mapM instanDontCol x 
            _ -> return x
	 } 

{-
instance (Prune mode, Traversable s) => Instan (GT_ user mode r s) (SubstI mode r s) (ST r) where
  instan s x = do
    let sub = fromSubstM s
    x' <- prune x
    case x' of
      GenVar n | Just val <- lookup n sub -> col $! val
      S x -> S <$> (instan s `mapM` x)
      _   -> return x'
-}
instance (Prune mode, Traversable s) => 
    Instan (GT_ user mode r s) (Subst_ user mode r s) (ST r) where
  instan sub x = 
      do { let vv = fromSubstM sub
         ; x' <- prune x 
	 ; case x' of 
	    GenVar{unique=n} | n `atLeast` vv
                     , Just val <- vv !! n -> col $! val
	    S x -> S <$> mapM (instan sub) x
            _ -> return x'
	 } 
  

--generalize_ x | trace ("generalize " ++ show x ) False = undefined
generalize x = do
  x' <- col x
  let mvars = nub $ collect isMutVar x'
  muniques <- mapM (getUnique . ref) mvars
  let !new_gvars = [ (m,GenVar{note_= note m, unique=u})
                    | (Just u,m) <- zip muniques mvars]
      !new_skols = [ (m,Skolem{note_ = note m, unique=0})
                    | (Nothing,m)<- zip muniques mvars]
  x'' <- replaceM (new_gvars ++ new_skols) x'
  assert (noMVars x'') (return ())
  return x''

generalizeG x = do
  x' <- mapM col x
  let mvars = nub $ concat (collect isMutVar <$> x')
  muniques <- mapM (getUnique . ref) mvars
  let new_gvars = [ (m,GenVar{note_= note m, unique=u})
                    | (Just u,m) <- zip muniques mvars]
      new_skols = [ (m,Skolem{note_ = note m, unique=0})
                    | (Nothing,m)<- zip muniques mvars]
  x'' <- replaceM (new_gvars ++ new_skols) `mapM` x'
  assert (all noMVars x'') (return ())
  return x''

generalizeGG x = do
  x' <- mapM2 col x
  let mvars = nub $ concat2 (collect isMutVar `fmap2` x')
  muniques <- mapM (getUnique . ref) mvars
  let new_gvars = [ (m,GenVar{note_= note m, unique=u})
                    | (Just u,m) <- zip muniques mvars]
      new_skols = [ (m,Skolem{note_ = note m, unique=0})
                    | (Nothing,m)<- zip muniques mvars]
  x'' <- replaceM (new_gvars ++ new_skols) `mapM2` x'
  assert (all (all noMVars) x'') (return ())
  return x''

-- | autoInst instantitates a type scheme with fresh mutable vars
--   Returns the instantiated term together with the new MutVars 
--  (you need these to apply substitutions) 
{-# SPECIALIZE autoInst :: GT_ user Normal r BasicShape -> 
                        ST r (SubstM (GT_ user Normal r BasicShape), GT_ user Normal r BasicShape) #-}
{-# SPECIALIZE autoInst :: GT_ user Basic r BasicShape -> 
                        ST r (SubstM (GT_ user Basic r BasicShape), GT_ user Basic r BasicShape) #-}
autoInst :: (Prune mode, TermShape s) => 
            GT_ user mode r s -> ST r (Subst_ user mode r s, GT_ user mode r s)       
autoInst x@MutVar{} = return (mempty, x)
autoInst x_ = do
           x     <- col x_
           let vars_x = vars x
           let (nn,ii) = unzip$ snubBy (compare `on` snd) 
                             [ (n,i) | GenVar{unique=i,note_=n} <- vars_x]
           subst <- mkSubstM ii <$> mapM fresh nn
           x'    <- instan subst x
           skolems <- replicateM (length$ nub$ filter isSkolem vars_x) (fresh Nothing)
           let x''  = replace (zip (nub$ filter isSkolem vars_x) skolems) x'
           assert (noGVars x'') (return ())
           return (subst, x'')

autoInstG:: (Traversable f, TermShape s, Prune mode) =>
               f(GT_ user mode r s) -> ST r (Subst_ user mode r s, f(GT_ user mode r s))
autoInstG xx_ = do
  xx <- mapM col xx_
  let vars_xx = concatMap vars xx
      (nn,ii) = unzip $ snubBy (compare `on` snd) 
                 [ (n,i) | GenVar{unique=i,note_=n} <- vars_xx]
  subst <- mkSubstM ii <$> mapM fresh nn
  xx' <- instan subst `mapM` xx
  skolems <- replicateM (length$ nub$ filter isSkolem vars_xx) (fresh Nothing)
  let xx''  = replace (zip (nub$ filter isSkolem vars_xx) skolems) <$> xx'
  assert (all noGVars xx'') (return ())
  return (subst, xx'')
    where 

autoInstGG ::  ( Traversable f,Traversable g, TermShape s, Prune mode) =>
               f (g (GT_ user mode r s)) -> 
                   ST r (Subst_ user mode r s, f (g(GT_ user mode r s)))
autoInstGG xx_ = do
  xx <- mapM2 col xx_
  let (nn,ii) = unzip $ snubBy (compare`on`snd) 
                [ (n,i) | GenVar{unique=i,note_=n} <- concatMap2 vars xx]
  subst <- mkSubstM ii <$> mapM fresh nn
  xx'   <- instan subst `mapM2` xx
  return (subst, xx')
    where 


-- |Semantic equality (equivalence up to renaming of vars) 
semEq :: (Prune mode, TermShape s) => GT_ user mode r s -> GT_ user mode r s -> ST r Bool
semEq x y = do
    (_,x') <- autoInst x
    (_,y') <- autoInst y
    xy_vars <- filterM isUnboundVar (collect isMutVar =<< [x', y'])
    unified <- runMaybeT (unify x' y' >> return ())
    if isNothing unified 
       then return False
       else do
--       mapM col xy_vars  Why col here?
         allM isUnboundVar xy_vars

-- isRenaming :: Subst_ user mode r s -> ST r Bool
isRenaming :: (Term t s user, GoodShape s) => SubstM (t s) -> Bool
isRenaming vv = all isVar [v | Just v <- fromSubstM vv]
--semEqG x y = return$ synEq x y

---------------------------------------------------------------
-- * Pure (partial) Semantic Equality
---------------------------------------------------------------
-- | Fails for terms with mutvars
---  TODO: I don't think this is very efficient
semEq' :: TermShape s => GT_ user mode r s -> GT_ user mode r s -> Bool
semEq' s t = fromMaybe False $ runST (runMaybeT $ do
  s' <- MaybeT$ (fmap join . sequence . fmap2 zonkTermS . fmap mutableTerm . zonkTermS) s
  t' <- MaybeT$ (fmap join . sequence . fmap2 zonkTermS . fmap mutableTerm . zonkTermS) t
  assert (noMVars s) $ assert (noMVars t) $ 
   return(s' == t'))

zonkTermS :: TermShape s => GT_ user mode r s -> Maybe (TermStatic s)
zonkTermS = zonkTerm

zonkTermS' :: TermShape s => GT_ user mode r s -> (TermStatic s)
zonkTermS' = zonkTermUnsafe

{-----------------------------------------------------
-- IDEAS FOR EFFICIENCY
-- Many-to-one matching algorithm (see SPJ87, Maranget2001)
-- Fuse autoInst and matching in a single pass
-- User the ATerm library from INRIA Nancy and the ELAN group
-----------------------------------------------------}

--rewrite1_ rr (S t) | trace ("rewrite " ++ show t ++ " with " ++  (show$ length rr) ++ " rules ") False = undefined
--rewrite1_ _ t | assert (noMVars t) False = undefined
-- rewrite1_ [] t = mzero
rewrite1_ rules t =
    case t of
      S u -> rewriteTop t `mplus`
             (second S . swap <$> runWriterT 
                        (someSubterm (WriterT . fmap swap . rewrite1_ rules) u))
      t   -> rewriteTop t
  where rewriteTop t = msum$ forEach rules $ \r@(lhs:->rhs) -> do
	        (freshv, lhs':->rhs') <- lift$ autoInstG r
	        match lhs' t
                return (freshv, rhs')

rewrite_ rules t = iterateMP (\(_subst,t)-> rewrite1_ rules t) (emptySubstM,t)

--narrow1_ _ t | trace ("narrow1 " ++ show t) False = undefined
narrow1_ [] t = mzero -- fail1 "narrow1: empty set of rules"
--narrow1_ _ t | not (noMVars t) = t `seq` error  "narrow1: " 
--narrow1_ _ t | assert (noMVars t) False = undefined
narrow1_ rules t@S{} = go (t, emptyC)
    where go (t, ct) = 
              narrowTop rules ct t
             `mplus` 
              msum [go (t, ct|>ct1) | (t, ct1) <- contexts t]
narrow1_ rules _ = mzero -- fail "narrow1: No Narrowing at vars"

narrowTop, narrowTopV :: OmegaPlus mode m r s =>
             [Rule_ user mode r s] -> GT_ user mode r s -> GT_ user mode r s
          -> m (ST r) (Subst_ user mode r s, GT_ user mode r s)
narrowTop  rules ct t = --assert (all noMVars [t, ct])$ 
                        unsafeNarrowTop rules ct t
narrowTopV rules ct t = --assert (all noMVars [t, ct])$ 
                        unsafeNarrowTopV rules ct t

unsafeNarrowTop, unsafeNarrowTopV :: OmegaPlus mode m r s =>
                  [Rule_ user mode r s] -> GT_ user mode r s -> GT_ user mode r s
                -> m (ST r) (Subst_ user mode r s, GT_ user mode r s)
unsafeNarrowTop   = unsafeNarrowTopG narrowTop1
unsafeNarrowTopV  = unsafeNarrowTopG narrowTop1V

unsafeNarrowTopG ::(Prune mode, TermShape s, MonadTrans t, MonadPlus (t (ST r))) =>
                  (GT_ user mode r s -> a -> t (ST r) (GT_ user mode r s))
                 -> [a] -> GT_ user mode r s -> GT_ user mode r s
                 -> t (ST r) (Subst_ user mode r s, GT_ user mode r s)
-- unsafeNarrowTopG _ _ _ t | trace ("unsafeNarrowTop " ++ show t) False = undefined
unsafeNarrowTopG narrowTop1 rules ct t = msum$ forEach rules $ \r -> do
               (vars, [t',ct']) <- lift$ autoInstG [t,ct]
               t''              <- narrowTop1 t' r
               return (vars, ct'|>t'')

narrowTop1, narrowTop1V :: OmegaPlus mode m r s => 
                           GT_ user mode r s -> Rule_ user mode r s 
                        -> m (ST r) (GT_ user mode r s)
narrowTop1V t r@(lhs:->rhs) = do
               assert (noGVars t) (return ())
               assert (noMVars lhs) (return ())
               assert (noMVars rhs) (return ())
--               assert (vars rhs `isSubsetOf` vars lhs) (return ())
               (lhsv, lhs':-> rhs') <- lift$ autoInstG r
               unify lhs' t
--               trace ("narrowing fired: t=" ++ st t ++ ", rule=" ++ sr r
--                   ++   ", rho= " ++ show (zonkTermS lhsv)
--                      )(return ()) 
--             assert (noGVars rhs'') (return ())
               return rhs'
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
                 ([t] -> Context user mode r s -> Subst_ user mode r s -> GT_ user mode r s
                  -> LogicT.SFKT (ST r) (Subst_ user mode r s, GT_ user mode r s))
               -> (GT user r s -> ST r Bool) -> [t] -> GT_ user mode r s 
               -> ST r [(Subst_ user mode r s, GT_ user mode r s)]

--narrowFullBase _ done [] t = -- trace ("narrowFull " ++ show t ++ " with empty TRS")$ 
--                           return []
narrowFullBase narrowTop1base done rules t = do 
--     assert (noMVars t) (return ())
     (subst0,t0) <- autoInst t
     -- nubByM (semEq `at` snd) =<< 
     LogicT.runM Nothing (search (Ind 0) (subst0, t0))
  where   
--   search :: (Subst user r s, GT user r s) -> LogicT'.SR r1 (ST r) (T2(Subst user r s) (GT user r s))
   search !ind (subst,t) = trace ("narrowFull search: " ++ show ind  ++ st t) $ 
       LogicT.ifte  (step emptyC subst t)
                    (\x@(sub',t') -> trace ("branch " ++ show ind ++ st t') $ 
                               lift (done (idGT t')) >>- \isDone -> 
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
narrowTop', narrowTopV' :: OmegaPlus Normal m r s => 
                          [RuleI r s] -> Context r s
                        -> Subst user r s -> GT user r s
                        -> m (ST r) (Subst user r s, GT user r s)
-}

narrowTop' :: OmegaPlus mode m r s =>
             [Rule_ user mode r s] -> GT_ user mode r s -> Subst_ user mode r s -> GT_ user mode r s
           -> m (ST r) (Subst_ user mode r s, GT_ user mode r s)

narrowTop'  = narrowTopBase narrowTop1

narrowTopV' :: OmegaPlus mode m r s =>
              [Rule_ user mode r s] -> GT_ user mode r s -> Subst_ user mode r s -> 
              GT_ user mode r s -> m (ST r) (Subst_ user mode r s, GT_ user mode r s)

narrowTopV' = narrowTopBase narrowTop1V

-- narrowTopBase' _ _ _ _  t | trace ("NarrowTop' " ++ show t) False = undefined
{-
narrowTopBase :: (Prune mode, MonadTrans t, MonadPlus (t (ST r)), TermShape s) =>
                (GT_ user mode r s -> a -> t (ST r) (GT_ user mode r s))
              -> [a] -> GT_ user mode r s -> SubstG (GT_ user mode r s) -> GT_ user mode r s
              -> t (ST r) (SubstG (GT_ user mode r s), GT_ user mode r s)
-}
narrowTopBase _ _ ct _ t | assert (noGVars t)  False = undefined
narrowTopBase _ _ ct _ t | assert (noGVars ct) False = undefined
narrowTopBase narrowTop1 rules ct subst t = msum$ forEach rules $ \r -> do
               assert(noGVars ct) (return ())
               (subst', [ct'], t') <- lift$ dupTermWithSubst subst [ct] t
               t''     <- narrowTop1 t' r
               ct''    <- lift$ col ct'
               subst'' <- lift(col `mapM` subst')
               return (subst'', ct''|>t'')

--------------------------------
-- * Duplication of Terms
--------------------------------

dupVar :: STRef s a -> ST s (STRef s a)
dupVar sr = readSTRef sr >>= newSTRef
dupTerm :: (Traversable s) => GT_ user eq r s -> ST r (GT_ user eq r s)
dupTerm t@MutVar{ref=r} = dupVar r >>= \r' -> return t{ref=r'}
dupTerm (S t) = fmap S $ mapM dupTerm t
dupTerm x = return x

dupTermWithSubst :: (Traversable subst,  TermShape s) =>
                   subst(GT_ user eq r s) -> [GT_ user eq r s] -> GT_ user eq r s
                -> ST r (subst(GT_ user eq r s), [GT_ user eq r s], GT_ user eq r s)

--dupTermWithSubst subst tt x | trace "dupTermWithSubst" False = undefined
dupTermWithSubst subst tt t@MutVar{} = do
    t'        <- dupTerm t
    let dict = [(t,t')]
    subst'  <- replaceM dict `mapM` subst
    tt'     <- replaceM dict `mapM` tt
    return (subst', tt', t')

dupTermWithSubst subst tt t@S{} = do
    let mutvars= collect isMutVar t
    newvars <- mapM dupTerm mutvars
    let dict = zip mutvars newvars
    t'     <- replaceM dict t
    tt'    <- replaceM dict `mapM` tt
    subst' <- TRS.GTerms.replaceM dict `mapM` subst
    subst `seq` return (subst', tt', t')

dupTermWithSubst subst tt x = return (subst, tt, x)


------------------------------
-- * Obtaining the results
------------------------------
run :: (TermShape s, Show (s (GT user r s)), Term t s user) => 
       (forall r.ST r (GT user r s)) -> t s
run c | Just x <- runST (fmap zonkTerm c) = x
      | otherwise = error "A mutable variable was found in the result"

runG :: (TermShape s, Show (s (GT user r s)), Traversable f, Term t s user) =>
         (forall r.ST r (f(GT user r s))) -> f(t s)
runG c | Just x <- sequence$ runST (fmap2 zonkTerm c) = x
       | otherwise = error "A mutable variable was found in the result"

runG' :: (TermShape s, Show (s (GT user r s)), Traversable f, Term t s user) =>
         (forall r.ST r (f(GT user r s))) -> f(t s)
runG' c = runST (c >>= mapM zonkTerm') 


runGG :: (TermShape s, Show (s (GT user r s)), Traversable f, Traversable f1, Term t s user) =>
         (forall r.ST r (f(f1(GT user r s)))) -> f(f1(t s))
runGG c | Just x <- sequence2$ runST ( (fmap3 zonkTerm c)) = x
        | otherwise = error "A mutable variable was found in the result"

runIO :: ST RealWorld a -> IO a
runIO = stToIO


runE :: (Omega Normal (ErrorT (TRSException)) r s, Term t s user) => 
        (forall r. ErrorT (TRSException) (ST r) (GT user r s)) -> t s
runE c | Just x <- runST ( either (error.show) id <$>
                              runErrorT (zonkTerm <$> c)) = x
       | otherwise = error "A mutable variable was found in the result"  

runEG :: (Omega Normal (ErrorT (TRSException)) r s, Traversable f, Term t s user) =>
         (forall r. ErrorT (TRSException) (ST r) (f(GT user r s))) -> f(t s)
runEG c | Just x <- sequence$ runST (either (error.show) id <$>
                                    (runErrorT (fmap2 zonkTerm c))) = x
        | otherwise = error "A mutable variable was found in the result"

runEGG :: (Omega Normal (ErrorT (TRSException)) r s, Traversable f, Traversable f1, Term t s user) =>
         (forall r. ErrorT (TRSException) (ST r) (f(f1(GT user r s)))) -> f(f1(t s))
runEGG c | Just x <- sequence2$ runST (either (error.show) id <$>
                                    (runErrorT (fmap3 zonkTerm c))) = x

runEIO :: ErrorT (TRSException) (ST RealWorld) a -> IO a
runEIO = fmap (either (error. show) id) . stToIO . runErrorT

-- runMaybeT = fmap (either (const Nothing) Just) . runErrorT

runM :: (Omega Normal MaybeT r s, Term t s user) => 
        (forall r. MaybeT (ST r) (GT user r s)) -> Maybe (t s)
runM c | Just x <- sequence$ runST (runMaybeT (fmap zonkTerm c)) = x

runMG :: (Omega Normal MaybeT r s, Traversable f, Term t s user) =>
         (forall r. MaybeT (ST r) (f(GT user r s))) -> Maybe (f(t s))
runMG c | Just x <- sequence2 $ runST(runMaybeT (fmap2 zonkTerm c)) = x

runMGG :: (Omega Normal MaybeT r s, Traversable f, Traversable f1, Term t s user)=>
         (forall r. MaybeT (ST r) (f(f1(GT user r s)))) -> Maybe (f(f1(t s)))
runMGG c | Just x <- sequence3$ runST(runMaybeT (fmap3 zonkTerm c)) = x

runMIO :: MaybeT (ST RealWorld) a -> IO (Maybe a)
runMIO = stToIO . runMaybeT



runL :: (Term t s user, Omega Normal (ListT') r s) => 
        (forall r. ListT' (ST r) (GT user r s)) -> [t s]
runL c   = runST (runListT' (lift . zonkTerm' =<< c ))

runLG :: (Omega Normal (ListT') r s, Traversable f, Term t s user) =>
         (forall r. ListT' (ST r) (f(GT user r s))) -> [f(t s)]
runLG c  = runST (runListT' (lift . mapM zonkTerm' =<< c))

runLGG :: (Omega Normal (ListT') r s, Traversable f, Traversable f1, Term t s user) =>
         (forall r. ListT' (ST r) (f(f1(GT user r s)))) -> [f(f1(t s))]
runLGG c = runST (runListT' (lift . mapM2 zonkTerm' =<< c))

runLIO :: ListT' (ST RealWorld) a -> IO [a]
runLIO = stToIO . runListT'

-- ---------------------------------------------------
-- TRS instances
-- ---------------------------------------------------
instance (Term t s user, TermShape s) => TRS.TRS t s [] user where
  {-# SPECIALIZE instance TRS.TRS (TermStatic_ Int) BasicShape [] user #-}
  rewrite  rr t    = runLWithSubst (rewrite rr  =<< lift(templateTerm' t))
  rewrite1 rr t    = runLWithSubst (rewrite1 rr =<< lift(templateTerm' t))
  narrow1  rr t    = runLWithSubst (narrow1 rr =<< lift(templateTerm' t))
  unify t u        = runLG (manualUnify t u)

instance (Term t s user, GoodShape s) => TRS.TRSN t s user where
--  narrow1'    rr t = runSTWithSubst (narrow1' rr (templateTerm t))
  narrowBasic rr t = runSTWithSubst ((fmap freeGT *** freeGT) `fmap2` 
                                        (narrowBasic rr =<< templateTerm' t))
  narrowFull rr t  = runSTWithSubst (narrowFull rr =<< templateTerm' t)
  narrowFullBounded pred rr t = 
      let pred' = (return . pred) <=< zonkTerm' <=< dupTerm in
      runSTWithSubst (narrowFullBounded pred' rr =<< templateTerm' t)

instance (Term t s user, TermShape s) => TRS.TRS t s Maybe user where
  {-# SPECIALIZE instance TRS.TRS (TermStatic_ Int) BasicShape Maybe user #-}
  rewrite  rr t    = runMWithSubst (rewrite rr  =<< lift (templateTerm' t))
  rewrite1 rr t    = runMWithSubst (rewrite1 rr =<< lift (templateTerm' t))
  narrow1  rr t    = runMWithSubst (narrow1 rr =<< lift (templateTerm' t))
  unify t u        = runMG (manualUnify t u)
instance OmegaPlus Normal t r s => 
    TRS.TRS (GT_ user Normal r) s (t (ST r)) user where
  {- SPECIALIZE instance TRS.TRS (GT_ user Normal r) BasicShape (ListT (ST r))  user #-}
  {- SPECIALIZE instance TRS.TRS (GT_ user Normal r) BasicShape (MaybeT (ST r)) user #-}
  unify t t'    = manualUnify' t t'
  rewrite       = rewrite
  rewrite1      = rewrite1
  narrow1    rr = narrow1 rr

runSTWithSubst :: (Term t s user, Omega Normal (ListT') r s) =>
                          (forall r. ST r [(Subst user r s, GT user r s)])
                      -> [(SubstM (t s), t s)]
runSTWithSubst m = runST (mapM (biM zonkSubst zonkTerm') =<< m)

runLWithSubst :: (Term t s user, Omega Normal (ListT') r s) =>
                          (forall r. ListT' (ST r) (Subst user r s, GT user r s))
                      -> [(SubstM (t s),t s)]
runLWithSubst m = runST (runListT' (runWithSubst m))

runMWithSubst :: (Term t s user, Omega Normal MaybeT r s) =>
                          (forall r. MaybeT (ST r) (Subst user r s, GT user r s))
                      -> Maybe (SubstM (t s),t s)
runMWithSubst m = runST (runMaybeT (runWithSubst m))

runWithSubst ::  (Term t s user, Omega mode m r s) =>
                          (m (ST r) (Subst user r s, GT_ user mode r s))
                        -> m (ST r) (SubstM (t s),t s)
runWithSubst m = lift . biM zonkSubst zonkTerm' =<< m

zonkSubst :: (Prune mode, Term t s user) =>
             (Subst_ user mode r s) -> ST r (SubstM (t s))
zonkSubst = zonkTermG'

{-
manualUnify :: Term t s user =>
               GT_ user mode r s -> GT_ user mode r s -> m (ST r) (Subst_ user mode r s)
-}
manualUnify t u = do
  t_ <- lift$ templateTerm' t
  u_ <- lift$ templateTerm' u
  (subst, [t',u']) <- lift$ autoInstG [t_,u_]
  unify t' u'
  return subst

-- I know, I'm going to burn in hell...
manualUnify' :: Omega mode m r s => 
               GT_ user mode r s -> GT_ user mode r s -> m (ST r) (Subst_ user mode r s)
manualUnify' t u = do
  t_ <- lift$ templateTerm' t
  u_ <- lift$ templateTerm' u
  return (isGT t_)
  (_,[t',u']) <- lift$ autoInstG [t_,u_]
  let mvars = [ v | MutVar{ref=v} <- collect isMutVar t, t <- [t',u']]
  mvars_indexes <- lift$ catMaybes <$> forM mvars getUnique
  let skolem_offset = maximum (0 : mvars_indexes)
  unify t' u'
  indexes <- lift$ forM mvars $ \v -> 
             readVar' v >>= \x -> 
             return$ case x of
               Empty Nothing      -> fromJust(elemIndex v mvars) + skolem_offset
               Empty (Just i)     -> i
               Mutable (Just i) _ -> i
               Mutable Nothing  _ -> fromJust(elemIndex v mvars) + skolem_offset
  return (mkSubstM indexes (map (MutVar Nothing) mvars))

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
class (Omega mode t r s, MonadPlus (t (ST r))) => 
    OmegaPlus mode t r s 

instance ( MonadError (TRSException) (t (ST r)), MonadTrans t, Monad (t (ST r)), Functor (t (ST r)), TermShape s, Prune mode) => Omega mode t r s
instance ( Omega mode t r s, MonadPlus (t (ST r))) => OmegaPlus mode t r s

----------------
-- Other stuff
----------------

someSubterm :: (Traversable t, MonadPlus m) => (a -> m a) -> t a -> m (t a)
someSubterm f x = msum$ interleave f return x

instance Show (GT_ user eq r s) => Observable (GT_ user eq r s) where
    observer = observeBase


{-# INLINE fail1 #-}
fail1 :: Monad m => String -> m a 
--fail1 msg = trace msg $ fail msg
fail1 = fail

-- TODOs:
-- - Float pruning to the type

st :: (TermShape s, Show (s (TermStatic s))) => GT_ user mode r s -> String 
st = show . zonkTermS'
sr ::  (Functor f, TermShape s, Show (f (TermStatic s))) =>
      f (GT_ user mode r s) -> String
sr = show . fmap zonkTermS'

