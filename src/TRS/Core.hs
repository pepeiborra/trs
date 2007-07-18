{-# OPTIONS_GHC -fglasgow-exts #-}
{-# OPTIONS_GHC -fallow-undecidable-instances #-}
{-# OPTIONS_GHC -fallow-overlapping-instances #-}
{-# OPTIONS_GHC -fno-monomorphism-restriction #-}
{-# OPTIONS_GHC -fglasgow-exts  #-}

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


module TRS.Core where

import Control.Applicative
import Control.Arrow ( first, second, (>>>))
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

import TRS.Types hiding (Term)
import TRS.Term  hiding (TRS(..), TRSN(..))
import qualified TRS.Term as Term
import {-# SOURCE #-} TRS.Terms
import TRS.Context
import TRS.Utils

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

-- --------------------
-- GT Term structure
-- --------------------
instance (TermShape s, Foldable s) => Term (GT_ eq r) s where
  {-# SPECIALIZE instance Term (GT_ eq r) BasicShape #-}
  isVar S{}      = False
  isVar _        = True
  mkVar          = GenVar
  varId (GenVar i) = i
  varId (CtxVar i) = i
  varId (MutVar i) = error "unexpected mutvar"
  subTerms (S x) = toList x
  subTerms _     = []
  synEq (MutVar r1) (MutVar r2) = r1 == r2 
  synEq (GenVar n) (GenVar m)   = m==n
  synEq (CtxVar n) (CtxVar m)   = m==n
  synEq (S x) (S y) | Just pairs <- matchTerm x y 
                    = all (uncurry synEq) pairs 
  synEq _ _         = False
  fromSubTerms (S t) tt = S $ modifySpine t tt
  fromSubTerms t _      = t
  fromGTM _      = unsafeCoerce#
  mkGTM _        = unsafeCoerce#

mutableTerm :: Term t s => t s -> ST r (GT r s)
mutableTerm t = do 
  freshvars <- replicateM (length$ vars_t) fresh 
  return$ mkGT (fromJust . (`lookup` zip vars_t freshvars) . SynEq) t
    where vars_t = SynEq <$> vars t

mutableTermG :: (Traversable f, Term t s) => f(t s) -> ST r (f(GT r s))
mutableTermG = fmap snd . autoInstG_ . fmap templateTerm

noCVars, noGVars, noMVars :: (TermShape s, Foldable s) => GT_ mode r s -> Bool
noGVars = null . collect isGenVar 
noMVars = null . collect isMutVar 
noCVars = null . collect isCtxVar

mkVarsForTerm :: (TermShape s, Foldable s) => GT_ eq r s -> ST r (Subst_ eq r s)
mkVarsForTerm t | null vars_t = return emptyS
                | otherwise   = do
    newvars <- replicateM (topvar+1) fresh 
    return (Subst newvars)
   where vars_t = vars t
         topvar = maximum [ i | GenVar i <- vars_t ]

---------------------------
-- * External Interface
---------------------------
-- This is the intended user API for this module
-- Below we expose versions of the functions we have defined before
--  which take have GTE types in signatures instead of GT. 

--fixRules :: (TermShape s, Functor s) => [Rule s] -> [Rule_ mode r s]
fixRules = fmap2 templateTerm
fixRulesB :: (TermShape s, Functor s) => [Rule s] -> [RuleG (GT_ Basic r s)]
fixRulesB = fixRules

unify	  :: Omega Semantic m r s => GTE r s -> GTE r s -> m (ST r) ()
unify = unify_

match	  :: Omega Semantic m r s => GTE r s -> GTE r s -> m (ST r) ()
match = match_

-- | Instantiates a type scheme with the given substitution
instan	  :: TermShape s => Subst r s -> GTE r s -> ST r (GTE r s)
instan = instan_

-- |leftmost outermost
rewrite1  :: OmegaPlus Semantic m r s => [Rule s] -> GTE r s -> m (ST r) (GTE r s)
rewrite1 rre = rewrite1_ (fixRules rre)

-- |leftmost outermost
rewrite   :: OmegaPlus Semantic m r s => [Rule s] -> GTE r s -> m (ST r) (GTE r s)
rewrite  rre = rewrite_ (fixRules rre)

-- |leftmost outermost
narrow1   :: OmegaPlus Semantic m r s => [Rule s] -> GTE r s -> 
             m (ST r) (Subst r s, GTE r s)
narrow1 rr = narrow1_ (fixRules rr)

-- |leftmost outermost
narrow1' :: (GoodShape s) => [Rule s] -> GTE r s -> ST r [(Subst r s, GTE r s)]
narrow1' rr = narrow1'_ (fixRules rr)

-- |leftmost outermost, in variables too
narrow1V :: (GoodShape s) => [Rule s] -> GTE r s -> ST r [(Subst r s, GTE r s)]
narrow1V rr = narrow1V_ (fixRules rr)

narrowFull:: (GoodShape s) => [Rule s] -> GTE r s -> 
             ST r [(Subst r s, GTE r s)]
narrowFull rr = narrowFull_ (fixRules rr)

narrowBasic rr term = narrowBasic_ (fixRules rr) 
                            (basicGT$ templateTerm term)

narrowFullV:: GoodShape s => [Rule s] -> GTE r s -> ST r [(Subst r s, GTE r s)]
narrowFullV rr = narrowFullV_ (fixRules rr)

narrowFullBounded  :: GoodShape s => 
                      (GTE r s -> ST r Bool) -> [Rule s] -> GTE r s -> 
                      ST r [(Subst r s, GTE r s)]
narrowFullBounded pred rr = narrowFullBounded_ (pred . eqGT) (fixRules rr)

narrowFullBoundedV :: GoodShape s => 
                      (GTE r s -> ST r Bool) -> [Rule s] -> GTE r s -> 
                      ST r [(Subst r s, GTE r s)]
narrowFullBoundedV pred rr = narrowFullBoundedV_ (pred . eqGT) (fixRules rr)

-- | generalize builds a sigma type, i.e. a type scheme, by 
--   replacing all mutvars in a term with GenVars
generalize :: TermShape s => GTE r s -> ST r (GTE r s)
generalize = generalize_

generalizeG::(TermShape s, Traversable f) => f(GTE r s) -> ST r (f(GTE r s))
generalizeG = generalizeG_

generalizeGG = generalizeGG_

-- | autoInst instantitates a type scheme with fresh mutable vars
--   Returns the instantiated term together with the new MutVars 
--  (you need these to apply substitutions) 
autoInst  :: (TermShape s) => GTE r s -> ST r (Subst r s, GTE r s)       
autoInst = autoInst_ 

rewrite1_ :: OmegaPlus mode m r s => [Rule_ mode r s] -> GT_ mode r s -> m (ST r) (GT_ mode r s)
rewrite_  :: OmegaPlus mode m r s => [Rule_ mode r s] -> GT_ mode r s -> m (ST r) (GT_ mode r s)
narrow1_  :: OmegaPlus mode m r s => [Rule_ mode r s] -> GT_ mode r s -> 
             m (ST r) (Subst_ mode r s, GT_ mode r s)
narrow1'_ :: (GoodShape s, Prune mode) => [Rule_ mode r s] -> GT_ mode r s 
             -> ST r [(Subst_ mode r s, GT_ mode r s)]

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

generalize_ ::(Prune mode, TermShape s) => GT_ mode r s -> ST r (GT_ mode r s)
generalizeG_::(Prune mode, TermShape s,Traversable f) => 
               f(GT_ mode r s) -> ST r (f(GT_ mode r s))
generalizeGG_::(Prune mode, TermShape s, Traversable f, Traversable f') => 
               f'(f(GT_ mode r s)) -> ST r (f'(f(GT_ mode r s)))

autoInst_ :: (Prune mode, TermShape s) => GT_ mode r s -> ST r (Subst_ mode r s, GT_ mode r s)       
autoInstG_:: (Traversable s, Traversable f, TermShape s, Prune mode) =>
               f(GT_ mode r s) -> ST r (Subst_ mode r s, f(GT_ mode r s))


-- * Basic primitives
unify_	  :: Omega mode m r s => GT_ mode r s -> GT_ mode r s -> m (ST r) ()
match_	  :: Omega mode m r s => GT_ mode r s -> GT_ mode r s -> m (ST r) ()

-----------------------------
-- * The underlying machinery
------------------------------

class Prune (mode :: *) where prune :: GT_ mode r s  -> ST r (GT_ mode r s)
instance Prune Basic     where prune x = pruneBasic_ x
instance Prune Syntactic where prune x = prune_ x
instance Prune Semantic  where prune x = prune_ x
instance TypeEq Syntactic mode HTrue => Prune mode where prune x = prune_ x

{-# INLINE prune_ #-}
prune_ (typ @ (MutVar ref)) =
	do { m <- readVar ref
	   ; case m of
	      Just t ->
		do { newt <- prune_ t
		   ; write ref (Just newt)
		   ; return newt }
	      Nothing -> return typ}
prune_ x = return x

pruneBasic_ (typ @ (MutVar ref)) =
	do { m <- readVar ref               -- One could make this block a one liner: 
	   ; case m of                      -- mapM (prune_ >=> write ref . Just)
	      Just t ->                      --     =<< readVar ref
		do { newt <- pruneBasic_ t       -- return typ
		   ; write ref (Just newt)  -- (note the mapM is in the Maybe monad)
		   ; return typ }
	      Nothing -> return typ}
pruneBasic_ x = return x

col :: (Prune mode, Traversable s) => GT_ mode r s  -> ST r (GT_ mode r s)    
col x =
     do { x' <- prune x
	; case x' of
	  (S y) -> 
	    do { t <- (mapM col y) 
	       ; return (S t)} 
	  _     -> return x'}
occurs v t = 
     do { t2 <- lift$ prune t 
	; case t2 of 
	  S w -> 
	    do { s <- (mapM (occurs v) w) 
	       ; return(foldr (||) False s ) 
	       } 
	  MutVar z -> return (v == z) 
	  _ -> return False } 

unify_ tA tB = 
     do  t1 <- lift$ prune tA 
	 t2 <- lift$ prune tB 
	 case (t1,t2) of 
	   (MutVar r1,MutVar r2) -> 
	     if r1 == r2 
		then return () 
		else lift$ write r1 (Just t2) 
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
		  mapM_ (uncurry unify_) pairs 
	   (x,y) -> throwError genErrorUnify -- (shapeErrorUnify tA tB)

varBind :: Omega mode m r s => Ptr_ mode r s -> GT_ mode r s -> m (ST r) ()
varBind r1 t2 = 
     do { b <- occurs r1 t2 
	; if b 
	    then throwError occursError
	    else lift$ write r1 (Just t2) } 

-- | match_ tA tB | trace ("match " ++ show tA ++ " and " ++ show tB) False = undefined
match_ tA tB = 
     do { t1 <- lift$ prune tA 
	; t2 <- lift$ prune tB 
	; case (t1,t2) of 
	  (MutVar r1,_) -> 
	    lift$ write r1 (Just t2) 
	  (GenVar n,GenVar m) -> 
	    if n==m 
		then return () 
		else throwError genErrorMatch
	  (S x,S y) -> 
	    case matchTerm x y of 
		Nothing -> throwError genErrorMatch
		Just pairs -> 
		  mapM_ (uncurry match_) pairs 
	  (_,_) -> throwError shapeErrorMatch 
	} 

class Instan term subst monad | term -> monad where 
  instan_ :: subst -> term -> monad term
  
instance (Prune mode, Traversable s) => Instan (GT_ mode r s) (Subst_ mode r s) (ST r) where
  instan_ sub t = do --prune >=> instan_ sub . DontCol >=> col . unDontCol  
      t1 <- prune t
      DontCol t2 <- instan_ sub (DontCol t1)
      col t2

newtype DontCol a = DontCol {unDontCol::a}
instance (Prune mode, Traversable s) => Instan (DontCol(GT_ mode r s)) (Subst_ mode r s) (ST r) where
  instan_ sub (DontCol x) = DontCol <$> instanDontCol x
    where
     instanDontCol x = do
         { case x of 
	    GenVar n | n `atLeast` (subst sub) -> return$ (subst sub !! n)
	    S x -> S <$> (mapM instanDontCol x) 
            _ -> return x
	 } 

instance (Prune mode, Traversable s) => Instan (GT_ mode r s) [(Int, GT_ mode r s)] (ST r) where
  instan_ sub x = do
    x' <- prune x
    case x' of
      GenVar n | Just val <- lookup n sub -> col $! val
      S x -> S <$> (instan_ sub `mapM` x) 
      _   -> return x'

instance (Prune mode, Traversable s) => Instan (GT_ mode r s) [Maybe (GT_ mode r s)] (ST r) where
  instan_ sub x = 
      do { x' <- prune x 
	 ; case x' of 
	    GenVar n | n `atLeast` sub
                     , Just val <- sub !! n -> col $! val
	    S x -> fmap S (mapM (instan_ sub) x) 
            _ -> return x'
	 } 
  

--generalize_ x | trace ("generalize " ++ show x ) False = undefined
generalize_ x = do
           x' <- col x
           let gvars = collect isGenVar x'
               mvars = collect isMutVar x'
               tot   = length gvars + length mvars
               new_gvars = map GenVar
                               ([0..tot]\\[j|GenVar j <- gvars])
           let x'' = replace (zip mvars new_gvars) x'
           assert (noMVars x'') (return ())
           return x''

generalizeG_ x = do
  x' <- mapM col x
  let gvars = nubSyntactically $ concat (toList (collect isGenVar <$> x'))
      mvars = nubSyntactically $ concat (toList (collect isMutVar <$> x'))
      tot   = length gvars + length mvars
      new_gvars = map GenVar ([0..tot]\\[j|GenVar j <- gvars])
      x''   = replace (zip mvars new_gvars) <$> x'
  assert (all noMVars x'') (return ())
  return x''

generalizeGG_ x = do
           x' <- mapM2 col x
           let gvars = nubSyntactically $ concat2 (toList2 (fmap2 (collect isGenVar) x'))
               mvars = nubSyntactically $ concat2 (toList2 (fmap2 (collect isMutVar) x'))
               tot   = length gvars + length mvars
               new_gvars = map GenVar
                               ([0..tot]\\[j|GenVar j <- gvars])
           let x'' = fmap2 (replace (zip mvars new_gvars)) x'
           assert (all (and . fmap noMVars) x'') (return ())
           return x''

nubSyntactically = map unSynEq . nub . map SynEq

--autoInst_ x | trace ("autoInst " ++ show x) False = undefined
autoInst_ x@MutVar{} = return (emptyS, x)
autoInst_ x
    | null gvars = return (emptyS, x)
    | otherwise  = do
           freshv <- mkVarsForTerm x
           x' <- instan_ freshv x
           assert (noGVars x') (return ())
           x' `seq` return (freshv, x')
    where gvars = collect isGenVar x


autoInstG_ xx | null vv = return (Subst [], xx)
              | otherwise = do
  freses <- Subst <$> replicateM (succ topIndex) fresh 
  xx' <- instan_ freses `mapM` xx
  assert (all noGVars xx') (return ())
  return (freses, xx')
    where topIndex = List.maximum vv
          vv = [ i | GenVar i <- concatMap vars xx]

autoInstGG_ xx | null vv = return (Subst [], xx)
               | otherwise = do
  freses <- Subst <$> replicateM (succ topIndex) fresh 
  xx' <- instan_ freses `mapM2` xx
  return (freses, xx')
    where topIndex = List.maximum vv
          vv = [ i | GenVar i <- concatMap2 vars xx]

-- |Semantic equality (equivalence up to renaming of vars) 
semEq :: (Prune mode, TermShape s) => GT_ mode r s -> GT_ mode r s -> ST r Bool
semEq x y = do
    [x',y'] <- mapM (autoInst_ >=> (generalize_ . snd)) [x,y]
    return (x' `synEq` y')

--semEqG :: (TermShape s) => GT_ eq r s -> GT_ eq r s -> ST r Bool
semEqG x y = do
    [x',y'] <- mapM (autoInstG_ >=> (generalizeG_ . snd)) [x,y]
    return (synEq <$> x' <*> y')

--semEqG x y = return$ synEq x y

---------------------------------------------------------------
-- * Pure (partial) Semantic Equality for GTE 
--       (based on zonking to an equivalent TermStatic)
---------------------------------------------------------------
instance TermShape s => Eq (GTE r s) where
  (==) = semEq'

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
	        (freshv, lhs') <- lift$ autoInst_ lhs
	        match_ lhs' t
                lift$ instan_ freshv rhs

rewrite1_ _ t = mzero

rewrite_ rules = fixM (rewrite1_ rules)

--narrow1_ _ t | trace ("narrow1 " ++ show t) False = undefined
narrow1_ [] t = mzero -- fail1 "narrow1: empty set of rules"
narrow1_ _ t | assert (noMVars t) False = undefined
narrow1_ rules t@S{} = go (t, emptyC)
    where go (t, ct) = 
              narrowTop rules ct t
             `mplus` 
              msum ( map (\(t, ct1) -> go (t, ct|>ct1) ) (contexts t))
narrow1_ rules _ = mzero -- fail "narrow1: No Narrowing at vars"

{-
narrowTop,narrowTopV :: OmegaPlus Syntactic m r s => [RuleI r s] -> Context r s -> GT r s
                            -> m (ST r) (Subst r s, GT r s)
unsafeNarrowTop, unsafeNarrowTopV
    :: OmegaPlus Syntactic m r s => [RuleI r s] -> Context r s -> GT r s
                            -> m (ST r) (Subst r s, GT r s)
-}
narrowTop  rules ct t = assert (all noMVars [t, ct])$ unsafeNarrowTop rules ct t
narrowTopV rules ct t = assert (all noMVars [t, ct])$ unsafeNarrowTopV rules ct t
unsafeNarrowTop   = unsafeNarrowTopG narrowTop1
unsafeNarrowTopV  = unsafeNarrowTopG narrowTop1V


-- unsafeNarrowTopG _ _ _ t | trace ("unsafeNarrowTop " ++ show t) False = undefined
unsafeNarrowTopG narrowTop1 rules ct t = msum$ forEach rules $ \r -> do
               (vars, [t',ct']) <- lift$ autoInstG_ [t,ct]
               t''              <- narrowTop1 t' r
               return (vars, ct'|>t'')

narrowTop1, narrowTop1V :: OmegaPlus mode m r s => GT_ mode r s -> Rule_ mode r s 
                        -> m (ST r) (GT_ mode r s)
narrowTop1V t r@(lhs:->rhs) = do
               assert (noGVars t) (return ())
               assert (noMVars lhs) (return ())
               assert (noMVars rhs) (return ())
               assert (vars (idGT rhs) `isSubsetOf` vars (idGT lhs)) (return ())
               (lhsv, lhs') <- lift$ autoInst_ lhs
               unify_ lhs' t
               trace ("narrowing fired: t=" ++ st t ++ ", rule=" ++ sr r
--                   ++   ", rho= " ++ show (zonkTermS lhsv)
                      )(return ()) 
               rhs'  <- lift$ instan_ lhsv rhs
               rhs'' <- lift$ col rhs'      -- OPT: col here might be unnecesary
--             assert (noGVars rhs'') (return ())
               return rhs''
narrowTop1 t@S{} r = narrowTop1V t r
narrowTop1 _ _     = mzero -- throwError "No narrowing at vars"

-------------------------------
-- * The Full Narrowing Framework
-------------------------------
narrow1'_ = narrowFullBase narrowTop'  (const (return True)) 
narrow1V_ = narrowFullBase narrowTopV' (const (return True)) 

narrowFull_  = narrowFullBase narrowTop' (const (return False))
narrowBasic_ rules = narrowFull_ (fmap2 basicGT rules) . basicGT

narrowFullV_ = narrowFullBase narrowTopV' (const (return False))
narrowFullBounded_  = narrowFullBase narrowTop'
narrowFullBoundedV_ = narrowFullBase narrowTopV'

{-
narrowFullBase :: forall r s. (TermShape s, Show (s(GT r s))) =>
              ([RuleI r s] -> Context r s -> Subst r s -> GT r s
               -> forall r1. LogicT'.SG r1 (ST r) (Subst r s, GT r s))
            -> (GT r s -> ST r Bool)
            -> [RuleI r s] -> GT r s 
            -> ST r [(Subst r s, GT r s)]
-}

newtype Ind = Ind Int deriving (Num,Enum, Eq)
instance Show Ind where show (Ind i) = " (" ++ show i ++ ") "

narrowFullBase _ done [] t = -- trace ("narrowFull " ++ show t ++ " with empty TRS")$ 
                           return []
narrowFullBase narrowTop1base done rules t = do 
     assert (noMVars t) (return ())
     (subst0,t0) <- autoInst_ t
     -- nubByM (semEq `at` snd) =<< 
     LogicT.runM Nothing (search (Ind 0) (subst0, t0))
  where   
--   search :: (Subst r s, GT r s) -> LogicT'.SR r1 (ST r) (T2(Subst r s) (GT r s))
   search ind (subst,t) = trace ("narrowFull search: " ++ show ind  ++ st t) $ 
       LogicT.ifte  (step emptyC subst t)
                    (\x@(sub',t') -> trace ("branch " ++ show ind ++ st t') $ 
                               lift (done (idGT t)) >>- \isDone -> 
                               if isDone then return (sub',t') else 
                                   search (succ ind) x)
                    (trace ("leaf" ++ show ind ++ st t) $ 
                         return (subst,t))
   step cs subst t = trace ("narrowFull step: " ++ st t) $
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
narrowTop'  = narrowTopBase narrowTop1
narrowTopV' = narrowTopBase narrowTop1V

-- narrowTopBase' _ _ _ _  t | trace ("NarrowTop' " ++ show t) False = undefined
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
dupVar sr = readSTRef sr >>= newSTRef
dupTerm (MutVar r) = fmap MutVar (dupVar r)
dupTerm (S t) = fmap S $ mapM dupTerm t
dupTerm x = return x

--dupTermWithSubst subst tt x | trace "dupTermWithSubst" False = undefined
{-
dupTermWithSubst :: (Eq (GT r s), TermShape s) => 
                    Subst r s -> [GT r s] -> GT r s 
                 -> ST r (Subst r s, [GT r s], GT r s)
-}
dupTermWithSubst subst tt t@MutVar{} = do
    t'        <- dupTerm t
    let dict   = [(t,t')]
        subst' = liftSubst (fmap (replace dict)) subst
        tt'    = fmap (replace dict) tt
    return (subst', tt', t')

dupTermWithSubst subst tt t@S{} = do
    let mutvars= collect isMutVar t
    newvars   <- mapM dupTerm mutvars
    let dict   = zip mutvars newvars
        t'     = replace dict t
        tt'    = fmap (replace dict) tt
        subst' = liftSubst (fmap(replace dict)) subst
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
  rewrite  rr t    = runL (rewrite rr (templateTerm t))
  rewrite1 rr t    = runL (rewrite1 rr (templateTerm t))
  narrow1  rr t    = runLWithSubst (narrow1    rr (templateTerm t))

instance (Term t s, GoodShape s) => Term.TRSN t s where
  narrow1'    rr t = runSTWithSubst (narrow1' rr (templateTerm t))
  narrowBasic rr t = runSTWithSubst (bi (fmap freeGT) freeGT `fmap2` narrowBasic rr (templateTerm t))
  narrowFull rr t  = runSTWithSubst (narrowFull rr (templateTerm t))
  narrowFullBounded pred rr t = 
      runSTWithSubst (narrowFullBounded ((pred <$>). zonkTerm') rr (templateTerm t))  

instance (Term t s, GoodShape s) => Term.TRS t s Maybe where
  rewrite  rr t    = runM (rewrite rr (templateTerm t))
  rewrite1 rr t    = runM (rewrite1 rr (templateTerm t))
  narrow1  rr t    = runMWithSubst (narrow1    rr (templateTerm t))

instance OmegaPlus Semantic t r s => Term.TRS (GT_ Semantic r) s (t (ST r)) where
  rewrite       = rewrite
  rewrite1      = rewrite1
  narrow1    rr = (first (zonkTerm <$>) <$>) . narrow1 rr

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

zonkSubst = mapM (fmap zonkTerm . col)

--------------------------------------
-- * The Omega type class and friends
--------------------------------------
-- |"Omega is just a Type Class constraint synonym" 
class (TermShape s, Show (s (TermStatic s))) => GoodShape s
instance (TermShape s, Show (s (TermStatic s))) => GoodShape s

#ifdef __HADDOCK__
class ( MonadError (TRSException) (t (ST r)), MonadTrans t, Monad (t (ST r)), Functor (t (ST r)), TermShape s) => Omega mode t r s
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


fmap2 f x = fmap (fmap  f) x
fmap3 f x = fmap (fmap2 f) x 
mapM2 f = mapM (mapM f)
concat2 = concat . concat
toList2 = map toList . toList
concatMap2 f = concat . concat . fmap (fmap f)
sequence2 = sequence . fmap sequence
sequence3 = sequence . fmap sequence2

st = show . zonkTermS'
sr = show . fmap zonkTermS'