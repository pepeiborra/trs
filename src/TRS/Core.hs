{-# OPTIONS_GHC -fglasgow-exts -fallow-undecidable-instances #-}
{-# OPTIONS_GHC -fallow-overlapping-instances #-}
{-# OPTIONS_GHC -fno-monomorphism-restriction #-}


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
import Control.Monad hiding (msum, mapM_, mapM, sequence, forM)
import Control.Monad.Error (MonadError(..), ErrorT(..), MonadTrans(..))
import Control.Monad.State (StateT(..), MonadState(..), gets, modify, lift)
import Control.Monad.Fix (MonadFix(..))
import Control.Exception (assert)
import Test.QuickCheck (Arbitrary(..))
import Data.List ((\\), nub, elemIndex)
import Data.Traversable
import Data.Foldable
import Data.Maybe 
import Data.Monoid
import Prelude hiding ( all, maximum, minimum, any, mapM_,mapM, foldr, foldl
                      , and, concat, concatMap, sequence, elem, notElem)

import TRS.Types 
import TRS.Term
import TRS.Terms
import TRS.Context
import TRS.Utils

import GHC.Exts (unsafeCoerce#)
import Observe
import qualified Debug.Trace

instance TermShape s => Eq (GT s r) where
  (==) = synEq   -- syntactic equality

{-# SPECIALIZE prune_ :: GT BasicShape r -> ST r (GT BasicShape r) #-}

---------------------------
-- * External Interface
---------------------------
-- This is the intended user API for this module
-- Below we expose versions of the functions we have defined before
--  which take have GTE types in signatures instead of GT. 

--liftGTE2 :: (GT s r -> GT s r -> a) -> GTE s r -> GTE s r -> a
liftGTE2 f x y =  f (idGT x) (idGT y)
--liftGTE :: Functor f => (GT s r -> f(GT s r)) -> GTE s r -> f(GTE s r)
liftGTE f = fmap eqGT . f . idGT
fixRules :: Functor s => [Rule s] -> [RuleI s r]
fixRules = map $ \(t :-> s) -> templateTerm t :-> templateTerm s
adaptSubstitutionResult f rre t = fmap (second eqGT) $ f (fixRules rre) (idGT t)

prune	  :: GTE s r -> ST r (GTE s r)
prune = liftGTE prune_

unify	  :: Omega m s r => GTE s r -> GTE s r -> m (ST r) ()
unify = liftGTE2 unify_

match	  :: Omega m s r => GTE s r -> GTE s r -> m (ST r) ()
match = liftGTE2 match_

-- | Instantiates a type scheme with the given substitution
instan	  :: TermShape s => Subst s r -> GTE s r -> ST r (GTE s r)
instan s = liftGTE (instan_ s)

rewrite1  :: OmegaPlus m s r => [Rule s] -> GTE s r -> m (ST r) (GTE s r)
rewrite1 rre = liftGTE (rewrite1_ (fixRules rre))

rewrite   :: OmegaPlus m s r => [Rule s] -> GTE s r -> m (ST r) (GTE s r)
rewrite  rre = liftGTE (rewrite_ (fixRules rre))

narrow1   :: OmegaPlus m s r => [Rule s] -> GTE s r -> 
             m (ST r) (Subst s r, GTE s r)
narrow1 = adaptSubstitutionResult narrow1_

narrow1',narrow1V 
          :: (OmegaPlus m s r) => [Rule s] -> GTE s r -> 
             m (ST r) (Subst s r, GTE s r)
narrow1' = adaptSubstitutionResult narrow1'_
narrow1V = adaptSubstitutionResult narrow1V_

narrowFull:: (OmegaPlus m s r) => [Rule s] -> GTE s r -> 
             m (ST r) (Subst s r, GTE s r)
narrowFull = adaptSubstitutionResult narrowFull_

narrowFullV:: (OmegaPlus m s r) =>
              [Rule s] -> GTE s r -> m (ST r) (Subst s r, GTE s r)
narrowFullV = adaptSubstitutionResult narrowFullV_
narrowFullBounded  :: (OmegaPlus m s r) =>
                      (GTE s r -> ST r Bool) -> [Rule s] -> GTE s r -> 
                      m (ST r) (Subst s r, GTE s r)
narrowFullBounded pred = adaptSubstitutionResult (narrowFullBounded_ (pred . eqGT))
narrowFullBoundedV :: (OmegaPlus m s r) =>
                      (GTE s r -> ST r Bool) -> [Rule s] -> GTE s r -> 
                      m (ST r) (Subst s r, GTE s r)
narrowFullBoundedV pred = adaptSubstitutionResult (narrowFullBoundedV_ (pred . eqGT))

-- | generalize builds a sigma type, i.e. a type scheme, by 
--   replacing all mutvars in a term with GenVars
generalize :: TermShape s => GTE s r -> ST r (GTE s r)
generalize = liftGTE generalize_

generalizeG::(TermShape s, Traversable f) => f(GTE s r) -> ST r (f(GTE s r))
generalizeG = fmap2 eqGT . generalizeG_  . fmap idGT

generalizeGG = fmap3 eqGT . generalizeGG_ . fmap2 idGT

-- | autoInst instantitates a type scheme with fresh mutable vars
--   Returns the instantiated term together with the new MutVars 
--  (you need these to apply substitutions) 
autoInst  :: TermShape s => GTE s r -> ST r (Subst s r, GTE s r)       
autoInst t = fmap (second eqGT) $ autoInst_ (idGT t)

-----------------------------
-- * The underlying machinery
------------------------------
-- |leftmost outermost
rewrite1_ :: OmegaPlus m s r => [RuleI s r] -> GT s r -> m (ST r) (GT s r)
rewrite_  :: OmegaPlus m s r => [RuleI s r] -> GT s r -> m (ST r) (GT s r)
narrow1_  :: OmegaPlus m s r => [RuleI s r] -> GT s r -> 
             m (ST r) (Subst s r, GT s r)
narrow1'_ :: (OmegaPlus m s r) => [RuleI s r] -> GT s r -> 
             m (ST r) (Subst s r, GT s r)

-- |leftmost outermost, on variables too (paramodulation)
narrow1V_
          :: (OmegaPlus m s r) => [RuleI s r] -> GT s r -> 
             m (ST r) (Subst s r, GT s r)

-- |Unbounded Full Narrowing
narrowFull_ :: (OmegaPlus m s r) => [RuleI s r] -> GT s r -> 
             m (ST r) (Subst s r, GT s r)

-- |Unbounded Full Paramodulation
narrowFullV_ :: (OmegaPlus m s r) =>
              [RuleI s r] -> GT s r -> m (ST r) (Subst s r, GT s r)

-- | Bounded versions. The first argument is the bound checking predicate
narrowFullBounded_ :: (OmegaPlus m s r) =>
                      (GT s r -> ST r Bool) -> [RuleI s r] -> GT s r -> 
                      m (ST r) (Subst s r, GT s r)
narrowFullBoundedV_:: (OmegaPlus m s r) =>
                      (GT s r -> ST r Bool) -> [RuleI s r] -> GT s r -> 
                      m (ST r) (Subst s r, GT s r)

generalize_ ::TermShape s => GT s r -> ST r (GT s r)
generalizeG_::(TermShape s,Traversable f) => f(GT s r) -> ST r (f(GT s r))
generalizeGG_::(TermShape s, Traversable f, Traversable f') => 
               f'(f(GT s r)) -> ST r (f'(f(GT s r)))

autoInst_ :: TermShape s => GT_ eq s r -> ST r (Subst_ eq s r, GT_ eq s r)       
autoInstG_:: (Traversable s, Traversable f, TermShape s) =>  
               f(GT_ eq s r) -> ST r (Subst_ eq s r, f(GT_ eq s r))


-- * Basic primitives
unify_	  :: Omega m s r => GT s r -> GT s r -> m (ST r) ()
match_	  :: Omega m s r => GT s r -> GT s r -> m (ST r) ()

-- ** Dereference variables
prune_	  :: GT_ eq s r  -> ST r (GT_ eq s r)
col 	  :: Traversable s => GT_ eq s r  -> ST r (GT_ eq s r)    
instan_	  :: Traversable s => Subst_ eq s r-> GT_ eq s r -> ST r (GT_ eq s r)

occurs	  :: Omega m s r => Ptr_ eq s r -> GT_ eq s r ->m (ST r) Bool

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

col x =
     do { x' <- prune_ x
	; case x' of
	  (S y) -> 
	    do { t <- (mapM col y) 
	       ; return (S t)} 
	  _     -> return x'}
occurs v t = 
     do { t2 <- lift$ prune_ t 
	; case t2 of 
	  S w -> 
	    do { s <- (mapM (occurs v) w) 
	       ; return(foldr (||) False s ) 
	       } 
	  MutVar z -> return (v == z) 
	  _ -> return False } 

unify_ tA tB = 
     do  t1 <- lift$ prune_ tA 
	 t2 <- lift$ prune_ tB 
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

varBind :: Omega m s r => Ptr s r -> GT s r -> m (ST r) ()
varBind r1 t2 = 
     do { b <- occurs r1 t2 
	; if b 
	    then throwError occursError
	    else lift$ write r1 (Just t2) } 

-- | match_ tA tB | trace ("match " ++ show tA ++ " and " ++ show tB) False = undefined
match_ tA tB = 
     do { t1 <- lift$ prune_ tA 
	; t2 <- lift$ prune_ tB 
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

instan_ sub x = 
      do { x' <- prune_ x 
	 ; case x' of 
	    GenVar n | n `atLeast` (subst sub) -> col $! (subst sub !! n) 
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
           let gvars = nub$ concat (toList (fmap (collect isGenVar) x'))
               mvars = nub$ concat (toList (fmap (collect isMutVar) x'))
               tot   = length gvars + length mvars
               new_gvars = map GenVar
                               ([0..tot]\\[j|GenVar j <- gvars])
           let x'' = fmap (replace (zip mvars new_gvars)) x'
           assert (all noMVars x'') (return ())
           return x''

generalizeGG_ x = do
           x' <- mapM2 col x
           let gvars = nub$ concat2 (toList2 (fmap2 (collect isGenVar) x'))
               mvars = nub$ concat2 (toList2 (fmap2 (collect isMutVar) x'))
               tot   = length gvars + length mvars
               new_gvars = map GenVar
                               ([0..tot]\\[j|GenVar j <- gvars])
           let x'' = fmap2 (replace (zip mvars new_gvars)) x'
           assert (all (and . fmap noMVars) x'') (return ())
           return x''

mapM2 f = mapM (mapM f)
concat2 = concat . concat
toList2 = map toList . toList

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
          maxGVar = maximum [ n | GenVar n <- gvars]


autoInstG_ xx = do
  freses <- Subst <$> replicateM topIndex fresh 
  xx' <- instan_ freses `mapM` xx
  return (freses, xx')
    where topIndex = maximum [ i | GenVar i <- concatMap vars xx]

autoInstGG_ xx = do
  freses <- Subst <$> replicateM topIndex fresh 
  xx' <- instan_ freses `mapM2` xx
  return (freses, xx')
    where topIndex = maximum [ i | GenVar i <- concatMap2 vars xx]
  
-----------------------
-- * Semantic Equality
-----------------------
instance TermShape s => Eq (GTE s r) where
--  a == b = resetVars (idGT a) `equal` resetVars(idGT b)
  (==) = equal_sem'

-- |Semantic equality (equivalence up to renaming of vars) 
equal_sem :: (TermShape s) => GT s r -> GT s r -> ST r Bool
equal_sem x@S{} y@S{} = fmap (either (return False) id) $ runErrorT $ do
    (theta_x, x') <- lift$ autoInst_ x
    (theta_y, y') <- lift$ autoInst_ y
    unify_ x' y'
    return (none isTerm theta_x && none isTerm theta_y)
  where none = (not.) . any

equal_sem x y = return$ synEq x y

-- | Out of the monad, fails for terms with mutvars
-- TODO Review in terms of staticTerm
equal_sem' :: (TermShape s) => GTE s r -> GTE s r -> Bool
equal_sem' s t = assert (noMVars s) $ assert (noMVars t) $ 
  let   s' = templateTerm $ zonkTerm s
        t' = templateTerm $ zonkTerm t
   in runST (equal_sem s' t')

instance TermShape s => Eq (Rule s) where
  (==) = equal_rule

-- | Semantic equivalence for rules 
equal_rule :: TermShape s => Rule s -> Rule s ->  Bool
equal_rule s1_ s2_ = runST$ do
   [l1:->r1,l2:->r2] <- mapM (mutableRule >=> generalizeG_) [s1_,s2_]
   return (l1 `synEq` l2 && r1 `synEq` r2)

instance TermShape s => Eq (TermStatic s) where
  t1 == t2 = runST$ do
   [t1',t2'] <- mapM (mutableTerm >=> generalize_) [t1,t2]
   return (t1' `synEq` t2')
   
-----------------------------------------------------
-----------------------------------------------------

--rewrite1_ rr (S t) | trace ("rewrite " ++ show t ++ " with " ++  (show$ length rr) ++ " rules ") False = undefined
--rewrite1_ _ t | assert (noMVars t) False = undefined
rewrite1_ rules (S t)
      | otherwise
      = rewriteTop (S t) `mplus` (fmap S$ someSubterm (rewrite1_ rules) t) 
        where rewriteTop t = msum$ forEach rules $ \r@(lhs:->rhs) -> do
	        (freshv, lhs') <- lift$ autoInst_ lhs
	        match_ lhs' t
                lift$ instan_ freshv rhs

rewrite1_ _ t = fail1 "no rewrite"

rewrite_ rules = fixM (rewrite1_ rules)

--narrow1_ _ t | trace ("narrow1 " ++ show t) False = undefined
narrow1_ [] _ = fail1 "narrow1: empty set of rules"
narrow1_ _ t | assert (noMVars t) False = undefined
narrow1_ rules t@S{} = go (t, emptyC)
    where go (t, ct) = 
              narrowTop rules ct t
             `mplus` 
              msum ( map (\(t, ct1) -> go (t, ct|>ct1) ) (contexts t))
narrow1_ rules _ = fail1 "narrow1: No Narrowing at vars"


narrowTop,narrowTopV :: OmegaPlus m s r => [RuleI s r] -> Context s r -> GT s r
                            -> m (ST r) (Subst s r, GT s r)
unsafeNarrowTop, unsafeNarrowTopV
    :: OmegaPlus m s r => [RuleI s r] -> Context s r -> GT s r
                            -> m (ST r) (Subst s r, GT s r)

narrowTop  rules ct t = assert (all noMVars [t,ct])$ unsafeNarrowTop rules ct t
narrowTopV rules ct t = assert (all noMVars [t,ct])$ unsafeNarrowTopV rules ct t
unsafeNarrowTop   = unsafeNarrowTopG narrowTop1
unsafeNarrowTopV  = unsafeNarrowTopG narrowTop1V


-- unsafeNarrowTopG _ _ _ t | trace ("unsafeNarrowTop " ++ show t) False = undefined
unsafeNarrowTopG narrowTop1 rules ct t = msum$ forEach rules $ \r -> do
               (vars, [t',ct']) <- lift$ autoInstG_ [t,ct]
               t''              <- narrowTop1 t' r
               return (vars, ct'|>t'')

narrowTop1, narrowTop1V :: Omega m s r => GT s r -> RuleI s r -> m (ST r) (GT s r)
narrowTop1V t r@(lhs:->rhs) = do
               assert (noGVars t) (return ())
               assert (noMVars lhs) (return ())
               assert (noMVars rhs) (return ())
               (lhsv, lhs') <- lift$ autoInst_ lhs
               unify_ lhs' t
--             trace ("narrowing fired: t=" ++ show t ++ ", rule=" ++ show r ++
--                     ", rho= " ++ show lhsv) (return ()) 
               rhs'  <- lift$ instan_ lhsv rhs
               rhs'' <- lift$ col rhs'      -- OPT: col here might be unnecesary
--             assert (noGVars rhs'') (return ())
               return rhs''
narrowTop1 t@S{} r = narrowTop1V t r
narrowTop1 _ _     = fail1 "No narrowing at vars"

-------------------------------
-- * The Full Narrowing Framework
-------------------------------
narrow1'_ = narrowFullG narrowTop'  (const (return True)) 
narrow1V_ = narrowFullG narrowTopV' (const (return True)) 

narrowFull_  = narrowFullG narrowTop' (const (return False))
narrowFullV_ = narrowFullG narrowTopV' (const (return False))
narrowFullBounded_  = narrowFullG narrowTop'
narrowFullBoundedV_ = narrowFullG narrowTopV'

narrowFullG :: (OmegaPlus m s r) =>
              ([RuleI s r] -> Context s r -> Subst s r -> GT s r
                          -> m (ST r) (Subst s r, GT s r)) 
            -> (GT s r -> ST r Bool)
            -> [RuleI s r] -> GT s r 
            -> m (ST r) (Subst s r, GT s r)

narrowFullG _ done [] t = -- trace ("narrowFull " ++ show t ++ " with empty TRS")$ 
                          lift (done t) >>= guard >> return (emptyS,t)
narrowFullG narrowTop1base done rules t = do 
     assert (noMVars t) (return ())
     (subst0,t0) <- lift$ autoInst_ t
     try search(subst0, t0)
  where 
          search (subst,t) = lift (done t) >>= guard . not >> 
                             step emptyC subst t >>= try search
          step cs subst t = -- trace ("narrowFull step: " ++ show t) $
                   (msum$ forEach (contexts t) $ \(ts,cs1) -> 
                       step (cs|>cs1) subst ts)
             `mplus`
                   narrowTop1base rules cs subst t 

narrowTop', narrowTopV'
    :: OmegaPlus m s r => [RuleI s r] -> Context s r -> Subst s r -> GT s r
                               -> m (ST r) (Subst s r, GT s r)

narrowTop'        = narrowTopG' narrowTop1
narrowTopV'       = narrowTopG' narrowTop1V

-- narrowTopG' _ _ _ _  t | trace ("NarrowTop' " ++ show t) False = undefined
narrowTopG' _ _ ct _ t | assert(all noGVars [ct,t]) False = undefined
narrowTopG' narrowTop1 rules ct subst t = msum$ forEach rules $ \r -> do
               (subst', [ct'], t') <- lift$ dupTermWithSubst subst [ct] t
               t'' <- narrowTop1 t' r
               return (subst', ct'|>t'')

--------------------------------------------------------------------------
-- * Out and back into the ST monad
--------------------------------------------------------------------------

mutableTerm :: (TermShape s, Functor s) => TermStatic s -> ST r (GT s r)
mutableTerm = autoInst_ . templateTerm >=> return . snd

mutableRule :: (TermShape s, Functor s) => Rule s -> ST r (RuleG (GT s r))
mutableRule = autoInstG_ . fmap templateTerm >=> return . snd

templateTerm :: Functor s =>  TermStatic s -> GT s r -- PEPE be careful with equality
templateTerm (Term x) = S(templateTerm <$> x)
templateTerm (Var n)  = GenVar n


zonkTerm :: (TermShape s) => GT_ eq s t -> TermStatic s
zonkTerm (MutVar r) = error "zonkTerm: No vars" 
zonkTerm (GenVar n) = Var n
zonkTerm (S y) = Term (fmap zonkTerm y)
zonkTerm (CtxVar n) = trace "dooyoo" $ Var n

zonkTermG :: (TermShape s, Functor s, Functor f) => f (GT_ eq s r) -> f (TermStatic s)
zonkTermG   = fmap zonkTerm

instTermG :: (TermShape s, Traversable f, Functor s) => 
            f (TermStatic s) -> ST r (f (GT s r))
instTermG = fmap snd . autoInstG_ . fmap templateTerm

--------------------------------
-- * Duplication of Terms
--------------------------------
dupVar sr = readSTRef sr >>= newSTRef
dupTerm (MutVar r) = fmap MutVar (dupVar r)
dupTerm (S t) = fmap S $ mapM dupTerm t
dupTerm x = return x

--dupTermWithSubst subst tt x | trace "dupTermWithSubst" False = undefined
dupTermWithSubst :: (Eq (GT s r), TermShape s) => 
                    Subst s r -> [GT s r] -> GT s r 
                 -> ST r (Subst s r, [GT s r], GT s r)
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
run :: (TermShape s, Show (s (GTE s r))) => (forall r.ST r (GTE s r)) -> TermStatic s
run c = runST (fmap zonkTerm c)

runG :: (TermShape s, Show (s (GTE s r)), Functor f) =>
         (forall r.ST r (f(GTE s r))) -> f(TermStatic s)
runG c = runST ( (fmap2 zonkTerm c))

runGG :: (TermShape s, Show (s (GTE s r)), Functor f, Functor f1) =>
         (forall r.ST r (f(f1(GTE s r)))) -> f(f1(TermStatic s))
runGG c = runST ( (fmap3 zonkTerm c))

runIO :: ST RealWorld a -> IO a
runIO = stToIO


runE :: (Omega (ErrorT (TRSException)) s r) => 
        (forall r. ErrorT (TRSException) (ST r) (GTE s r)) -> (TermStatic s)
runE c = runST (fmap (either (error.show) id) 
                              (runErrorT (fmap zonkTerm c)))

runEG :: (Omega (ErrorT (TRSException)) s r, Functor f) =>
         (forall r. ErrorT (TRSException) (ST r) (f(GTE s r))) -> f(TermStatic s)
runEG c = runST (fmap (either (error.show) id) 
                                    (runErrorT (fmap2 zonkTerm c)))

runEGG :: (Omega (ErrorT (TRSException)) s r, Functor f, Functor f1) =>
         (forall r. ErrorT (TRSException) (ST r) (f(f1(GTE s r)))) -> f(f1(TermStatic s))
runEGG c = runST (fmap (either (error.show) id) 
                                      (runErrorT (fmap3 zonkTerm c)))

runEIO :: ErrorT (TRSException) (ST RealWorld) a -> IO a
runEIO = fmap (either (error. show) id) . stToIO . runErrorT



runM :: (Omega (ErrorT (TRSException)) s r) => 
        (forall r. ErrorT (TRSException) (ST r) (GTE s r)) -> Maybe (TermStatic s)
runM c = runST (fmap (either (const Nothing) Just)
                              (runErrorT (fmap zonkTerm c)))

runMG :: (Omega (ErrorT (TRSException)) s r, Functor f) =>
         (forall r. ErrorT (TRSException) (ST r) (f(GTE s r))) -> Maybe (f(TermStatic s))
runMG c = runST (fmap (either (const Nothing) Just) 
                                    (runErrorT (fmap2 zonkTerm c)))

runMGG :: (Omega (ErrorT (TRSException)) s r, Functor f, Functor f1) =>
         (forall r. ErrorT (TRSException) (ST r) (f(f1(GTE s r)))) -> Maybe (f(f1(TermStatic s)))
runMGG c = runST (fmap (either (const Nothing) Just) 
                                      (runErrorT (fmap3 zonkTerm c)))

runMIO :: ErrorT (TRSException) (ST RealWorld) a -> IO (Maybe a)
runMIO = fmap (either (const Nothing) Just) . stToIO . runErrorT



runL :: Omega (ListT') s r => (forall r. ListT' (ST r) (GTE s r)) -> [TermStatic s]
runL c = runST (runListT' (fmap zonkTerm c))

runLG :: (Omega (ListT') s r, Functor f) =>
         (forall r. ListT' (ST r) (f(GTE s r))) -> [f(TermStatic s)]
runLG c = runST (runListT' (fmap2 zonkTerm c))

runLGG :: (Omega (ListT') s r, Functor f, Functor f1) =>
         (forall r. ListT' (ST r) (f(f1(GTE s r)))) -> [f(f1(TermStatic s))]
runLGG c = runST (runListT' (fmap3 zonkTerm c))

runLIO :: ListT' (ST RealWorld) a -> IO [a]
runLIO = stToIO . runListT'

----------------
-- Other stuff
----------------
someSubterm :: (Traversable t, MonadPlus m) => (a -> m a) -> t a -> m (t a)
someSubterm f x = msum$ interleave f return x

isConst :: Foldable t => t a -> Bool
isConst = null . toList

instance Show (GT_ eq s r) => Observable (GT_ eq s r) where
    observer = observeBase


{-# INLINE fail1 #-}
fail1 :: Monad m => String -> m a 
--fail1 msg = trace msg $ fail msg
fail1 = fail

-- TODOs:
-- - Float pruning to the type

