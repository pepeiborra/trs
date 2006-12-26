{-# OPTIONS_GHC -fglasgow-exts -fallow-undecidable-instances #-}
{-# OPTIONS_GHC -fallow-overlapping-instances #-}
{-# OPTIONS_GHC -fno-monomorphism-restriction #-}
{-# OPTIONS_GHC -fdebugging #-}

-----------------------------------------------------------------------------------------
{-| Module      : TRS.Core
    Copyright   : 
    License     : All Rights Reserved

    Maintainer  : Pepe Iborra
    Stability   : 
    Portability : 
-}
----------------------------------------------------------------------------------------


module TRS.Core where

import Control.Applicative
import Control.Arrow ( first, second, (>>>))
import Control.Monad hiding (msum, mapM_, mapM, sequence, forM)
import Control.Monad.Error (MonadError(..), ErrorT(..), MonadTrans(..))
import Control.Monad.State (StateT(..), MonadState(..), gets, modify, lift)
import Control.Monad.Fix (MonadFix(..))
import Data.List ((\\), nub, elemIndex)
import Data.Traversable
import Data.Foldable
import Data.Maybe 
import Data.Monoid
import Prelude hiding ( all, maximum, minimum, any, mapM_,mapM, foldr, foldl
                      , and, concat, concatMap, sequence, elem, notElem)
import TRS.Types
import TRS.Terms
import TRS.Context
import TRS.Utils
import Control.Exception (assert)
import Test.QuickCheck (Arbitrary(..))

import GHC.Exts (unsafeCoerce#)
import Observe
import qualified Debug.Trace

instance RWTerm s => Eq (GT s r) where
  (==) = equal   -- syntactic equality

{-# SPECIALIZE prune_ :: GT TermST r -> ST r (GT TermST r) #-}
{-# SPECIALIZE equal :: GT TermST r  -> GT TermST r  -> Bool #-}


---------------------------
-- External Interface
---------------------------
-- This is the intended user API for this module
-- Below we expose versions of the functions we have defined before
--  which take have GTE types in signatures instead of GT. 

--liftGTE2 :: (GT s r -> GT s r -> a) -> GTE s r -> GTE s r -> a
liftGTE2 f x y =  f (idGT x) (idGT y)
--liftGTE :: Functor f => (GT s r -> f(GT s r)) -> GTE s r -> f(GTE s r)
liftGTE f = fmap eqGT . f . idGT
--fixRules :: [Rule s r] -> [RuleI s r]
fixRules = fmap2 idGT
adaptSubstitutionResult f rre t = fmap (second eqGT) $ f (fixRules rre) (idGT t)

prune	  :: GTE s r -> ST r (GTE s r)
prune = liftGTE prune_

unify	  :: Omega m s r => GTE s r -> GTE s r -> m (ST r) ()
unify = liftGTE2 unify_

match	  :: Omega m s r => GTE s r -> GTE s r -> m (ST r) ()
match = liftGTE2 match_

instan	  :: RWTerm s => Subst s r -> GTE s r -> ST r (GTE s r)
instan s = liftGTE (instan_ s)

rewrite1  :: OmegaPlus m s r => [Rule s r] -> GTE s r -> m (ST r) (GTE s r)
rewrite1 rre = liftGTE (rewrite1_ (fixRules rre))

rewrite   :: OmegaPlus m s r => [Rule s r] -> GTE s r -> m (ST r) (GTE s r)
rewrite  rre = liftGTE (rewrite_ (fixRules rre))

narrow1   :: OmegaPlus m s r => [Rule s r] -> GTE s r -> 
             m (ST r) (Subst s r, GTE s r)
narrow1 = adaptSubstitutionResult narrow1_

narrow1',narrow1V 
          :: (OmegaPlus m s r) => [Rule s r] -> GTE s r -> 
             m (ST r) (Subst s r, GTE s r)
narrow1' = adaptSubstitutionResult narrow1'_
narrow1V = adaptSubstitutionResult narrow1V_

narrowFull:: (OmegaPlus m s r) => [Rule s r] -> GTE s r -> 
             m (ST r) (Subst s r, GTE s r)
narrowFull = adaptSubstitutionResult narrowFull_

narrowFullV:: (OmegaPlus m s r) =>
              [Rule s r] -> GTE s r -> m (ST r) (Subst s r, GTE s r)
narrowFullV = adaptSubstitutionResult narrowFullV_
narrowFullBounded  :: (OmegaPlus m s r) =>
                      (GTE s r -> ST r Bool) -> [Rule s r] -> GTE s r -> 
                      m (ST r) (Subst s r, GTE s r)
narrowFullBounded pred = adaptSubstitutionResult (narrowFullBounded_ (pred . eqGT))
narrowFullBoundedV :: (OmegaPlus m s r) =>
                      (GTE s r -> ST r Bool) -> [Rule s r] -> GTE s r -> 
                      m (ST r) (Subst s r, GTE s r)
narrowFullBoundedV pred = adaptSubstitutionResult (narrowFullBoundedV_ (pred . eqGT))

generalize :: RWTerm s => GTE s r -> ST r (GTE s r)
generalize = liftGTE generalize_

generalizeG::(RWTerm s, Traversable f) => f(GTE s r) -> ST r (f(GTE s r))
generalizeG = fmap2 eqGT . generalizeG_  . fmap idGT

generalizeGG = fmap3 eqGT . generalizeGG_ . fmap2 idGT

autoInst  :: RWTerm s => GTE s r -> ST r (Subst s r, GTE s r)       
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

-- Unbounded Full Narrowing
narrowFull_ :: (OmegaPlus m s r) => [RuleI s r] -> GT s r -> 
             m (ST r) (Subst s r, GT s r)

-- Unbounded Full Paramodulation
narrowFullV_ :: (OmegaPlus m s r) =>
              [RuleI s r] -> GT s r -> m (ST r) (Subst s r, GT s r)

-- Bounded versions. The first argument is the bound checking predicate
narrowFullBounded_ :: (OmegaPlus m s r) =>
                      (GT s r -> ST r Bool) -> [RuleI s r] -> GT s r -> 
                      m (ST r) (Subst s r, GT s r)
narrowFullBoundedV_:: (OmegaPlus m s r) =>
                      (GT s r -> ST r Bool) -> [RuleI s r] -> GT s r -> 
                      m (ST r) (Subst s r, GT s r)

generalize_ ::RWTerm s => GT s r -> ST r (GT s r)
generalizeG_::(RWTerm s,Traversable f) => f(GT s r) -> ST r (f(GT s r))
generalizeGG_::(RWTerm s, Traversable f, Traversable f') => 
               f'(f(GT s r)) -> ST r (f'(f(GT s r)))

-- |Returns the instantiated term together with the new MutVars 
--  (you need these to apply substitutions) 
autoInst_ :: RWTerm s => GT s r -> ST r (Subst s r, GT s r)       
autoInstG_:: (Traversable s, Traversable f) =>  f(GT s r) -> ST r (Subst s r, f(GT s r))


-- * Basic primitives
unify_	  :: Omega m s r => GT s r -> GT s r -> m (ST r) ()
match_	  :: Omega m s r => GT s r -> GT s r -> m (ST r) ()

-- | Syntactic equality
equal	  :: RWTerm s    => GT s r -> GT s r -> Bool

-- ** Dereference variables
prune_	  :: GT_ eq s r  -> ST r (GT_ eq s r)
col 	  :: Traversable s => GT_ eq s r  -> ST r (GT_ eq s r)    
instan_	  :: Traversable s => Subst_ eq s r-> GT_ eq s r -> ST r (GT_ eq s r)

resetVars :: (Eq (GT_ eq s r), Traversable s) => GT_ eq s r -> GT_ eq s r
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

-- match_ tA tB | trace ("match " ++ show tA ++ " and " ++ show tB) False = undefined
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
equal x y = go x y
  where 
    go x y = 
      case (x,y) of 
	(MutVar r1,MutVar r2) -> 
	  r1 == r2 
	(GenVar n,GenVar m) -> m==n
	(CtxVar n,CtxVar m) -> m==n
        (S x, S y) -> 
	    case matchTerm x y of 
	      Nothing -> False 
	      Just pairs -> all (uncurry go) pairs 
        other -> False

collect   :: Foldable s  => (GTE s r -> Bool) -> GTE s r -> [GTE s r]
collect pred = liftGTE (collect_ (pred . eqGT) )

{- Good performance of equality is fundamental. But everytime it's called
   a resetVars is done (see the Eq instance for GTE), which is expensive

   Let's distinguish between syntactic and semantic equivalence. 
   Function 'equal' above tests for syntactic. When paired with resetVars below
   we are testing for semantic. Syntactic is much faster, semantic is correct. 
   For instance, in dupTermWithSubst I only need to test for 
   syntactic, as in most places inside this module! 
   Thus the reasoning is as follows. Inside this module I want to use syntactic
   equivalence. Why? Because it's way faster, and I don't need the extra 
   generality. But for the client, I want to expose the always correct 
   semantic version of equality instance.
-}
-- This is a kludge. Used to simulate 'equivalence up to renaming'
-- In theory this 'canonicalizes' the vars of a term
resetVars x = reset x
    where reset g@GenVar{} = new_vars !! fromMaybe undefined (elemIndex g vars_x)
          reset m@MutVar{} = new_vars !! fromMaybe undefined (elemIndex m vars_x)
          reset (S t)      = S$ fmap reset t 
          reset x  = x
          vars_x   = vars x
          new_vars = map GenVar [0..]

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
           let gvars = collect_ isGenVar x'
               mvars = collect_ isMutVar x'
               tot   = length gvars + length mvars
               new_gvars = map GenVar
                               ([0..tot]\\[j|GenVar j <- gvars])
           let x'' = (replaceAll (zip mvars new_gvars)) x'
           assert (noMVars x'') (return ())
           return x''

generalizeG_ x = do
           x' <- mapM col x
           let gvars = nub$ concat (toList (fmap (collect_ isGenVar) x'))
               mvars = nub$ concat (toList (fmap (collect_ isMutVar) x'))
               tot   = length gvars + length mvars
               new_gvars = map GenVar
                               ([0..tot]\\[j|GenVar j <- gvars])
           let x'' = fmap (replaceAll (zip mvars new_gvars)) x'
           assert (all noMVars x'') (return ())
           return x''

generalizeGG_ x = do
           x' <- mapM2 col x
           let gvars = nub$ concat2 (toList2 (fmap2 (collect_ isGenVar) x'))
               mvars = nub$ concat2 (toList2 (fmap2 (collect_ isMutVar) x'))
               tot   = length gvars + length mvars
               new_gvars = map GenVar
                               ([0..tot]\\[j|GenVar j <- gvars])
           let x'' = fmap2 (replaceAll (zip mvars new_gvars)) x'
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
           freshv <- fmap (Subst . reverse) $ 
                    foldM (\rest gv -> liftM (:rest) $
                            if gv`elem`gvars then fresh else return gv) 
                          []
                          (map GenVar [0..maxGVar+1])
           x' <- instan_ freshv x
           assert (noGVars x') (return ())
           x' `seq` return (freshv, x')
    where gvars = collect_ isGenVar x
          maxGVar = maximum [ n | GenVar n <- gvars]
          upd list i v | (h, (_:t)) <- splitAt i list = h ++ v:t
          updM list i c = c >>= return . upd list i

run_autoInstG_ autoInst1 = fmap swap . flip runStateT emptyS . autoInst1 
  where swap (a,b) = (b,a)

autoInstG_ = run_autoInstG_ (mapM autoInst1)
autoInstGG_= run_autoInstG_ (mapM2 autoInst1)

autoInst1 x = do
           freshv <- createFreshs x
           lift$ instan_ freshv x
    where createFreshs t | null vars_t = get 
                         | otherwise   = do
             freshv <- gets subst
             unless (topIndex `atLeast` freshv) $ do
                extra_freshv <- replicateM (topIndex - length freshv + 1) 
                                           (lift fresh)
                put (Subst$ freshv ++ extra_freshv)
             get
               where
                  vars_t = vars t
                  topIndex = maximum [ i | GenVar i <- vars_t ]

-----------------------
-- * Semantic Equality
-----------------------
instance RWTerm s => Eq (GTE s r) where
--  a == b = resetVars (idGT a) `equal` resetVars(idGT b)
  (==) = equal_sem'

-- |Semantic equality (equivalence up to renaming of vars) 
equal_sem :: (RWTerm s) => GT s r -> GT s r -> ST r Bool
equal_sem x@S{} y@S{} = fmap (either (return False) id) $ runErrorT $ do
    (theta_x, x') <- lift$ autoInst_ x
    (theta_y, y') <- lift$ autoInst_ y
    unify_ x' y'
    return (none isTerm theta_x && none isTerm theta_y)
  where none = (not.) . any

equal_sem x y = return$ equal x y

-- | Out of the monad, fails for terms with mutvars
equal_sem' :: (RWTerm s) => GTE s r -> GTE s r -> Bool
equal_sem' s t = assert (noMVars s) $ assert (noMVars t) $ 
  let   s' = fromFix $ toFix s
        t' = fromFix $ toFix t
   in runST (equal_sem s' t')

instance RWTerm s => Eq (Rule s r) where
  (==) = equal_rule'

-- | Semantic equivalence for rules (no mvars restriction)
equal_rule' :: RWTerm s => Rule s r -> Rule s r ->  Bool
equal_rule' s1 s2 = runST (equal_rule s1' s2')
      where s1' = fromFixG (toFixG (fmap idGT s1))
            s2' = fromFixG (toFixG (fmap idGT s2))

-- | Semantic equivalence for rules
equal_rule :: RWTerm s => Rule s r -> Rule s r -> ST r Bool
equal_rule s1 s2 = fmap(either (return False) id) $ runErrorT$ do
   (theta1, l1:->r1) <- lift$ autoInstG_ (fmap idGT s1)
   (theta2, l2:->r2) <- lift$ autoInstG_ (fmap idGT s2)
   unify_ l1 l2 >> unify_ r1 r2
   lift$ isARenaming (subst theta1) &>& allM isEmptyVar (subst theta2)
   where (&>&) = liftM2 (&&)
         isARenaming = allM (\(MutVar m) -> readVar m >>= 
                       return . maybe True (not . isTerm))

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
-- * Out and back into the ST monad with recursive Fixpoint datastructures
--------------------------------------------------------------------------

fromFix :: (Functor s) => Fix s -> (forall r. GT_ eq s r)
fromFix (Fix x) = S(fmap fromFix x)
fromFix (Var n) = GenVar n

toFix :: (RWTerm s) => GT_ eq s t -> Fix s
toFix (MutVar r) = error "toFix: No vars" 
toFix (GenVar n) = Var n
toFix (S y) = Fix (fmap toFix y)

toFixG :: (RWTerm s, Functor s, Functor f) => f (GT_ eq s r) -> f (Fix s)
toFixG   = fmap toFix

fromFixG :: (Functor f, Functor s) => f (Fix s) -> f (GT_ eq s r)
fromFixG = fmap fromFix

--------------------------------
-- * Duplication of Terms
--------------------------------
dupVar sr = readSTRef sr >>= newSTRef
dupTerm (MutVar r) = fmap MutVar (dupVar r)
dupTerm (S t) = fmap S $ mapM dupTerm t
dupTerm x = return x

--dupTermWithSubst subst tt x | trace "dupTermWithSubst" False = undefined
dupTermWithSubst :: (Eq (GT s r), RWTerm s) => 
                    Subst s r -> [GT s r] -> GT s r 
                 -> ST r (Subst s r, [GT s r], GT s r)
dupTermWithSubst subst tt t@MutVar{} = do
    t'        <- dupTerm t
    let dict   = [(t,t')]
        subst' = liftSubst (fmap (replaceAll dict)) subst
        tt'    = fmap (replaceAll dict) tt
    return (subst', tt', t')

dupTermWithSubst subst tt t@S{} = do
    let mutvars= collect_ isMutVar t
    newvars   <- mapM dupTerm mutvars
    let dict   = zip mutvars newvars
        t'     = replaceAll dict t
        tt'    = fmap (replaceAll dict) tt
        subst' = liftSubst (fmap(replaceAll dict)) subst
    return (subst', tt', t')

dupTermWithSubst subst tt x = return (subst, tt, x)

-- syntactic equality is primordial here
replaceAll :: (Eq (GT s r), RWTerm s) => 
              [(GT s r, GT s r)] -> GT s r -> GT s r
replaceAll dict x = fromJust$ replaceAll' dict x
   where replaceAll' dict (S t) = lookup (S t) dict `mplus` 
                                  fmap S (mapM (replaceAll' dict) t) 
         replaceAll' dict x = lookup x dict `mplus` return x

------------------------------
-- * Obtaining the results
------------------------------
run :: (RWTerm s, Show (s (GTE s r))) => (forall r.ST r (GTE s r)) -> GTE s r
run c = fromFix (runST (fmap toFix c))

runG :: (RWTerm s, Show (s (GTE s r)), Functor f) =>
         (forall r.ST r (f(GTE s r))) -> f(GTE s r)
runG c = (fmap fromFix) (runST ( (fmap2 toFix c)))

runGG :: (RWTerm s, Show (s (GTE s r)), Functor f, Functor f1) =>
         (forall r.ST r (f(f1(GTE s r)))) -> f(f1(GTE s r))
runGG c = (fmap2 fromFix) (runST ( (fmap3 toFix c)))

runIO :: ST RealWorld a -> IO a
runIO = stToIO


runE :: (Omega (ErrorT (TRSException)) s r) => 
        (forall r. ErrorT (TRSException) (ST r) (GTE s r)) -> (GTE s r)
runE c = fromFix (runST (fmap (either (error.show) id) 
                              (runErrorT (fmap toFix c))))

runEG :: (Omega (ErrorT (TRSException)) s r, Functor f) =>
         (forall r. ErrorT (TRSException) (ST r) (f(GTE s r))) -> f(GTE s r)
runEG c = fmap fromFix (runST (fmap (either (error.show) id) 
                                    (runErrorT (fmap2 toFix c))))

runEGG :: (Omega (ErrorT (TRSException)) s r, Functor f, Functor f1) =>
         (forall r. ErrorT (TRSException) (ST r) (f(f1(GTE s r)))) -> f(f1(GTE s r))
runEGG c = fmap2 fromFix (runST (fmap (either (error.show) id) 
                                      (runErrorT (fmap3 toFix c))))

runEIO :: ErrorT (TRSException) (ST RealWorld) a -> IO a
runEIO = fmap (either (error. show) id) . stToIO . runErrorT



runL :: Omega (ListT') s r => (forall r. ListT' (ST r) (GTE s r)) -> [GTE s r]
runL c = map fromFix (runST (runListT' (fmap toFix c)))

runLG :: (Omega (ListT') s r, Functor f) =>
         (forall r. ListT' (ST r) (f(GTE s r))) -> [f(GTE s r)]
runLG c = map (fmap fromFix) (runST (runListT' (fmap2 toFix c)))

runLGG :: (Omega (ListT') s r, Functor f, Functor f1) =>
         (forall r. ListT' (ST r) (f(f1(GTE s r)))) -> [f(f1(GTE s r))]
runLGG c = map (fmap2 fromFix) (runST (runListT' (fmap3 toFix c)))

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

