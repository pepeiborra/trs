{-# OPTIONS_GHC -fglasgow-exts -fallow-undecidable-instances -fallow-overlapping-instances -fallow-incoherent-instances #-}

-----------------------------------------------------------------------------------------
{-| Module      : TRS.Core
    Copyright   : 
    License     : All Rights Reserved

    Maintainer  : 
    Stability   : 
    Portability : 
-}
----------------------------------------------------------------------------------------

module TRS.Core where

import Control.Applicative
import Control.Arrow ( first, second )
import Control.Monad hiding (msum, mapM_, mapM, sequence, forM)
import Control.Monad.List (runListT, ListT(..),lift)
import Control.Monad.Identity (runIdentity)
import Control.Monad.Error (ErrorT(..), MonadTrans(..))
import Control.Monad.State (StateT(..), gets, modify)
import Data.List ((\\), nub, elemIndex)
import Data.Traversable
import Data.Foldable
import Data.Maybe (fromJust)
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

instance RWTerm s => Eq (GT s r) where
  (==) = equal

{-# SPECIALIZE prune_ :: Omega m TermST r => GT TermST r -> m (ST r) (GT TermST r) #-}
{-# SPECIALIZE equal :: GT TermST r  -> GT TermST r  -> Bool #-}


prune_	  :: Omega m s r => GT s r  -> GTm m s r

unify_	  :: Omega m s r => GT s r -> GT s r -> m (ST r) ()
match_	  :: Omega m s r => GT s r -> GT s r -> m (ST r) ()
equal	  :: RWTerm s    => GT s r -> GT s r -> Bool
resetVars :: RWTerm s    => GT s r -> GT s r
occurs	  :: Omega m s r => Ptr s r -> GT s r -> m (ST r) Bool
-- |Dereference variables
--col 	  :: Omega m s r => GT s r  -> GTm m s r    
instan_	  :: Omega m s r => Subst s r-> GT s r -> GTm m s r
-- |leftmost outermost
rewrite1_ :: OmegaPlus m s r => [RuleI s r] -> GT s r -> m (ST r) (GT s r)
rewrite_  :: OmegaPlus m s r => [RuleI s r] -> GT s r -> m (ST r) (GT s r)
narrow1_  :: OmegaPlus m s r => [RuleI s r] -> GT s r -> 
             m (ST r) (Subst s r, GT s r)
narrow1'_, narrow1V_
          :: (OmegaPlus m s r, MonadTry (m(ST r))) => [RuleI s r] -> GT s r -> 
             m (ST r) (Subst s r, GT s r)

-- Unbounded Full Narrowing

narrowFull_ :: (OmegaPlus m s r, MonadTry (m (ST r))) => [RuleI s r] -> GT s r -> 
             m (ST r) (Subst s r, GT s r)
-- Unbounded Full Narrowing, with narrowing on variables

narrowFullV_ :: (OmegaPlus m s r, MonadTry (m (ST r))) =>
              [RuleI s r] -> GT s r -> m (ST r) (Subst s r, GT s r)
narrowFullBounded_ :: (OmegaPlus m s r, MonadTry (m (ST r))) =>
                      (GT s r -> ST r Bool) -> [RuleI s r] -> GT s r -> 
                      m (ST r) (Subst s r, GT s r)
narrowFullBoundedV_:: (OmegaPlus m s r, MonadTry (m (ST r))) =>
                      (GT s r -> ST r Bool) -> [RuleI s r] -> GT s r -> 
                      m (ST r) (Subst s r, GT s r)

--generalize_ ::Omega m s r => GT s r -> GTm m s r
---generalizeG_::(Traversable f, Omega m s r) => f(GT s r) -> m (ST r) (f(GT s r))
-- |Returns the instantiated term together with the new MutVars 
--  (you need these to apply substitutions) 
autoInst_  :: Omega m s r => GT s r -> m (ST r) (Subst s r, GT s r)       
fresh	  :: Omega m s r => GTm m s r
readVar   :: MonadTrans t=> STRef s a -> t (ST s) a
write     :: MonadTrans t=> STRef s a -> a -> t (ST s) ()

fresh = lift (newSTRef Nothing) >>= return . MutVar
readVar r = lift$ readSTRef r
write r x = lift$ writeSTRef r x
--    collect_ :: (GT s r -> Bool) -> GT s r -> [GT s r]

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
     do { t2 <- prune_ t 
	; case t2 of 
	  S w -> 
	    do { s <- (mapM (occurs v) w) 
	       ; return(foldr (||) False s ) 
	       } 
	  MutVar z -> return (v == z) 
	  _ -> return False } 
unify_ tA tB = 
     do  t1 <- prune_ tA 
	 t2 <- prune_ tB 
	 case (t1,t2) of 
	   (MutVar r1,MutVar r2) -> 
	     if r1 == r2 
		then return () 
		else write r1 (Just t2) 
	   (MutVar r1,_) -> varBind r1 t2 
	   (_,MutVar r2) -> varBind r2 t1 
	   (GenVar n,GenVar m) -> 
	    if n==m 
		then return () 
		else fail1 "Gen error" 
	   (S x,S y) -> 
	     case matchTerm x y of
		Nothing -> fail1 ("ShapeErr in unify_(" ++ show tA ++ ',' : show tB ++ ")")
		Just pairs -> 
		  mapM_ (uncurry unify_) pairs 
	   (x,y) -> fail1$ "ShapeErr Unifying " ++show x ++ " and " ++ show y 

-- match_ tA tB | trace ("match " ++ show tA ++ " and " ++ show tB) False = undefined
match_ tA tB = 
     do { t1 <- prune_ tA 
	; t2 <- prune_ tB 
	; case (t1,t2) of 
	  (MutVar r1,_) -> 
	    write r1 (Just t2) 
	  (GenVar n,GenVar m) -> 
	    if n==m 
		then return () 
		else fail1 "Gen error" 
	  (S x,S y) -> 
	    case matchTerm x y of 
		Nothing -> fail1 "ShapeErr" 
		Just pairs -> 
		  mapM_ (uncurry match_) pairs 
	  (_,_) -> fail1 "ShapeErr?" 
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
           
resetVars x = reset x
    where reset (GenVar n) = new_gvars !! fromJust(elemIndex n gvars)
          reset (MutVar r) = new_mvars !! fromJust(elemIndex r mvars)
          reset (S t)      = S$ fmap reset t 
          reset x = x
          gvars = [n | GenVar n <- collect_ isGenVar x]
          mvars = [r | MutVar r <- collect_ isMutVar x]
          new_gvars = map GenVar [0..]
          new_mvars = map GenVar [length gvars..]

{- Good performance of equality is fundamental. But everytime it's called
   a resetVars is done. One would wish to cache the result of a previous
   call to resetVars. Maybe steal some ideas about caching from the 
   Finger Trees paper!

   Another DANGEROUS thing is confusing identity with eq-uivalence. Equals 
   tests for the second, but in haskell the Eq type class is commonly identified
   with the first. For instance, in dupTermWithSubst I want to test for 
   identity, as in most places inside this module! 
   Thus the reasoning is as follows. In this module I want to use identity. But for
   the client, I want to expose the instance that provides equivalence.
-}

instan_ sub x = 
      do { x' <- prune_ x 
	 ; case x' of 
	    GenVar n | n < length (subst sub) -> col $! (subst sub !! n) 
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
              
autoInstG xx | null gvars = return (emptyS, xx)
             | otherwise  = do
           freshv <- liftM Subst $ replicateM ((maximum$ [i|GenVar i <-gvars]) + 1) 
                                              fresh
           xx' <- mapM (instan_ freshv) xx
           assert (all noGVars xx') (return ())
           return (freshv, xx')
    where gvars = concatMap (collect_ isGenVar) xx

    -- The intent is to do one rewrite step only
    -- But.. for some MonadPlus's, you might get different results
--rewrite1_ rr (S t) | trace ("rewrite " ++ show t ++ " with " ++  (show$ length rr) ++ " rules ") False = undefined
--rewrite1_ _ t | assert (noMVars t) False = undefined
rewrite1_ rules (S t)
--      | isConst t = rewriteTop rules (S t)
      | otherwise
      = rewriteTop (S t) `mplus` (fmap S$ someSubterm (rewrite1_ rules) t) 
        where rewriteTop t = msum$ forEach rules $ \r@(lhs:->rhs) -> do
	        (freshv, lhs') <- autoInst_ lhs
	        match_ lhs' t
--	        trace ("rule fired: " ++ show r ++ " for " ++ show t) (return 0)
                instan_ freshv rhs

rewrite1_ _ t = fail1 "no rewrite"

rewrite_ rules = fixM (rewrite1_ rules)

narrow1_ _ t | trace ("narrow1 " ++ show t) False = undefined
narrow1_ [] _ = fail1 "narrow1: empty set of rules"
narrow1_ _ t | assert (noMVars t) False = undefined
narrow1_ rules t@S{} = narrow1' (t, emptyC)
    where narrow1' (t, ct) = 
              narrowTop rules ct t
             `mplus` 
              msum ( map (\(t, ct1) -> narrow1' (t, ct|>ct1) ) (contexts t))
narrow1_ rules _ = fail1 "narrow1: No Narrowing at vars"
-------------------------------
-- The New Narrowing Framework
-------------------------------
narrow1'_ = narrowFullG narrowTop'  (const (return True)) 
narrow1V_ = narrowFullG narrowTopV' (const (return True)) 

narrowFull_  = narrowFullG narrowTop' (const (return False))
narrowFullV_ = narrowFullG narrowTopV' (const (return False))
narrowFullBounded_  = narrowFullG narrowTop'
narrowFullBoundedV_ = narrowFullG narrowTopV'

narrowFullG :: (OmegaPlus m s r, MonadTry (m (ST r))) =>
              ([RuleI s r] -> Context s r -> Subst s r -> GT s r
                          -> m (ST r) (Subst s r, GT s r)) 
            -> (GT s r -> ST r Bool)
            -> [RuleI s r] -> GT s r 
            -> m (ST r) (Subst s r, GT s r)

narrowFullG _ done [] t = trace ("narrowFull " ++ show t ++ " with empty TRS")$ 
                          lift (done t) >>= guard >> return (emptyS,t)
narrowFullG narrowTop1base done rules t = do 
     assert (noMVars t) (return ())
     (subst0,t0) <- autoInst_ t
     try search(subst0, t0)
  where 
          search (subst,t) = lift (done t) >>= guard . not >> 
                             step emptyC subst t >>= try search
          step cs subst t = trace ("narrowFull step: " ++ show t) $
                   (msum$ forEach (contexts t) $ \(ts,cs1) -> 
                       step (cs|>cs1) subst ts)
             `mplus`
                   narrowTop rules cs subst t 
          narrowTop = narrowTop1base

narrowTop,narrowTopV :: OmegaPlus m s r => [RuleI s r] -> Context s r -> GT s r
                            -> m (ST r) (Subst s r, GT s r)
unsafeNarrowTop, unsafeNarrowTopV
    :: OmegaPlus m s r => [RuleI s r] -> Context s r -> GT s r
                               -> m (ST r) (Subst s r, GT s r)
narrowTop', narrowTopV'
    :: OmegaPlus m s r => [RuleI s r] -> Context s r -> Subst s r -> GT s r
                               -> m (ST r) (Subst s r, GT s r)

narrowTop rules ct t  = assert (all noMVars [t,ct])$ unsafeNarrowTop rules ct t
narrowTopV rules ct t = assert (all noMVars [t,ct])$ unsafeNarrowTopV rules ct t
unsafeNarrowTop   = unsafeNarrowTopG narrowTop1
unsafeNarrowTopV  = unsafeNarrowTopG narrowTop1V
narrowTop'  = narrowTopG' narrowTop1
narrowTopV' = narrowTopG' narrowTop1V

-- unsafeNarrowTopG _ _ _ t | trace ("unsafeNarrowTop " ++ show t) False = undefined
unsafeNarrowTopG narrowTop1 rules ct t = msum$ forEach rules $ \r -> do
               (vars, [t',ct']) <- autoInstG [t,ct]
               t''              <- narrowTop1 t' r
               return (vars, ct'|>t'')

narrowTopG' _ _ _ _  t | trace ("NarrowTop' " ++ show t) False = undefined
narrowTopG' _ _ ct _ t | assert(all noGVars [ct,t]) False = undefined
narrowTopG' narrowTop1 rules ct subst t = msum$ forEach rules $ \r -> do
               (subst', [ct'], t') <- lift$ dupTermWithSubst subst [ct] t
               t'' <- narrowTop1 t' r
               return (subst', ct'|>t'')

narrowTop1, narrowTop1V :: Omega m s r => GT s r -> RuleI s r 
                          -> m (ST r) (GT s r)
narrowTop1V t r@(lhs:->rhs) = do
               assert (noGVars t) (return ())
               assert (noMVars lhs) (return ())
               assert (noMVars rhs) (return ())
               (lhsv, lhs') <- autoInst_ lhs
               unify_ lhs' t
               trace ("narrowing fired: t=" ++ show t ++ ", rule=" ++ show r ++
                     ", rho= " ++ show lhsv) (return ()) 
               rhs' <- instan_ lhsv rhs
               rhs'' <- col rhs'         -- OPT: col here might be unnecesary
--               assert (noGVars rhs'') (return ())
               return rhs''
narrowTop1 t@S{} r = narrowTop1V t r
narrowTop1 _ _     = fail1 "No narrowing at vars"

varBind :: Omega m s r => Ptr s r -> GT s r -> m (ST r) ()
varBind r1 t2 = 
     do { b <- occurs r1 t2 
	; if b 
	    then fail1 "OccursErr"  
	    else write r1 (Just t2) } 

fromFix_ :: (Functor s, Show (s (GTE s r))) => Fix s -> GT s r
fromFix_ (Fix x) = S(fmap fromFix_ x)
fromFix_ (Var n) = GenVar n

toFix_ :: (RWTerm s) => GT s t -> Fix s
toFix_ (MutVar r) = error "toFix: No vars" 
toFix_ (GenVar n) = Var n
                   
toFix_ (S y) = Fix (fmap toFix_ y)

toFixG_ :: (RWTerm s, Functor s, Functor f) => f (GT s r) -> f (Fix s)
toFixG_   = fmap toFix_

fromFixG_ :: (Show (s (GTE s r)), Functor f, Functor s) => f (Fix s) -> f (GT s r)
fromFixG_ = fmap fromFix_

--------------------------------
-- Duplication of Terms
--------------------------------
dupVar sr = readSTRef sr >>= newSTRef
dupTerm (MutVar r) = fmap MutVar (dupVar r)
dupTerm (S t) = fmap S $ mapM dupTerm t
dupTerm x = return x

--dupTermWithSubst subst tt x | trace "dupTermWithSubst" False = undefined
dupTermWithSubst :: (RWTerm s) => 
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

replaceAll :: RWTerm s => [(GT s r, GT s r)] -> GT s r -> GT s r
replaceAll dict x = fromJust$ replaceAll' dict x
   where replaceAll' dict (S t) = lookup (S t) dict `mplus` 
                                  fmap S (mapM (replaceAll' dict) t) 
         replaceAll' dict x = lookup x dict `mplus` return x

------------------------------
-- Obtaining the results
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



runE :: Omega (ErrorT String) s r => 
        (forall r. ErrorT String (ST r) (GTE s r)) -> (GTE s r)
runE c = either (error . show) fromFix (runST (runErrorT (fmap toFix c)))

runEG :: (Omega (ErrorT String) s r, Functor f) =>
         (forall r. ErrorT String (ST r) (f(GTE s r))) -> f(GTE s r)
runEG c = either (error.show) (fmap fromFix) (runST (runErrorT (fmap2 toFix c)))

runEGG :: (Omega (ErrorT String) s r, Functor f, Functor f1) =>
         (forall r. ErrorT String (ST r) (f(f1(GTE s r)))) -> f(f1(GTE s r))
runEGG c = either (error.show) (fmap2 fromFix) (runST (runErrorT (fmap3 toFix c)))

runEIO :: ErrorT String (ST RealWorld) a -> IO a
runEIO = fmap (either (error. show) id) . stToIO . runErrorT



runL :: Omega (ListT) s r => (forall r. ListT (ST r) (GTE s r)) -> [GTE s r]
runL c = map fromFix (runST (runListT (fmap toFix c)))

runLG :: (Omega (ListT) s r, Functor f) =>
         (forall r. ListT (ST r) (f(GTE s r))) -> [f(GTE s r)]
runLG c = map (fmap fromFix) (runST (runListT (fmap2 toFix c)))

runLGG :: (Omega (ListT) s r, Functor f, Functor f1) =>
         (forall r. ListT (ST r) (f(f1(GTE s r)))) -> [f(f1(GTE s r))]
runLGG c = map (fmap2 fromFix) (runST (runListT (fmap3 toFix c)))

runLIO :: ListT (ST RealWorld) a -> IO [a]
runLIO = stToIO . runListT

-----------------------
-- Equivalence of terms
-----------------------

instance RWTerm s => Eq (GTE s r) where
  a == b = --trace "using Equivalence" $ 
            resetVars (idGT a) `equal` resetVars(idGT b)

instance Show(GTE s r) => Show(GT s r) where
    show = show . eqGT  

instance Arbitrary(GTE s r) => Arbitrary(GT s r) where
    arbitrary = fmap idGT arbitrary 

instance (Functor s, Show(s(GTE s r))) => Show(s(GT s r)) where
    show = show . fmap eqGT 

liftGTE2 :: (GT s r -> GT s r -> a) -> GTE s r -> GTE s r -> a
liftGTE2 f x y =  f (idGT x) (idGT y)
liftGTE :: Functor f => (GT s r -> f(GT s r)) -> GTE s r -> f(GTE s r)
liftGTE f = fmap eqGT . f . idGT
fixRules :: [Rule s r] -> [RuleI s r]
fixRules = fmap2 idGT
adaptSubstitutionResult f rre t = fmap (second eqGT) $ f (fixRules rre) (idGT t)

prune	  :: Omega m s r => GTE s r -> m (ST r) (GTE s r)
prune = liftGTE prune_

unify	  :: Omega m s r => GTE s r -> GTE s r -> m (ST r) ()
unify = liftGTE2 unify_

match	  :: Omega m s r => GTE s r -> GTE s r -> m (ST r) ()
match = liftGTE2 match_

instan	  :: Omega m s r => Subst s r -> GTE s r -> m (ST r) (GTE s r)
instan subst = liftGTE (instan_ subst)

-- |leftmost outermost
rewrite1  :: OmegaPlus m s r => [Rule s r] -> GTE s r -> m (ST r) (GTE s r)
rewrite1 rre = liftGTE (rewrite1_ (fixRules rre))

rewrite   :: OmegaPlus m s r => [Rule s r] -> GTE s r -> m (ST r) (GTE s r)
rewrite rre = liftGTE (rewrite_ (fixRules rre))

narrow1   :: OmegaPlus m s r => [Rule s r] -> GTE s r -> 
             m (ST r) (Subst s r, GTE s r)
narrow1 = adaptSubstitutionResult narrow1_

narrow1',narrow1V 
          :: (OmegaPlus m s r, MonadTry (m(ST r))) => [Rule s r] -> GTE s r -> 
             m (ST r) (Subst s r, GTE s r)
narrow1' = adaptSubstitutionResult narrow1'_
narrow1V = adaptSubstitutionResult narrow1V_

-- Unbounded Full Narrowing
narrowFull:: (OmegaPlus m s r, MonadTry (m (ST r))) => [Rule s r] -> GTE s r -> 
             m (ST r) (Subst s r, GTE s r)
narrowFull = adaptSubstitutionResult narrowFull_

-- Unbounded Full Narrowing, with narrowing on variables
narrowFullV:: (OmegaPlus m s r, MonadTry (m (ST r))) =>
              [Rule s r] -> GTE s r -> m (ST r) (Subst s r, GTE s r)
narrowFullV = adaptSubstitutionResult narrowFullV_
narrowFullBounded  :: (OmegaPlus m s r, MonadTry (m (ST r))) =>
                      (GTE s r -> ST r Bool) -> [Rule s r] -> GTE s r -> 
                      m (ST r) (Subst s r, GTE s r)
narrowFullBounded pred = adaptSubstitutionResult (narrowFullBounded_ (pred . eqGT))
narrowFullBoundedV :: (OmegaPlus m s r, MonadTry (m (ST r))) =>
                      (GTE s r -> ST r Bool) -> [Rule s r] -> GTE s r -> 
                      m (ST r) (Subst s r, GTE s r)
narrowFullBoundedV pred = adaptSubstitutionResult (narrowFullBoundedV_ (pred . eqGT))

fromFix  :: (Functor s, Show (s (GTE s r))) => Fix s -> GTE s r
toFix    :: (RWTerm s, Functor s) => GTE s r -> Fix s
fromFixG :: (Show (s (GTE s r)), Functor f, Functor s) => f (Fix s) -> f (GTE s r)
toFixG   :: (RWTerm s, Functor s, Functor f) => f (GTE s r) -> f (Fix s)

toFix   = toFix_ . idGT
fromFix = eqGT . fromFix_ 
toFixG  = toFixG_ . fmap idGT
fromFixG= fmap eqGT . fromFixG_

generalize ::Omega m s r => GTE s r -> m (ST r) (GTE s r)
generalize = liftGTE generalize_

generalizeG::(Traversable f, Omega m s r) => f(GTE s r) -> m (ST r) (f(GTE s r))
generalizeG = fmap2 eqGT . generalizeG_ . fmap idGT

-- |Returns the instantiated term together with the new MutVars 
--  (you need these to apply substitutions) 
autoInst  :: Omega m s r => GTE s r -> m (ST r) (Subst s r, GTE s r)       
autoInst t = fmap (second eqGT) $ autoInst_ (idGT t)

collect   :: Foldable s  => (GTE s r -> Bool) -> GTE s r -> [GTE s r]
collect pred = liftGTE (collect_ (pred . eqGT) )

----------------
-- Other stuff
----------------
someSubterm :: (Traversable t, MonadPlus m) => (a -> m a) -> t a -> m (t a)
someSubterm f x = msum$ interleave f return x

noCVars, noGVars, noMVars :: RWTerm s => GT_ eq s r -> Bool
noGVars = null . collect_ isGenVar
noMVars = null . collect_ isMutVar 
noCVars = null . collect_ isCtxVar 

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

