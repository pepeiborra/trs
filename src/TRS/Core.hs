{-# OPTIONS_GHC -fglasgow-exts -fallow-undecidable-instances -fno-monomorphism-restriction -fdebugging -cpp #-}

-----------------------------------------------------------------------------------------
{-| Module      : TRS.Core
    Copyright   : 
    License     : All Rights Reserved

    Maintainer  : 
    Stability   : 
    Portability : 
-}
-----------------------------------------------------------------------------------------

module TRS.Core ( GT(..), isMutVar, isGenVar, isCtxVar, GTm
		, Fix(..), toFix, fromFix, toFixG, fromFixG
                , Subst
                , Rule, RuleG(..), swap
                , RWTerm(..), Omega
                , narrow1, narrow1', narrow1V, narrowFull, narrowFullV
                , narrowFullBounded, narrowFullBoundedV
                , rewrite, rewrite1
                , equal
                , generalize, generalizeG, instan, autoInst, collect
                , noMVars, noGVars
                , runE, runEG, runEGG, runEIO
                , run, runG, runGG, runIO) where

import Control.Applicative
import Control.Arrow ( first, second )
import Control.Monad hiding (msum, mapM_, mapM, sequence, forM)
import Control.Monad.List (runListT, ListT(..),lift)
import Control.Monad.Identity (runIdentity)
import Control.Monad.ST
import Control.Monad.Error (ErrorT(..), MonadTrans(..))
import Control.Monad.State (StateT(..), gets, modify)
import Data.STRef
import Data.List ((\\), nub, elemIndex)
import Data.Traversable
import Data.Foldable
import Data.Maybe (fromJust)
import Data.Monoid
import Prelude hiding ( all, maximum, minimum, any, mapM_,mapM, foldr, foldl
                      , and, concat, concatMap, sequence, notElem)
import TRS.Context
import TRS.Utils
import Control.Exception (assert)

import qualified Debug.Trace
import GHC.Exts (breakpointCond)
import Observe

data GT s r = 
   S (s (GT s r))
 | MutVar (STRef r (Maybe (GT s r)))
 | GenVar Int
 | CtxVar Int

type Ptr s r   = STRef r (Maybe (GT s r))
newtype Subst s r = Subst {subst::[GT s r]}

emptyS = Subst mempty

type GTm m s r = m (ST r) (GT s r)

newtype Fix s  = Fix (s (Fix s))
   deriving Show

type Rule s r = RuleG (GT s r)
data RuleG a = a :-> a -- (GT s r) :-> (GT s r) -- Switch to a newtype for efficiency
   deriving (Eq, Ord)
instance Functor (RuleG) where
    fmap = fmapDefault              --fmap f (l:->r) = f l :-> f r
instance Foldable (RuleG) where 
    foldMap = foldMapDefault        --foldMap f (l:->r) = f l `mappend` f r
instance Traversable (RuleG ) where
    traverse f (l:->r) = (:->) <$> f l <*> f r

class (Traversable s) => RWTerm s where
    matchTerm     :: s x -> s x -> Maybe [(x,x)]
    toVar         :: Int -> s a

instance RWTerm s => Eq (GT s r) where
  (==) = equal

-- "Omega is just a Type Class constraint synonym" 
--             is an unregistered trademark of Pepe Type Hacker enterprises
class (MonadTrans m, Monad (m (ST r)), Functor (m (ST r)), RWTerm s, Show (s(GT s r))) => 
    Omega (m :: (* -> *) -> * -> *) (s :: * -> *) r

class (Omega m s r, MonadPlus (m (ST r))) => OmegaPlus m s r 

instance (MonadTrans m, Monad (m (ST r)), Functor (m (ST r)), RWTerm s, Show (s (GT s r))) => Omega m s r
instance (MonadTrans m, MonadPlus (m (ST r)), Functor (m (ST r)), RWTerm s, Show (s (GT s r))) => OmegaPlus m s r

prune	  :: Omega m s r => GT s r  -> GTm m s r

unify	  :: Omega m s r => GT s r -> GT s r -> m (ST r) ()
match	  :: Omega m s r => GT s r -> GT s r -> m (ST r) ()
equal	  :: RWTerm s    => GT s r -> GT s r -> Bool
resetVars :: RWTerm s    => GT s r -> GT s r
occurs	  :: Omega m s r => Ptr s r -> GT s r -> m (ST r) Bool
-- |Dereference variables
col 	  :: Omega m s r => GT s r  -> GTm m s r    
instan	  :: Omega m s r => Subst s r-> GT s r -> GTm m s r
-- |leftmost outermost
rewrite1  :: OmegaPlus m s r => [Rule s r] -> GT s r -> m (ST r) (GT s r)
rewrite   :: OmegaPlus m s r => [Rule s r] -> GT s r -> m (ST r) (GT s r)
narrow1   :: OmegaPlus m s r => [Rule s r] -> GT s r -> m (ST r) (Subst s r, GT s r)
-- Unbounded Full Narrowing

narrowFull:: (RWTerm s, Show (s (GT s r))) => [Rule s r] -> GT s r -> ST r [(Subst s r, GT s r)]
-- Unbounded Full Narrowing, with narrowing on variables

narrowFullV:: (RWTerm s, Show (s (GT s r))) => 
              [Rule s r] -> GT s r -> ST r [(Subst s r, GT s r)]
narrowFullBounded  :: (RWTerm s, Show (s (GT s r))) => 
                      (GT s r -> ST r Bool) -> [Rule s r] -> GT s r -> 
                      ST r [(Subst s r, GT s r)]
narrowFullBoundedV :: (RWTerm s, Show (s (GT s r))) => 
                      (GT s r -> ST r Bool) -> [Rule s r] -> GT s r -> 
                      ST r [(Subst s r, GT s r)]

generalize ::Omega m s r => GT s r -> GTm m s r
generalizeG::(Traversable f, Omega m s r) => f(GT s r) -> m (ST r) (f(GT s r))
-- |Returns the instantiated term together with the new MutVars 
--  (you need these to apply substitutions) 
autoInst  :: Omega m s r => GT s r -> m (ST r) (Subst s r, GT s r)       
collect   :: Foldable s  => (GT s r -> Bool) -> GT s r -> [GT s r]
fresh	  :: Omega m s r => GTm m s r
readVar   :: MonadTrans t=> STRef s a -> t (ST s) a
write     :: MonadTrans t=> STRef s a -> a -> t (ST s) ()

fresh = lift (newSTRef Nothing) >>= return . MutVar
readVar r = lift$ readSTRef r
write r x = lift$ writeSTRef r x
--    collect :: (GT s r -> Bool) -> GT s r -> [GT s r]
-- | Ought to call colGT before this to make sure all the variables have
--   been dereferenced 
collect p (S x) = foldr (\t gg -> collect p t ++ gg) [] x
collect p x = if p x then [x] else []

prune (typ @ (MutVar ref)) =
	do { m <- readVar ref
	   ; case m of
	      Just t ->
		do { newt <- prune t
		   ; write ref (Just newt)
		   ; return newt }
	      Nothing -> return typ}
prune x = return x

col x =
     do { x' <- prune x
	; case x' of
	  (S y) -> 
	    do { t <- (mapM col y) 
	       ; return (S t)} 
	  _     -> return x'}
occurs v t = 
     do { t2 <- prune t 
	; case t2 of 
	  S w -> 
	    do { s <- (mapM (occurs v) w) 
	       ; return(foldr (||) False s ) 
	       } 
	  MutVar z -> return (v == z) 
	  _ -> return False } 
unify tA tB = 
     do  t1 <- prune tA 
	 t2 <- prune tB 
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
		Nothing -> fail1 ("ShapeErr in unify(" ++ show tA ++ ',' : show tB ++ ")")
		Just pairs -> 
		  mapM_ (uncurry unify) pairs 
	   (_,_) -> fail1 "ShapeErr? (U)" 

match tA tB | trace ("match " ++ show tA ++ " and " ++ show tB) False = undefined
match tA tB = 
     do { t1 <- prune tA 
	; t2 <- prune tB 
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
		  mapM_ (uncurry match) pairs 
	  (_,_) -> fail1 "ShapeErr?" 
	} 
equal x y = go (resetVars x) (resetVars y) 
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
           
instan sub x = 
      do { x' <- prune x 
	 ; case x' of 
	    GenVar n | n < length (subst sub) -> col (subst sub !! n) 
	    S x -> fmap S (mapM (instan sub) x) 
            _ -> return x'
	 } 
generalize x = do
           x' <- col x
           let gvars = collect isGenVar x'
               mvars = collect isMutVar x'
               tot   = length gvars + length mvars
               new_gvars = map (Just . GenVar) 
                               ([0..tot]\\[j|GenVar j <- gvars])
           zipWithM write [v|MutVar v <-mvars] new_gvars
           x'' <- col x'
           assert (noMVars x'') (return ())
           return x''

generalizeG x = do
           x' <- mapM col x
           let gvars = nub$ concat (toList (fmap (collect isGenVar) x'))
               mvars = nub$ concat (toList (fmap (collect isMutVar) x'))
               tot   = length gvars + length mvars
               new_gvars = map (Just . GenVar)
                               ([0..tot]\\[j|GenVar j <- gvars])
           zipWithM write [v|MutVar v <-mvars] new_gvars
           x'' <- mapM col x'
           assert (all noMVars x'') (return ())
           return x''


resetVars x@S{} = reset x
    where reset g@(GenVar {}) = new_gvars !! fromJust(elemIndex g gvars)
          reset r@(MutVar {}) = new_mvars !! fromJust(elemIndex r mvars)
          reset (S t)      = S$ fmap reset t 
          gvars = collect isGenVar x
          mvars = collect isMutVar x
          new_gvars = map GenVar [0..]
          new_mvars = map GenVar [length gvars..]
resetVars x = x

autoInst x | null (collect isGenVar x) = return (emptyS,x)
autoInst x@MutVar{} = return (emptyS, x)
autoInst (GenVar _) = do v <- fresh
                         return (Subst [v], v)
autoInst x
    | null gvars = return (emptyS, x)
    | otherwise  = do
           freshv <- liftM Subst $ replicateM ((maximum$ [i|GenVar i <-gvars]) + 1) 
                                              fresh
           x' <- instan freshv x
           assert (noGVars x') (return ())
           return (freshv, x')
    where gvars = collect isGenVar x

autoInstG xx | null gvars = return (emptyS, xx)
             | otherwise  = do
           freshv <- liftM Subst $ replicateM ((maximum$ [i|GenVar i <-gvars]) + 1) 
                                              fresh
           xx' <- mapM (instan freshv) xx
           assert (all noGVars xx') (return ())
           return (freshv, xx')
    where gvars = concatMap (collect isGenVar) xx

    -- The intent is to do one rewrite step only
    -- But.. for some MonadPlus's, you might get different results
rewrite1 rr (S t) | trace ("rewrite " ++ show t ++ " with " ++ 
                          (show$ length rr) ++ " rules ") False = undefined
rewrite1 _ t | assert (noMVars t) False = undefined
rewrite1 rules (S t)
--      | isConst t = rewriteTop rules (S t)
      | otherwise
      = rewriteTop (S t) `mplus` (fmap S$ someSubterm (rewrite1 rules) t) 
        where rewriteTop t = msum$ forEach rules $ \r@(lhs:->rhs) -> do
	        (freshv, lhs') <- autoInst lhs
	        match lhs' t
	        trace ("rule fired: " ++ show r ++ " for " ++ show t) (return 0)
                instan freshv rhs

rewrite1 _ t = fail1 "no rewrite"

rewrite rules = fixM (rewrite1 rules)

narrow1 [] _ = fail1 "narrow: empty set of rules"
narrow1 _ t | trace ("narrow1 " ++ show t) False = undefined
narrow1 _ t | assert (noMVars t) False = undefined
narrow1 rules t@S{} = narrow1' (t, emptyC)
    where narrow1' (t, ct) = 
              narrowTop rules ct t
             `mplus` 
              msum (map narrow1' (contexts t))

-------------------------------
-- The New Narrowing Framework
-------------------------------
narrow1' = narrowFullG narrowTop'  (const (return True)) 
narrow1V = narrowFullG narrowTopV' (const (return True)) 

narrowFull  = narrowFullG narrowTop' (const (return False))
narrowFullV = narrowFullG narrowTopV' (const (return False))
narrowFullBounded = narrowFullG narrowTop'
narrowFullBoundedV = narrowFullG narrowTopV'

narrowFullG :: (RWTerm s, Show(s(GT s r))) =>
              ([Rule s r] -> Context s r -> Subst s r -> GT s r
                          -> ListT (ST r) (Subst s r, GT s r)) 
            -> (GT s r -> ST r Bool)
            -> [Rule s r] -> GT s r 
            -> ST r [(Subst s r, GT s r)]

narrowFullG _ done [] t = trace ("narrowFull " ++ show t ++ " with empty TRS") $ 
                     return [(emptyS,t)]
narrowFullG narrowTop1base done rules t = runListT$ do 
     assert (noMVars t) (return ())
     (subst0,t0) <- autoInst t
     search emptyS t0
  where 
          step cs subst t = trace ("narrowFull step: " ++ show t) $
                   lift (done t) >>= guard >> 
                   (msum$ forEach (contexts t) $ \(ts,cs1) -> 
                       step (cs|>cs1) subst ts)
             `mplus`
                   narrowTop rules cs subst t
          search subst t = step emptyC subst t >>= try(uncurry search) 
          narrowTop = narrowTop1base

narrowTop,narrowTopV :: OmegaPlus m s r => [Rule s r] -> Context s r -> GT s r
                            -> m (ST r) (Subst s r, GT s r)
narrowTop rules ct t = assert (all noMVars [t,ct]) $ unsafeNarrowTop t rules ct
narrowTopV rules ct t = assert (all noMVars [t,ct])$ unsafeNarrowTopV t rules ct
narrowTop' rules ct s t = assert (all noMVars [t,ct])$ unsafeNarrowTop' t rules ct s
narrowTopV' rules ct s t= assert (all noMVars [t,ct])$ unsafeNarrowTopV' t rules ct s

unsafeNarrowTop, unsafeNarrowTopV
    :: OmegaPlus m s r => GT s r -> [Rule s r] -> GT s r
                               -> m (ST r) (Subst s r, GT s r)
unsafeNarrowTop', unsafeNarrowTopV'
    :: OmegaPlus m s r => GT s r -> [Rule s r] -> GT s r -> Subst s r
                               -> m (ST r) (Subst s r, GT s r)
unsafeNarrowTop   = unsafeNarrowTopG narrowTop1
unsafeNarrowTopV  = unsafeNarrowTopG narrowTop1V
unsafeNarrowTop'  = unsafeNarrowTopG' narrowTop1
unsafeNarrowTopV' = unsafeNarrowTopG' narrowTop1V

unsafeNarrowTopG _ t _ _ | trace ("unsafeNarrowTop") False = undefined
unsafeNarrowTopG narrowTop1 t rules ct = msum$ forEach rules $ \r -> do
               (vars, [t',ct']) <- autoInstG [t,ct]
               t''              <- narrowTop1 t' r
               return (vars, ct'|>t'')

unsafeNarrowTopG' narrowTop1 t rules ct subst = msum$ forEach rules $ \r -> do
               (subst', [ct'], t') <- lift$ dupTermWithSubst subst [ct] t
               t'' <- narrowTop1 t' r
               return (subst', ct'|>t'')

narrowTop1, narrowTop1V :: Omega m s r => GT s r -> Rule s r 
                          -> m (ST r) (GT s r)
narrowTop1V t r@(lhs:->rhs) = do
               assert (noGVars t) (return ())
               assert (noMVars lhs) (return ())
               assert (noMVars rhs) (return ())
               (lhsv, lhs') <- autoInst lhs
               unify lhs' t
               trace ("narrowing fired: t=" ++ show t ++ ", rule=" ++ show r ) (return ()) 
               rhs' <- instan lhsv rhs
               rhs'' <- col rhs'         -- OPT: col here might be unnecesary
               assert (noGVars rhs'') (return ())
               return rhs''
narrowTop1 t@S{} r = narrowTop1V t r
narrowTop1 _ _     = fail1 "No narrowing at vars"

varBind :: Omega m s r => Ptr s r -> GT s r -> m (ST r) ()
varBind r1 t2 = 
     do { b <- occurs r1 t2 
	; if b 
	    then fail1 "OccursErr"  
	    else write r1 (Just t2) } 

fromFix :: (Functor s, Show (s (GT s r))) => Fix s -> GT s r
fromFix (Fix x) = S(fmap fromFix x)

toFix :: (RWTerm s) => GT s t -> Fix s
toFix (MutVar r) = error "toFix: No vars" 
toFix (GenVar n) = --error "toFix: No generic vars" 
                  Fix (toVar n) 
toFix (S y) = Fix (fmap toFix y)

toFixG :: (RWTerm s, Functor s, Functor f) => f (GT s r) -> f (Fix s)
toFixG   = fmap toFix

fromFixG :: (Show (s (GT s r)), Functor f, Functor s) => f (Fix s) -> f (GT s r)
fromFixG = fmap fromFix

--------------------------------
-- Duplication of Terms
--------------------------------
dupVar sr = readSTRef sr >>= newSTRef
dupTerm (MutVar r) = fmap MutVar (dupVar r)
dupTerm (S t) = fmap S $ mapM dupTerm t
dupTerm x = return x

dupTermWithSubst :: (RWTerm s, Show (s (GT s r))) => 
                    Subst s r -> [GT s r] -> GT s r 
                 -> ST r (Subst s r, [GT s r], GT s r)
--dupTermWithSubst subst tt x | trace "dupTermWithSubst" False = undefined
dupTermWithSubst (Subst s) tt (MutVar r) = do
    newvar <- dupVar r
    let subst' = Subst$ fmap (replace (MutVar r) (MutVar newvar)) s
    let tt'    = fmap (replace (MutVar r) (MutVar newvar)) tt
    return (subst', tt', MutVar newvar)

dupTermWithSubst subst tt (S t) = fmap unwrap$  mapMState foldFun (subst, tt) t
    where wrapRes (subst,tt,t) = (t, (subst, tt))
          unwrap  (t, (subst, tt)) = (subst, tt, S t)
          foldFun t (s,tt) = do (s',tt',t') <- dupTermWithSubst s tt t 
                                return (t',(s',tt'))

dupTermWithSubst subst tt x = return (subst, tt, x)

replace x x' (S t) = S$ fmap (replace x x') t
replace x x' y | x == y = x'
replace _ _ y = y 

------------------------------
-- Obtaining the results
------------------------------
run :: (RWTerm s, Show (s (GT s r))) => (forall r.ST r (GT s r)) -> GT s r
run c = fromFix (runST (fmap toFix c))

runG :: (RWTerm s, Show (s (GT s r)), Functor f) =>
         (forall r.ST r (f(GT s r))) -> f(GT s r)
runG c = (fmap fromFix) (runST ( (fmap2 toFix c)))

runGG :: (RWTerm s, Show (s (GT s r)), Functor f, Functor f1) =>
         (forall r.ST r (f(f1(GT s r)))) -> f(f1(GT s r))
runGG c = (fmap2 fromFix) (runST ( (fmap3 toFix c)))

runIO :: 
            ErrorT String (ST RealWorld) a
         -> IO a
runIO = fmap (either (error. show) id) . stToIO . runErrorT

runE :: Omega (ErrorT String) s r => 
        (forall r. ErrorT String (ST r) (GT s r)) -> (GT s r)
runE c = either (error . show) fromFix (runST (runErrorT (fmap toFix c)))

runEG :: (Omega (ErrorT String) s r, Functor f) =>
         (forall r. ErrorT String (ST r) (f(GT s r))) -> f(GT s r)
runEG c = either (error.show) (fmap fromFix) (runST (runErrorT (fmap2 toFix c)))

runEGG :: (Omega (ErrorT String) s r, Functor f, Functor f1) =>
         (forall r. ErrorT String (ST r) (f(f1(GT s r)))) -> f(f1(GT s r))
runEGG c = either (error.show) (fmap2 fromFix) (runST (runErrorT (fmap3 toFix c)))

runEIO :: 
            ErrorT String (ST RealWorld) a
         -> IO a
runEIO = fmap (either (error. show) id) . stToIO . runErrorT

--------------------------------
-- Instances and base operators
--------------------------------
liftSubst f (Subst s) = Subst (f s)
swap :: Rule s r -> Rule s r
swap (lhs:->rhs) = rhs:->lhs

vars = "XYZWJIKHW"
instance (Show (s (GT s r))) => Show (GT s r) where
    show (S s)      = show s
    show (GenVar n) = if n < length vars then [vars !! n] else ('v' : show n)
    show (MutVar r) = "?"
    show (CtxVar c) = '[' : show c ++ "]" 

instance (RWTerm s, Ord (s (GT s r))) => Ord (GT s r) where
    compare (S t1) (S t2) = compare t1 t2
    compare S{} _ = GT
    compare _ S{} = LT
    compare MutVar{} MutVar{} = EQ
    compare GenVar{} GenVar{} = EQ
    compare GenVar{} MutVar{} = GT
    compare MutVar{} GenVar{} = LT
    compare _ CtxVar{} = GT
    compare CtxVar{} _ = LT

instance Show (s(GT s r)) => Show (Subst s r) where
    show = show . subst

instance Show (a) => Show (RuleG (a)) where
    show (a:->b) = show a ++ " -> " ++ show b
--    showList  = unlines . map show

----------------
-- Other stuff
----------------
someSubterm :: (Traversable t, MonadPlus m) => (a -> m a) -> t a -> m (t a)
someSubterm f x = msum$ interleave f return x

isGenVar, isMutVar, isCtxVar :: GT s r -> Bool
isGenVar GenVar{} = True
isGenVar _ = False
isMutVar MutVar{} = True
isMutVar _ = False
isCtxVar CtxVar{} = True
isCtxVar _ = False

noCVars, noGVars, noMVars :: RWTerm s => GT s r -> Bool
noGVars = null . collect isGenVar
noMVars = null . collect isMutVar 
noCVars = null . collect isCtxVar 

isConst :: Foldable t => t a -> Bool
isConst = null . toList

instance Show (GT s r) => Observable (GT s r) where
    observer = observeBase

#define DEBUG
trace msg x = 
#ifdef DEBUG 
  Debug.Trace.trace msg x 
#else 
  x 
#endif

{-# INLINE fail1 #-}
fail1 :: Monad m => String -> m a 
fail1 msg = trace msg $ fail msg
--fail1 = fail

-- TODOs:
-- - Float pruning to the type

