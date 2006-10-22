{-# OPTIONS_GHC -fglasgow-exts -fallow-undecidable-instances -fno-monomorphism-restriction -fdebugging -cpp#-}

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
                , narrow, narrow1, narrowAll, narrowBU, narrowFull
                , rewrite, rewrite1
                , equal, equalR
                , generalize, generalizeG, instan, autoInst, collect
                , noMVars, noGVars
                , runE, runEG, runEGG 
                , runEIO ) where

import Control.Applicative
import Control.Arrow ( first, second )
import Control.Monad hiding (msum, mapM_, mapM, sequence, forM)
import Control.Monad.List (runListT, ListT(..),lift)
import Control.Monad.Fix
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
import Control.Exception

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

instance Show (s(GT s r)) => Show (Subst s r) where
    show = show . subst

type GTm m s r = m (ST r) (GT s r)
--type MST m r = m (ST r) 

newtype Fix s  = Fix (s (Fix s))
   deriving Show

{-
data Safe s r v p where
    Safe {safe :: GT s r} :: 
-}
type Rule s r = RuleG (GT s r)
data RuleG a = a :-> a -- (GT s r) :-> (GT s r) -- Switch to a newtype for efficiency
   deriving (Eq, Ord)
instance Functor (RuleG) where
    fmap = fmapDefault              --fmap f (l:->r) = f l :-> f r
instance Foldable (RuleG) where 
    foldMap = foldMapDefault        --foldMap f (l:->r) = f l `mappend` f r
instance Traversable (RuleG ) where
    traverse f (l:->r) = (:->) <$> f l <*> f r
{-
instance FunctorM (RuleG s r) where
    fmapM f (l:->r) = do {l' <- f l; r' <- f r; return (l':->r')} 
-}


swap :: Rule s r -> Rule s r
swap (lhs:->rhs) = rhs:->lhs

class (Traversable s) => RWTerm s where
    matchTerm     :: s x -> s x -> Maybe [(x,x)]
    toVar         :: Int -> s a

instance RWTerm s => Eq (GT s r) where
  (==) = equal

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

-- "Omega is just a Type Class constraint synonym" 
--             is an unregistered trademark of Pepe Type Hacker enterprises
class (MonadTrans m, MonadPlus (m (ST r)), Functor (m (ST r)), RWTerm s, Show (s(GT s r))) => 
    Omega (m :: (* -> *) -> * -> *) (s :: * -> *) r

instance (MonadTrans m, MonadPlus (m (ST r)), Functor (m (ST r)), RWTerm s, Show (s (GT s r))) => Omega m s r

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

prune	  :: Omega m s r => 
                       GT s r  -> GTm m s r

unify	  :: Omega m s r => GT s r -> GT s r -> m (ST r) ()
match	  :: Omega m s r => 
                       GT s r -> GT s r -> m (ST r) ()
equal	  :: RWTerm s => GT s r -> GT s r -> Bool
resetVars :: RWTerm s => GT s r -> GT s r
occurs	  :: Omega m s r => 
                       Ptr s r -> GT s r -> m (ST r) Bool
col 	  :: Omega m s r => 
                       GT s r  -> GTm m s r    -- ^Dereference variables
instan	  :: Omega m s r => Subst s r-> GT s r -> GTm m s r
rewrite1  :: Omega m s r => 
                       [Rule s r] -> GT s r -> GTm m s r -- ^leftmost outermost
narrow1   :: Omega m s r => 
                       [Rule s r] -> GT s r -> GTm m s r -- ^leftmost outermost. Assumption: term is MutVars free
narrowAll :: Omega m s r => 
                       [Rule s r] -> GT s r -> m (ST r) [(Subst s r, GT s r)] -- ^leftmost outermost. Assumption: term is MutVars free
generalize:: Omega m s r => GT s r -> GTm m s r
generalizeG :: (Traversable f, Omega m s r) => f(GT s r) -> m (ST r) (f(GT s r))
autoInst  :: Omega m s r => 
                       GT s r -> m (ST r) (Subst s r, GT s r)       -- ^Returns the instantitated term together with the new MutVars (you need these to apply substitutions) 

collect   :: Foldable s => (GT s r -> Bool) -> GT s r -> [GT s r]
fresh	  :: Omega m s r => GTm m s r
readVar   :: (MonadTrans t) => STRef s a -> t (ST s) a
write     :: (MonadTrans t) => STRef s a -> a -> t (ST s) ()

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

-- #define DEBUG
trace msg x = 
#ifdef DEBUG 
  Debug.Trace.trace msg x 
#else 
  x 
#endif
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
             -- Buf, menudo follón con las variables. Tengo q solucionarlo o claudicar...
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
           freshv <- liftM Subst $ replicateM ((maximum$ [i|GenVar i <-gvars]) + 1) fresh
           x' <- instan freshv x
           assert (noGVars x') (return ())
           return (freshv, x')
    where gvars = collect isGenVar x

    -- The intent is to do one rewrite step only
    -- But.. for some MonadPlus's, you might get different results
rewrite1 rr (S t) | trace ("rewrite " ++ show t ++ " with " ++ 
                          (show$ length rr) ++ " rules ") False = undefined
rewrite1 rules (S t)
      | isConst t = rewriteTop (S t)
      | otherwise
      = rewriteTop (S t) `mplus` (fmap S $ someSubterm (rewrite1 rules) t)
       where rewriteTop t = msum $ map (rewriteTop1 t) rules
             rewriteTop1 t r@(lhs :-> rhs) = do
	        (freshv, lhs') <- autoInst lhs
	        match lhs' t
	        trace ("rule fired: " ++ show r ++ " for " ++ show t) $ 
                 instan freshv rhs
rewrite1 _ t = fail1 "no rewrite"  -- TODO: Fail1 or identity? 
narrow1 [] _ = fail1 "narrow: empty set of rules"
narrow1 rules x@(S t) = do
       (vars, x'@(S t')) <- autoInst x
       narrowTop x' `mplus` (fmap S $ someSubterm (narrow1 rules) t')
        where 
          narrowTop t = msum . fmap (narrowTop1 t) $ rules 
--narrow1 _ _ = fail "Narrowing at variable position not allowed"
narrow1 rules (MutVar r) = narrowTop (MutVar r)
        where 
          narrowTop t = msum . fmap (narrowTop1 t) $ rules 

narrowAll [] t = return [(emptyS, t)]
narrowAll rules (S t) = do
    results <- narrowAll' rules (S t)
    if null results then fail1 "No narrowings" else return results
        where 
          narrowAll' :: Omega m s r => [Rule s r] -> GT s r 
                                    -> m (ST r) [(Subst s r, GT s r)]
          narrowAll' rules (S t) | isConst t = narrowAllTop (S t) rules
          narrowAll' rules (S t) = do
              assert (noMVars (S t)) (return ())
              top  <- narrowAllTop (S t) rules
              subs <- successes $interleave (narrowAll' rules) 
                                            (\t->return [(emptyS,t)]) t
              let --combine::[s [(Subst s r, GT s r)]] -> [(Subst s r, GT s r)]
                  combine = fmap( second S
                                . first (Subst . concatMap subst . toList)
                                . unzipG ) 
                          . concat 
                          . fmap parallelComb 
                  subs' = combine subs
              return (top ++ subs')
          narrowAll' _ _ = fail1 "narrowing: variable position"
          narrowAllTop = (successes.). narrowTop
narrowAll rules _ = return []

-------------------------------
-- The New Narrowing Framework
-------------------------------
{- the NarrowState structure makes for a nice state monad handling a narrowing sequenc.
   It is nice because it allows to explore multiple narrowing paths. We are interested
   in (all) the normal (up to narrowing) forms, which means, the failures for the 
   ListT monad when narrowing at top as well as subterms. But, how to grab them ?
   In the ListT monad, failure, that is, mzero, is the empty list. 
   One cannot test for failure, as there is no 'try..handle' abstraction
   Thus, it'd be desirable to install YAMT (yet another monad trasnformer) on top.
   That being the ErrorT MT. But how will this interact? 
   Another option: DIY. Embed this "try..handle" abstraction in the List monad yourself
                   This is what I'm doing now.
-}
data NarrowState s r = NS { rules   :: [Rule s r]
                          , context :: GT s r
                          , csubst  :: Subst s r }

emptyNS rules = NS rules emptyC emptyS

narrowFull :: Omega m s r => [Rule s r] -> GT s r 
           -> m (ST r) [(Subst s r, GT s r)]
narrowFull [] t = return [(emptyS,t)]
narrowFull _rules t = runListT$ do 
     assert (noMVars t) (return ())
     (subst0,t0) <- lift$ autoInst t
     let state0 = NS _rules emptyC subst0
     (t',ns) <- runStateT (search t0) state0
     return (csubst ns, t')
  where 
          step :: Omega m s r => 
                   GT s r -> StateT (NarrowState s r) (ListT (m (ST r))) (GT s r)
          step t = trace ("narrowFull step: " ++ show t) $
              do (ts,cs) <- lift$ ListT$ return$ contexts t
                 under cs$ step ts
             `mplus`
              narrowTop' t
          search t = step t >>= tryStateTListT search 
          narrowTop' :: Omega m s r => GT s r -> 
                        StateT (NarrowState s r) (ListT (m (ST r))) (GT s r)
          narrowTop' t = --trace ("narrowFullTop at " ++ show t) $ 
                        do 
              rules   <- gets rules
              context <- gets context
              subst   <- gets csubst
              r       <- lift$ ListT (return rules)
              (subst',[context'],t') <- lift2$ dupTermWithSubst subst [context] t
              t'' <- lift$ narrowTop t' r
              let new_term = context' |> t''
--              trace "made a narrowing" $  
              modify (\ns -> ns{csubst = subst', context = emptyC})
              return new_term
          narrowTop t r = --wrap failures in the inner monad into mzeros in ListT
                          ListT (fmap box (narrowTop1 t r) `mplus` return [])
          withRules cont = gets rules >>= lift . cont 
          under :: Omega m s r => Context s r -> 
                   StateT (NarrowState s r) (ListT (m (ST r))) (GT s r) -> 
                   StateT (NarrowState s r) (ListT (m (ST r))) (GT s r)
          under cs do_cont = modify (\ns -> ns{context = (context ns) |> cs}) >>
                             do_cont
          lift2 x = lift$ lift x
          box x = [x]
{-
narrowRoot :: (Omega m s r) => [Rule s r] -> Context s -> GT s r
           -> [(Context s, GT s r, Int, Subst s r)]
narrowRoot rules c t = runListT$ do
          (subst,t') <- ListT$ map (narrow1 t) rules
          c' <- 
-}
narrowBU :: (Omega m s r) => [Rule s r] -> GT s r -> m (ST r) [(Subst s r, GT s r)]

{-
narrowBU rules (S t) = runListT$ do
          (st, ct) <- ListT . return $ contexts t
          (ct', subst,  st') <- step rules ct st 
          (_, subst_t,  t' ) <- step rules empty? (S t)
          (st2, ct2) <- ListT$ contexts ct
          (ct2', subst2, st2') <- ListT$ step rules ct2 st2hu
          return [ (subst, c' st')
                 , (subst2 ++ subst, ct2' st2' st')
                 , (subst_t, t')]
-}

narrowBU rules t = runListT$ do
          (ct,subst1,st) <- loop rules t mempty emptyS
          term           <- lift$ generalize (ct|>st)
          assert (noCVars term) (return ())
          return (subst1, term)

loop :: (Omega m s r) => [Rule s r] -> Context s r -> [GT s r] -> Subst s r
                      -> ListT (m(ST r)) (Context s r, Subst s r, GT s r)
-- The results from an iteration of the loop are two:
--  Traversing: Combining all the subterms, order matters
--  Processing: 1. Narrowing at the top (of the subterm)
--              2. BU Narrowing from the subterm
--  - 1. BU Narrowing the subterms sequentially, trying all the possible paths,
--       and then afterwards top-narrow the top. So when a context is all holes,
--       we top-narrow the top! And in this case, 
--    2. Top-Narrowing the subterms (i.e.at the top). That is, if possible
-- Note that all these narrowings are modulo failure. I.e. if a narrowing step
-- fails, we proceed to the next step with the current term. We do not cut

loop _ ct acc s | trace ("loop ct=" ++ show ct ++ ", |acc|=" ++ (show$ length acc)) False = undefined
loop rules ct0 acc subst0 
--    | null cts = return (emptyC, subst0, ct0)
    | null cts = do (_,subst,ct') <- ListT$ tryTopNarrow rules emptyC ct0 subst0
                    return (emptyC, subst, close ct' acc)
    | otherwise = 
        do result <- ListT$ tryTopNarrow rules emptyC (close ct0 acc) subst0
           return result
          `mplus`
        do (st,ct)          <- ListT$ return cts
           (st',subst,stst) <- loop rules st mempty subst0
           (ct',subst',st') <- loop rules ct ((st'|> stst) : acc) subst
           ListT$ tryTopNarrow rules emptyC (close ct' (st':acc)) subst'
    where cts = contexts ct0
          atom [x] = True
          atom _   = False
close ct [] = ct
close ct (st:stt) = close (ct |> st) stt

-- This just returns all the possible 1-step narrowings at the top position.
-- However, if no narrowing is possible, it returns the original term.
-- So effectively this action NEVER FAILS
-- Furthermore, it takes care of applyiing the obtained substitution to 
--  the given context, and returning the compound substitution
tryTopNarrow :: (Omega m s r) => [Rule s r] -> Context s r -> GT s r -> Subst s r 
     -> m(ST r) [(Context s r, Subst s r, GT s r)]
tryTopNarrow rules ct t subst0 = do
          narrows <- successes$ narrowTop t rules
          case narrows of          -- Taking care of the no-narrows case
            [] -> return [(ct, subst0, t)]
            _  -> forM narrows $ \(subst, t') -> do
                    ct'    <- instan subst ct
                    subst' <- subst *& subst0
                    t''    <- generalize t'  --Note the implications of generalize here!
                    return (ct', subst', t'')

mtry f x = f x `mplus` x

rewrite   :: (Omega m s r) => [Rule s r] -> GT s r -> m (ST r) (GT s r)
narrow    :: (Omega m s r) => [Rule s r] -> GT s r -> m (ST r) (GT s r)
rewrite rules = fixM (rewrite1 rules)
narrow  rules = fixM (narrow1 rules)

isConst :: Foldable t => t a -> Bool
isConst = null . toList

someSubterm :: (Traversable t, MonadPlus m) => (a -> m a) -> t a -> m (t a)
someSubterm f x = msum$ interleave f return x
{-
interleaveBut ii f g x =  [ liftM ((,) i) x 
                            | (i,x) <- zip [0..] interleave f g x
                            , i `notElem` ii]
-}
narrowTop :: Omega m s r => GT s r -> [Rule s r]
                            -> [m (ST r) (Subst s r, GT s r)]
narrowTop t rules = assert (noMVars t) $ unsafeNarrowTop t rules

unsafeNarrowTop :: Omega m s r => GT s r -> [Rule s r]
                               -> [m (ST r) (Subst s r, GT s r)]
unsafeNarrowTop t rules = flip map rules $ \r -> do
              (vars, t') <- autoInst t
              t''        <- narrowTop1 t' r
              return (vars, t'')

narrowTop1 :: Omega m s r => GT s r -> Rule s r 
                          -> m (ST r) (GT s r)
narrowTop1 t@S{} r@(lhs:->rhs) = do
               assert (noGVars t) (return ())
               assert (noMVars lhs) (return ())
               assert (noMVars rhs) (return ())
               (lhsv, lhs') <- autoInst lhs
               unify lhs' t
--               trace ("narrowing fired: " ++ show t ++ " " ++ show r ) (return ()) 
               rhs' <- instan lhsv rhs -- Pensar que la sustitución debe cubrir a 
                                -- todo el término. ¿Lo cumple esta impl.?
               rhs'' <- col rhs'         -- OPT: col here might be unnecesary
               assert (noGVars rhs'') (return ())
               return rhs''
narrowTop1 _ _ = fail1 "No rewriting at vars"

varBind :: Omega m s r => Ptr s r -> GT s r -> m (ST r) ()
varBind r1 t2 = 
     do { b <- occurs r1 t2 
	; if b 
	    then fail1 "OccursErr"  
	    else write r1 (Just t2) } 

vars = "XYZWJIKHW"
instance (Show (s (GT s r))) => Show (GT s r) where
    show (S s)      = show s
    show (GenVar n) = if n < length vars then [vars !! n] else ('v' : show n)
    show (MutVar r) = "?"
    show (CtxVar c) = '[' : show c ++ "]" 

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

equalR (l1:->r1) (l2:->r2) = l1 `equal` l2 && r1 `equal` r2


{-# INLINE fail1 #-}
fail1 :: Monad m => String -> m a 
fail1 msg = trace msg $ fail msg
--fail1 = fail

instance Show (a) => Show (RuleG (a)) where
    show (a:->b) = show a ++ " -> " ++ show b
--    showList  = unlines . map show

-- TODOs:
-- - Float pruning to the type
-- - Fuse seq and map into mapM
-- - OPT: instantiate all rules before starting the rewrite/narrowing rows
-- - Replace parts of the RSclass with a Traversable instance


{- Substitution Composition 

If we model a substitution as simply a list of Mvars, with which to instantiate GVars,
it is going to be really painful to model substitution composition.
But moreover, we are not interested in full composition of substitutions. In fact, only
composition of disjoint substitutions is needed!
Suppose we have 5 GenVars, and some first narrowing step gives the substitution:
{a,[],[],[],[]}
[] Represent empty substitutions. That is, only instantiating the first 
-}
(*&) :: Omega m s r => Subst s r -> Subst s r -> m (ST r) (Subst s r)
(Subst s1) *& (Subst s2) = do
        s1' <- l s1
        s2' <- l s2
        v   <- lift$ zipWithM compose1 s1' s2'
        return (Subst v)
    where compose1 (MutVar r1) (MutVar r2) = do
            v1 <- readSTRef r1
            v2 <- readSTRef r2
            writeSTRef r1 (v1 `mplus` v2)
            return (MutVar r1)
          unitValue = fresh
          max_l = max (length s1) (length s2)
          l x = if length x < max_l
                then liftM (x ++) $ replicateM (max_l - length x) unitValue
                else return x

emptyS = Subst mempty

dupVar sr = readSTRef sr >>= newSTRef
dupTerm (MutVar r) = fmap MutVar (dupVar r)
dupTerm (S t) = fmap S $ mapM dupTerm t
dupTerm x = return x

dupTermWithSubst :: Omega m s r => Subst s r -> [GT s r] -> GT s r 
                 -> m (ST r) (Subst s r, [GT s r], GT s r)
--dupTermWithSubst subst tt x | trace "dupTermWithSubst" False = undefined
dupTermWithSubst (Subst s) tt (MutVar r) = lift$ do
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

liftSubst f (Subst s) = Subst (f s)

instance Show (GT s r) => Observable (GT s r) where
    observer = observeBase