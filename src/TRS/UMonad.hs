{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fglasgow-exts #-}
module TRS.UMonad where

import Control.Applicative
import Control.Arrow
import Control.Monad.State
import Data.Foldable
import Data.List ((\\))

import TRS.Substitutions
import TRS.Types
import TRS.Term
import TRS.Rules
import TRS.Utils

class (Functor m, MonadPlus m) => MonadEnv f m | m -> f where
    varBind :: Var (Term g) -> Term f -> m ()
    apply   :: (Var :<: f) => Term f -> m (Term f)
    getEnv  :: m (Subst f)

instance (Eq (Term f), Var :<: f, MonadPlus m) => MonadEnv f (StateT (Subst f) m)    where
    varBind t u = guard (occurs t u) >> modify (insertSubst t u)
    apply t = get >>= \sigma -> return (fixEq (applySubst sigma) t)
    getEnv  = get

instance (Eq (Term f), Var :<: f, MonadPlus m) => MonadEnv f (StateT (Subst f, b) m) where
    varBind t u = withFst $ varBind t u
    apply   t   = withFst $ apply t
    getEnv      = withFst $ get

occurs _ _ = True --TODO

class (Functor m, Monad m) => MonadFresh m where variant :: (f :<: fs, Var :<: f, Var :<: fs, Foldable f, Foldable fs) => Rule f -> Term fs -> m(Rule fs)
  -- The Functor requirement is not necessary, but I find it convenient
  -- Functor should be a siuperclass of Monad

instance Monad m => MonadFresh (StateT [Int] m) where
  variant r@(lhs:->rhs) t = do
     names <- get
     let vars_r = snub (vars lhs ++ vars rhs)
         (vars', names') = splitAt (length vars_r) (names \\ map varId' (vars t))
     put names'
     return $ applySubst (mkSubst (vars_r `zip` map var vars')) <$>  r

instance (Monad m) => MonadFresh (StateT (b, [Int]) m) where variant r t = withSnd $ variant r t

newtype GMonadT s m a = GMonadT {unU :: StateT s m a}
    deriving (Functor, Monad, MonadPlus, MonadPlus1, MonadState s, MonadTrans)

-- Don't understand why deriving does not work for these. Oh well.
--deriving instance (MonadPlus m, MonadEnv f (StateT (Subst f) m)) => MonadEnv f (GMonadT (Subst f) m)
--deriving instance (Functor m, Monad m) => MonadFresh (GMonadT [Int] m)
instance (Monad m, MonadFresh (StateT s m)) => MonadFresh (GMonadT s m) where variant r t = GMonadT $ variant r t
instance (MonadPlus m, MonadEnv f (StateT s m)) => MonadEnv f (GMonadT s m) where
    varBind t u = GMonadT (varBind t u)
    apply  = GMonadT . apply
    getEnv = GMonadT getEnv

type RMonadT   m a = GMonadT [Int] m a
type UMonadT f m a = GMonadT (Subst f) m a
type NMonadT f m a = GMonadT (Subst f, [Int]) m a


--evalU acc sigma = evalStateT (unU acc) sigma
runG s acc = runStateT (unU acc) s
evalG s m  = evalStateT (unU m)  s

runR :: Monad m => RMonadT m a -> m (a, [Int])
runR = runG [0..]
runU :: (Var :<: f, Eq (Term f), Monad m) => UMonadT f m a -> m (a, Subst f)
runU = liftM (second zonkSubst) . runG emptySubst
runN :: (Var :<: f, Eq (Term f), Monad m) => NMonadT f m a -> m (a, Subst f)
runN = liftM (second (zonkSubst . fst)) . runG (emptySubst, [(0::Int)..])

evalR :: Monad m => RMonadT m a -> m a
evalR = evalG [0..]
evalU :: Monad m => UMonadT f m a -> m a
evalU = evalG emptySubst
evalN :: Monad m => NMonadT f m a -> m a
evalN = evalG (emptySubst, [(0::Int)..])

execU :: Monad m => UMonadT f m a -> m (Subst f)
execU acc = execStateT (unU acc) emptySubst

applyF  :: (Var :<: f, f:<:fs, MonadState (Subst fs) m) => f(Term fs) -> m (Term fs)
applyF t = get >>= \sigma -> return (applySubstF sigma t)


----------------------
-- With...
with :: (Monad m, MonadTrans t1, MonadState s (t1 m), MonadState s2 (t2 m)) =>
        (s -> s2) ->
        (s2 -> s -> s) ->
        (t2 m a -> s2 -> m (a,s2)) -> t2 m a -> t1 m a
with gets puts run m = do
      s <- gets `liftM` get
      (res,s') <- lift $ run m s
      modify (puts s')
      return res

withFst :: (MonadState (s, b) (t1 m), MonadTrans t1, Monad m) => StateT s m a -> t1 m a
withFst = with fst (\x' (x,y) -> (x',y)) runStateT
withSnd :: (MonadState (b, s) (t1 m), MonadTrans t1, Monad m) => StateT s m a -> t1 m a
withSnd = with snd (\y' (x,y) -> (x,y')) runStateT
