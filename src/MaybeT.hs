{-# OPTIONS -fallow-undecidable-instances #-}
module MaybeT where
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Fix
import Control.Monad.Error

newtype MaybeT m a = MaybeT { runMaybeT :: m (Maybe a) }

instance Monad m => Monad (MaybeT m) where
	return = MaybeT . return . Just
	m >>= fm = MaybeT$ runMaybeT m >>= \maybe_v ->
	 		case maybe_v of 
			  Nothing -> return Nothing
			  Just v  -> runMaybeT$ fm v
	fail _ = MaybeT (return Nothing)

instance MonadTrans MaybeT where
	lift c = MaybeT (c >>= \v -> return$ Just v)

instance Monad m => MonadPlus (MaybeT m) where
    m1 `mplus` m2 = MaybeT$ runMaybeT m1 >>= \t1 -> 
                     case t1 of 
                       Nothing -> runMaybeT m2
                       _       -> return t1
    mzero = MaybeT (return Nothing)

instance (MonadFix m) => MonadFix (MaybeT m) where
   mfix f = MaybeT $ mfix $ \a -> runMaybeT $ f $ case a of
                                                    Just  r -> r
                                                    _       -> error "empty mfix argument"

instance Monad m => Functor (MaybeT m) where
    fmap f (MaybeT x) = MaybeT (liftM (fmap f) x)


-- ATTENTION!: This MonadError instance is not standard
instance (Monad m) => MonadError e (MaybeT m) where
    throwError _     = MaybeT$ return Nothing
    m `catchError` h = MaybeT$ runMaybeT m >>=  
                       maybe (runMaybeT (h undefined)) (return . Just)


