{-# OPTIONS_GHC -cpp -fglasgow-exts #-}
{-# OPTIONS_GHC -fallow-undecidable-instances #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  TRS.Utils
-- Copyright   :  (c) Pepe Iborra 2006-2007
--                (c) Universidad Politécnica de Valencia 2006-2007
-- License     :  BSD-style (see LICENSE)
--
-- Maintainer  :  pepeiborra@gmail.org
-- Stability   :  experimental
-- Portability :  portable
--
-- Internal
-----------------------------------------------------------------------------

module TRS.Utils where
import Control.Applicative
import Control.Arrow
import Control.Monad.State hiding (mapM, sequence)
import Control.Monad.List (ListT(..))
import Control.Monad.Error (throwError, catchError, Error, ErrorT(..), MonadError)
import Data.Traversable
import Data.Foldable
import Prelude hiding ( all, maximum, minimum, any, mapM_,mapM, foldr, foldl, concat
                      , sequence, and )

import qualified Debug.Trace

inBounds _ [] = False
inBounds 0 _  = True
inBounds i (x:xs) = inBounds (i-1) xs

both f = first f . second f

-- |A fixpoint-like monadic operation. Currenty a bit ugly, maybe there is a 
--- better way to do this 'circularly'
fixM :: MonadPlus m => (a -> m a) -> (a -> m a)
fixM f x = (f x >>= fixM f) `mplus` return x

iterateMn :: Monad m => Int -> (a -> m a) -> a -> m a
iterateMn 0 f x = return x
iterateMn n f x = f x >>= iterateMn (n-1) f 

iterateM f x = let iM f x = x : iM f (x >>= f) in
               sequence $ iM f $ return x


-- |All the pairs of element + rest of the list
selections :: [a] -> [(a,[a])]
selections []     = []
selections (x:xs) = (x,xs) : [ (y,x:ys) | (y,ys) <- selections xs ]

allM :: (Monad m) => (a -> m Bool) -> [a] -> m Bool
allM = (liftM and .) . mapM

class Unpack p u | p -> u where
    unpack :: p -> u

ily pack transform f = unpack . transform (pack . f)

unsafeZipG :: (Traversable t1, Traversable t2) => t1 a -> t2 b -> t2 (a,b)
unsafeZipG t1 t2  = evalState (mapM zipG' t2) (toList t1)
       where zipG' y = do (x:xx) <- get
                          put xx
                          return (x,y)

zipGsafe t1 t2 
    | size t2 > size t1 = evalState (mapM zipG' t2) (toList t1)
    | otherwise = evalState (mapM zipG' t1) (toList t2)
       where zipG' y = do (x:xx) <- get
                          put xx
                          return (x,y)

zipG :: (Traversable t, Traversable t1) =>
        t1 a1 -> t a -> Either (t (a1, a)) (t1 (a, a1))
zipG t1 t2 
    | size t2 > size t1 = Left$ evalState (mapM zipG' t2) (toList t1)
    | otherwise = Right$  evalState (mapM zipG' t1) (toList t2)
       where zipG' y = do (x:xx) <- get
                          put xx
                          return (x,y)

-- | Crappy unzip, takes two traversals
-- TODO: optimize
unzipG :: Traversable t => t (a,b) -> (t a, t b)
unzipG t = let fstz = fmap fst t
               sndz = fmap snd t
           in (fstz, sndz)

unzipG3 :: Traversable t => t (a,b,c) -> (t a, t b, t c)
unzipG3 t = let fstz = fmap (\(a,b,c)->a) t
                sndz = fmap (\(a,b,c)->b) t
                trdz = fmap (\(a,b,c)->c) t
            in (fstz,sndz,trdz)

mapMState :: (Traversable t, Monad m) => (a -> s -> m (b,s)) -> s -> t a -> m (t b, s)
mapMState f s0 x = flip runStateT s0 (mapM f' x)
    where f' y = do s      <- get
                    (v,s') <- lift$ f y s
                    put s'
                    return v

size :: Traversable t => t a -> Int
size = length . toList    

--fmap2 = (fmap.) . fmap
fmap2 f x = fmap (fmap  f) x
fmap3 f x = fmap (fmap2 f) x 

successes :: (MonadPlus m, Functor m) => [m a] -> m [a]
successes cc = fmap concat $ sequence $ map (\c->fmap unit c `mplus` return []) cc
    where unit x = [x]

-- Awesome. Data.Traversable is incredible!
interleave :: (MonadPlus m, Traversable t) =>
                 (a -> m b) -> (a -> m b) -> t a -> [m (t b)]
interleave f g x = let
        indexed_fs = map (indexed f g) [0..size x - 1] 
        indexed f default_f i (j,x) = if i==j then f x else default_f x
     in map (\f->mapM f (unsafeZipG [0..] x)) indexed_fs

----------------------------------------------------------
-- A monad isomorphic to ListT 
-- Only the monadError instance is different
----------------------------------------------------------
newtype ListT' m a = ListT_ {runListT_ :: ListT m a}
  deriving (Monad, MonadPlus, MonadIO, MonadTrans, MonadFix, Functor)

listT'    = ListT_ . ListT 
runListT' = runListT . runListT_

{- This is the standard MonadError instance, useless since ST is not MonadError
instance MonadError e m => MonadError e (ListT' m) where
  throwError _   = listT' (return [])
  catchError m f = listT'$ catchError (runListT' m) (\e-> runListT' (f e))
-}

instance Monad m => MonadError e (ListT' m) where
  throwError _   = listT' (return [])
  catchError m f = listT' (runListT' m       >>= \v -> 
                     if null v 
                                then runListT' (f undefined)
                                else return v)

-- | Try a computation m over an argument a, returning a if it failed
try :: MonadError e m => (a -> m a) -> a -> m a
try m a = m a `catchError` \_->return a

tryListT :: Monad m => a -> ListT m a -> ListT m a
tryListT a (ListT m) = ListT$ do 
  v <- m
  case v of 
    [] -> return [a]
    x  -> return x

try1 m a = let ListT m1 = m a in  
           ListT$ (m1 >>= \v -> return (if null v then [a] else v))
----------------------------------------
-- The brilliant FunctorN class
--  supercedes all fmap, fmap2, fmap3..
----------------------------------------
class FunctorN a b c d | a b c -> d where 
  gfmap :: (a -> b) -> c -> d

instance FunctorN a b a b where
  gfmap = id

instance (Functor f, FunctorN a b c d) => FunctorN a b (f c) (f d) where
  gfmap f = fmap (gfmap f)


class TraversableN a b c d | b c d -> a, a c d -> b, a b d -> c, a b c -> d where
  gmapM :: Monad m => (a -> m b) -> c -> m d

instance TraversableN a b a b where
  gmapM f = f

instance (Traversable f, TraversableN a b c d) => TraversableN a b (f c) (f d) where
  gmapM f = mapM (gmapM f)

---------------------------------------------------------

forEach = flip map
lift2 x = lift$ lift x
mtry f x = f x `mplus` x

atLeast _ []   = False
atLeast 0 _    = True
atLeast n list = atLeast (n-1) (tail list)


runIdentityT = runErrorT_

runIdentityT, runErrorT_ :: (Functor m) => ErrorT [Char] m a -> m a
runErrorT_ =  fmap noErrors . runErrorT
noErrors (Left msg) = error msg
noErrors (Right x)  = x

-- #define DEBUG
trace msg x = 
#ifdef DEBUG 
  Debug.Trace.trace msg x 
#else 
  x 
#endif