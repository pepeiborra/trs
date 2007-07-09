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
import qualified Control.Monad.LogicT as LogicT
import Control.Monad.Error (throwError, catchError, Error, ErrorT(..), MonadError)
import Control.Monad.LogicT.SFKT (SFKT)
import Data.List (group, sort)
import Data.Traversable
import Data.Foldable
import qualified Prelude
import Prelude hiding ( all, maximum, minimum, any, mapM_,mapM, foldr, foldl, concat
                      , sequence, and, elem )

import qualified Debug.Trace
import Control.Exception

snub :: Ord a => [a] -> [a]
snub = map head . group . sort

g `at` f = \x y -> g (f x) (f y)

inBounds _ [] = False
inBounds 0 _  = True
inBounds i (x:xs) = inBounds (i-1) xs

x `isSubsetOf` y = all (`elem` y) x

both f = first f . second f

------------------------------------------------------------------------
--
-- Monadic versions of functions on lists
-- (stolen from http://www.cee.hw.ac.uk/DART/software/rank2-HW/)

-- Assumes that xs and xy have already been nub-ed.
unionByM :: Monad m => (a -> a -> m Bool) -> [a] -> [a] -> m [a]
unionByM p xs ys =
    go xs ys
    where go xs' [] = return xs'
	  go xs' (y':ys') =
	      do b <- elemByM p y' xs'
		 if b then go xs' ys' else go (y':xs') ys'

elemByM :: Monad m => (a -> a -> m Bool) -> a -> [a] -> m Bool
elemByM _ _ [] = return False
elemByM p x (y:ys) =
    do b <- p x y
       if b then return True else elemByM p x ys


nubByM f l = nubByM' l [] where
  nubByM' [] _ = return []
  nubByM' (x:xs) ls = trace "nubByM'" $ do
    b <- elemByM f x ls
    if b then nubByM' xs ls else (x:) <$> nubByM' xs (x:ls)
    

nubByM1 :: Monad m => (a -> a -> m Bool) -> [a] -> m [a]
nubByM1 _ [] = return []
nubByM1 p (x:xs) =
    do ys <- nubByM1 p xs
       b <- elemByM p x ys
       if b then return ys else return (x:ys)

deleteByM :: Monad m => (a -> a -> m Bool) -> a -> [a] -> m [a]
deleteByM _ _ [] = return []
deleteByM p x (y:ys) =
    do xs <- deleteByM p x ys
       b <- p x y
       if b then return xs else return (y : xs)

-- -----------------------------------------------------------

secondM f (x, y) = f y >>= \y' -> return (x,y')

-- |A fixpoint-like monadic operation. Currenty a bit ugly, maybe there is a 
--- better way to do this 'circularly'
fixM :: MonadPlus m => (a -> m a) -> (a -> m a)
fixM f x = (f x >>= fixM f) `mplus` return x

iterateMn :: Monad m => Int -> (a -> m a) -> a -> m a
iterateMn 0 f x = return x
iterateMn n f x = f x >>= iterateMn (n-1) f 

iterateM f x = let iM f x = x : iM f (x >>= f) in
               sequence $ iM f $ return x

concatMapM f = fmap concat . mapM f

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

modifySpine t xx = assert (xx >=: toList t) $  mapM (\_-> pop) t `evalState` xx
  where pop = gets head >>= \v -> modify tail >> return v

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

#if __GLASGOW_HASKELL__ < 607
f >=> g = \ x -> f x >>= g
#endif
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
----------------------------------------------------------
-- A monad isomorphic to ErrorT 
-- Only the monadPlus instance is different
----------------------------------------------------------
newtype ErrorT' e m a = ErrorT_ {unErrorT :: ErrorT e m a}
  deriving (Monad, MonadError e, MonadIO, MonadTrans, MonadFix, Functor)

runErrorT' = runErrorT . unErrorT

instance (Error e, MonadPlus m) => MonadPlus (ErrorT' e m) where
  mzero = ErrorT_ mzero
  ErrorT_ (ErrorT m1) `mplus` ErrorT_ (ErrorT m2) = (ErrorT_ . ErrorT) 
                                                    (m1 `mplus` m2) 

----------------------------------------
-- The brilliant FunctorN class
--  supercedes all fmap, fmap2, fmap3..
--  but produces headache type errors
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

-- -------------------------------------
-- MonadComp: Composing Monads weirdly
-- -------------------------------------

newtype MCompT (t1 :: (* -> *) -> * -> *) (t2 :: (* -> *) -> * -> *) (m :: * -> *) a = MCompT {unMCompT :: t1 (t2 m) a}
  deriving (MonadError e, MonadPlus, Monad, Functor) --, LogicT (MCompT t1 t2))

-- Cant really define a MonadTrans instance!!!
--instance (MonadTrans t1, MonadTrans t2) => MonadTrans (MCompT t1 t2) where 
instance (Error e, MonadTrans t1) => MonadTrans (MCompT t1 (ErrorT e)) where 
   lift m = MCompT (lift (lift m))
instance (Error e, MonadTrans t1) => MonadTrans (MCompT t1 (ErrorT' e)) where 
   lift m = MCompT (lift (lift m))
instance (MonadTrans t1) => MonadTrans (MCompT t1 ListT) where 
   lift m = MCompT (lift (lift m))
instance (MonadTrans t1) => MonadTrans (MCompT t1 SFKT) where 
   lift m = MCompT (lift (lift m))
-- instance (MonadTrans t1, MonadTrans t2) => MonadTrans (MCompT t1 t2) 
----------------------------------------

forEach = flip map
lift2 x = lift (lift  x)
lift3 x = lift (lift2 x)
mtry f x = f x `mplus` x

atLeast _ []   = False
atLeast 0 _    = True
atLeast n list = atLeast (n-1) (tail list)

_      >=: []     = True
(x:xx) >=: (y:yy) = xx >=: yy
_      >=: _      = False

propLEQCons xx yy = (length xx >= length yy) == xx >=: yy
    where types = (xx::[Int], yy::[Int])

runIdentityT = runErrorT_

runIdentityT, runErrorT_ :: (Functor m) => ErrorT [Char] m a -> m a
runErrorT_ =  fmap noErrors . runErrorT
noErrors (Left msg) = error msg
noErrors (Right x)  = x

handleError :: MonadError e m =>  (e -> m a) -> m a -> m a
handleError = flip catchError

trace msg x = 
#ifdef DEBUG 
  Debug.Trace.trace msg x 
#else 
  x 
#endif

instance (Monad m, Error e) => MonadError e (SFKT m) where
    throwError _ = mzero
    catchError m f = LogicT.ifte m return (f undefined)

{-# INLINE msum' #-}
msum' :: (LogicT.LogicT t, MonadPlus (t m), Monad m) => [t m a] -> t m a
msum' = Prelude.foldr LogicT.interleave mzero

(>>-) :: (Monad m, MonadPlus (t m), LogicT.LogicT t) =>
	    t m a -> (a -> t m b) -> t m b
(>>-) = LogicT.bindi