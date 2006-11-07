{-# OPTIONS_GHC -cpp -fglasgow-exts -fallow-undecidable-instances -fallow-overlapping-instances #-}
-----------------------------------------------------------------------------------------
{-| Module      : TRS.Utils
    Copyright   : 
    License     : All Rights Reserved

    Maintainer  : 
    Stability   : 
    Portability : 
-}
-----------------------------------------------------------------------------------------

module TRS.Utils where
import Control.Applicative
import Control.Monad.State hiding (mapM, sequence)
import Control.Monad.List (ListT(..))
import Control.Monad.Error (catchError, Error, ErrorT, MonadError)
import Data.Traversable
import Data.Foldable
import Prelude hiding ( all, maximum, minimum, any, mapM_,mapM, foldr, foldl, concat
                      , sequence, and )

import qualified Debug.Trace


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
fmap2 f x = fmap (fmap f) x
fmap3 f x = fmap (fmap (fmap f)) x 

successes :: (MonadPlus m, Functor m) => [m a] -> m [a]
successes cc = fmap concat $ sequence $ map (\c->fmap unit c `mplus` return []) cc
    where unit x = [x]

-- Awesome. Data.Traversable is incredible!
parallelComb :: Traversable t => t [a] -> [t a]
parallelComb = sequenceA

interleave :: (MonadPlus m, Traversable t) =>
                 (a -> m b) -> (a -> m b) -> t a -> [m (t b)]
interleave f g x = let
        indexed_fs = map (indexed f g) [0..size x - 1] 
        indexed f default_f i (j,x) = if i==j then f x else default_f x
     in map (\f->mapM f (unsafeZipG [0..] x)) indexed_fs


{-
   Creo que había entendido mal lo que pone abajo
   En realidad debería ocurrir lo siguiente:
      - Narrowing en una variable: fail
      - Intento de Narrowing y fallo de unificación: fail
      - SI NO HAY REGLAS: fail siempre (inductivamente se ve)
-} 

{-
-- Exigencias del guión.
-- Queremos que fixM narrowing (t): 
--  1. Declare success si t es una variable
--  2. Declare failure si t es un término que no unifica con ninguna regla
--   2.1 Incluido el caso de que NO HAYA REGLAS.
--
   Por lo tanto, si el conjunto de reglas es el conjunto vacío:
        narrowing V : success
        narrowing t : failure
        fixNarrowing V : success
        fixNarrowing t : failure

Pero tal y como está declarado fixM, nunca se produce un mzero (i.e. un fail)!

-}

tryList :: a -> [a] -> [a]
tryList a [] = [a]
tryList _ x  =  x

tryListT :: Monad m => a -> ListT m a -> ListT m a
tryListT a (ListT m) = ListT$ do 
  v <- m
  case v of 
    [] -> return [a]
    x  -> return x
{-
Ejemplo en el que la funcion f en (tryList f) es recursiva:

f0 x = [ y | x' <- g x, y <- f0 x'] ++ [ f0 y | y <- h x]

f = tryList f0

Problema: 
f x -expand f-> tryList f0 x -

-}

class MonadTry m where
 try :: (a -> m a) -> a -> m a

instance MonadTry [] where
 try f a | null (f a) = [a]
         | otherwise  = f a

instance Monad m => MonadTry (ListT m) where
 try m a = let ListT m1 = m a in  
           ListT$ (m1 >>= \v -> return (if null v then [a] else v))

instance MonadTry m => MonadTry (StateT s m) where
 try m a = let StateT v = m a in
            StateT$ \s -> try (\(a,s) -> v s) (a,s)

instance MonadError e m => MonadTry m  where
 try m a = m a `catchError` \_->return a

forEach = flip map
lift2 x = lift$ lift x
mtry f x = f x `mplus` x

atLeast _ []   = False
atLeast 0 _    = True
atLeast n list = atLeast (n-1) (tail list)

-- #define DEBUG
trace msg x = 
#ifdef DEBUG 
  Debug.Trace.trace msg x 
#else 
  x 
#endif