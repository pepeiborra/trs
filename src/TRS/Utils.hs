{-# OPTIONS_GHC -cpp -fglasgow-exts #-}
{-# OPTIONS_GHC -fallow-undecidable-instances #-}
{-# OPTIONS_GHC -fignore-breakpoints #-}
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
import Control.Monad.State hiding (mapM, sequence, msum)
import Control.Monad.List (ListT(..))
import Control.Monad.Error (throwError, catchError, Error, ErrorT(..), MonadError)
import Data.AlaCarte
import Data.List (group, sort, sortBy, groupBy, intersperse)
import Data.Maybe
import Data.Traversable
import Data.Foldable
import qualified Prelude
import Prelude hiding ( all, any, maximum, minimum, any, mapM_,mapM, foldr, foldl, concat
                      , sequence, and, or, elem, concatMap )

import Control.Exception

#if __GLASGOW_HASKELL__ < 607 
infixr 1 <=<
f <=< g = \x -> g x >>= f
#endif

isList :: [a] -> [a]
isList = id
isMaybe :: Maybe a -> Maybe a
isMaybe = id

const2 :: a -> b -> b1 -> a
const2 = const . const


showsVar :: (Integral a) => Int -> a -> [Char] -> [Char]
showsVar p n = if fromIntegral n < length varNames
                         then ([varNames !! fromIntegral n] ++)
                         else ('v' :) . showsPrec p n
    where varNames = "XYZWJIKHW"

brackets, parens, hash :: String -> String
brackets = ('[' :) . (++ "]")
parens   = ('(' :) . (++ ")")
hash     = ('#' :) . (++ "#")


punct :: [a] -> [[a]] -> [a]
punct p = concat . intersperse p

{- |
 A function inspired by the perl function split. A list is splitted
 on a seperator element in smaller non-empty lists.
 The seperator element is dropped from the resulting list.
-}
splitOn :: Eq a => a -- ^ seperator
       -> [a] -- ^ list to split
       -> [[a]]
splitOn x xs = let (l, r) = break (==x) xs in
   (if null l then [] else [l]) ++ (if null r then [] else splitOn x $
                                       tail r)

---------------------------------------------------------
snub :: Ord a => [a] -> [a]
snub = map head . group . sort

snubBy :: (a -> a -> Ordering) -> [a] -> [a]
snubBy f = map head . groupBy (((==EQ).) . f) . sortBy f

on, at :: (a -> a -> b) -> (t -> a) -> (t -> t -> b)
g `at` f = \x y -> g (f x) (f y)
on = at


inBounds1 :: (Ord t1, Num t1) => t1 -> [t] -> Bool
inBounds1 _ [] = False
inBounds1 0 _  = True
inBounds1 i (_:xs) = inBounds1 (i-1) xs

inBounds :: Int -> [a] -> Bool
inBounds i _ | i < 0 = False
inBounds i xx = length (take (i+1) xx) == i+1

propInBounds :: Int -> [()] -> Bool
propInBounds i xx = inBounds i xx == inBounds1 i xx

isSubsetOf :: (Eq a, Foldable f) => f a -> f a -> Bool
x `isSubsetOf` y = all (`elem` y) x

firstM :: (Monad m) => (t -> m a) -> (t, t1) -> m (a, t1)
firstM  f (a, b) = f a >>= \a' -> return (a', b)
secondM :: (Monad m) => (t1 -> m a) -> (t, t1) -> m (t, a)
secondM f (a, b) = f b >>= \b' -> return (a, b')

biM :: Monad m =>  (a -> m b) -> (c -> m d) -> (a,c) -> m (b, d)
biM f g = firstM f >=> secondM g

swap :: (a,b) -> (b,a)
swap(x,y) = (y,x)
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


nubByM :: (Functor m, Monad m) => (a -> a -> m Bool) -> [a] -> m [a]
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
-- |A fixpoint-like monadic operation. Currenty a bit ugly, maybe there is a 
--- better way to do this 'circularly'
closureMP :: MonadPlus m => (a -> m a) -> (a -> m a)
closureMP f x = (f x >>= closureMP f) `mplus` return x

class MonadPlus m => MonadPlus1 m where isMZero :: m a -> Bool
instance MonadPlus1 []            where isMZero = null
instance MonadPlus1 Maybe         where isMZero = isNothing

fixMP :: (MonadPlus1 m) => (a -> m a) -> (a -> m a)
fixMP f x = let x' = f x in if isMZero x' then return x else fixMP f =<< x' -- msum (fixMP f `liftM` x')

-- Fixpoint of a monadic function, using Eq comparison (this is a memory eater)
fixM_Eq :: (Monad m, Eq a) => (a -> m a) -> a -> m a
fixM_Eq f = go (0::Int)  where 
  go i prev_result = trace ("Iteration " ++ show i) $ do 
    x <- f prev_result
    if x == prev_result then return x
                        else go (i+1) x 

-- Fixpoint of a regular function, using Eq comparison (bad, memory eater!)
fixEq :: Eq a => (a -> a) -> a -> a
fixEq f x = case f x of y | y == x    -> y
                          | otherwise -> fixEq f y

iterateMn :: Monad m => Int -> (a -> m a) -> a -> m a
iterateMn 0 _ x = return x
iterateMn n f x = f x >>= iterateMn (n-1) f 

iterateM :: (Monad m) => (a -> m a) -> a -> m [a]
iterateM f x = let iM f x = x : iM f (x >>= f) in
               sequence $ iM f $ return x

concatMapM :: (Monad m, Functor m, Traversable t) => (a1 -> m [a]) -> t a1 -> m [a]
concatMapM f = fmap concat . mapM f

assertM :: (Monad m) => m Bool -> m b -> m b
assertM acc cont = acc >>= \cond -> assert cond cont

-- |All the pairs of element + rest of the list
selections :: [a] -> [(a,[a])]
selections []     = []
selections (x:xs) = (x,xs) : [ (y,x:ys) | (y,ys) <- selections xs ]

andM :: (Traversable t, Monad m) => t(m Bool) -> m Bool
andM = liftM and . sequence
 
allM :: (Traversable t, Monad m) => (a -> m Bool) -> t a -> m Bool
allM = (liftM and .) . mapM

anyM :: (Traversable t, Monad m) => (a -> m Bool) -> t a -> m Bool
anyM = (liftM or .) . mapM

class Unpack p u | p -> u where
    unpack :: p -> u

ily ::(Unpack b u) => (b1 -> c) -> ((a -> c) -> a1 -> b) -> (a -> b1) -> a1 -> u
ily pack transform f = unpack . transform (pack . f)

unsafeZipG :: (Traversable t1, Traversable t2) => t1 a -> t2 b -> t2 (a,b)
unsafeZipG t1 t2  = evalState (mapM zipG' t2) (toList t1)
       where zipG' y = do (x:xx) <- get
                          put xx
                          return (x,y)

unsafeZipWithG :: (Traversable t1, Traversable t2) => 
                 (a -> b -> c) -> t1 a -> t2 b -> t2 c
unsafeZipWithG f t1 t2 = fmap (uncurry f) (unsafeZipG t1 t2)

zipG :: (Traversable t) => t a -> t a -> t (a, a)
zipG t1 t2= either id id $ zipG' t1 t2

zipG' :: (Traversable t, Traversable t1) =>
        t1 a1 -> t a -> Either (t (a1, a)) (t1 (a, a1))
zipG' t1 t2 
    | toList t2 >=: toList t1 = Left$ evalState (mapM zipG' t2) (toList t1)
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
unzipG3 t = let fstz = fmap (\(a,_,_)->a) t
                sndz = fmap (\(_,b,_)->b) t
                trdz = fmap (\(_,_,c)->c) t
            in (fstz,sndz,trdz)

mapMState :: (Traversable t, Monad m) => (a -> s -> m (b,s)) -> s -> t a -> m (t b, s)
mapMState f s0 x = flip runStateT s0 (mapM f' x)
    where f' y = do s      <- get
                    (v,s') <- lift$ f y s
                    put s'
                    return v

size :: Foldable t => t a -> Int
size = length . toList

modifySpine      :: Traversable t => t a -> [b] -> t b
modifySpine t xx = assert (xx >=: toList t) $  mapM (\_-> pop) t `evalState` xx
  where pop = gets head >>= \v -> modify tail >> return v

-- Only 1st level children
someSubterm :: Traversable t => (a -> a) -> t a -> [t a]
someSubterm f x = interleave f id x


-- Only 1st level children
someSubtermM :: (Traversable t, MonadPlus m) => (a -> m a) -> t a -> m (t a)
someSubtermM f x = msum$ interleaveM f return x

-- | Like someSubterm, but works on all the subterms not only the 1st level
-- > someSubTerm f t = [(t'1,old1), (t'2, old2) ...]
someSubtermDeep :: forall f m. (Functor f, Foldable f, MonadPlus m) =>  (Expr f -> Expr f) -> Expr f -> m(Expr f, Expr f)
someSubtermDeep f = foldExpr' g where
    g :: Foldable f => Expr f -> f (m(Expr f, Expr f)) -> m(Expr f, Expr f)
    g t_old t = return (f t_old, t_old) `mplus` msum t


successes :: (MonadPlus m, Functor m) => [m a] -> m [a]
successes cc = fmap concat $ sequence $ map (\c->fmap unit c `mplus` return []) cc
    where unit x = [x]

interleave :: (Traversable f) => (a ->b) -> (a -> b) -> f a -> [f b]
interleave f g x = let
        indexed_fs = map (indexed f g) [0..size x - 1] 
        indexed f default_f i (j,x) = if i==j then f x else default_f x
     in map (\f->fmap f (unsafeZipG [0..] x)) indexed_fs

-- Awesome. Data.Traversable is incredible!
interleaveM :: (MonadPlus m, Traversable t) =>
                 (a -> m b) -> (a -> m b) -> t a -> [m (t b)]
interleaveM f g x = let
        indexed_fs = map (indexed f g) [0..size x - 1] 
        indexed f default_f i (j,x) = if i==j then f x else default_f x
     in map (\f->mapM f (unsafeZipG [0..] x)) indexed_fs


-- Awesome. Data.Traversable is incredible!
interleaveM' :: (MonadPlus m, Traversable t) => (a -> m a) -> (a -> m a) -> t a -> [m (t a, a)]
interleaveM' f g x = let
        indexed_fs = map (indexed f g) [0..size x - 1]
        indexed f default_f i (j,x) = if i==j
                                         then (put x >> lift (f x))
                                         else (lift $ default_f x)
     in map (`runStateT` undefined) (map (\f->mapM f (unsafeZipG [0..] x)) indexed_fs)


#if __GLASGOW_HASKELL__ < 607
f >=> g = \ x -> f x >>= g
#endif
----------------------------------------------------------
-- A monad isomorphic to ListT 
-- Only the monadError instance is different
----------------------------------------------------------
newtype ListT' m a = ListT_ {runListT_ :: ListT m a}
  deriving (Monad, MonadPlus, MonadIO, MonadTrans, Functor)

listT' :: m [a] -> ListT' m a
listT'    = ListT_ . ListT 
runListT' :: ListT' m a -> m [a]
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

try1 :: (Monad m) => (a -> ListT m a) -> a -> ListT m a
try1 m a = let ListT m1 = m a in  
           ListT$ (m1 >>= \v -> return (if null v then [a] else v))
----------------------------------------------------------
-- A monad isomorphic to ErrorT 
-- Only the monadPlus instance is different
----------------------------------------------------------
newtype ErrorT' e m a = ErrorT_ {unErrorT :: ErrorT e m a}
  deriving (Monad, MonadError e, MonadIO, MonadTrans, MonadFix, Functor)

runErrorT' :: ErrorT' e m a -> m (Either e a)
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
--instance (MonadTrans t1) => MonadTrans (MCompT t1 SFKT) where 
--   lift m = MCompT (lift (lift m))
-- instance (MonadTrans t1, MonadTrans t2) => MonadTrans (MCompT t1 t2) 
----------------------------------------


forEach :: [a] -> (a -> b) -> [b]
forEach = flip map

return2 :: (Monad m, Monad n) => a -> m(n a)
return2 = return . return

fmap2 :: (Functor f1, Functor f) => (a -> b) -> f1 (f a) -> f1 (f b)
fmap2 f x = fmap (fmap  f) x
fmap3 :: (Functor f2, Functor f1, Functor f) => 
         (a -> b) -> f2 (f (f1 a)) -> f2 (f (f1 b))
fmap3 f x = fmap (fmap2 f) x 

($>) :: (Functor f) => f a -> (a -> b) -> f b
($>) = flip (<$>)

(<$$>) :: (Functor f1, Functor f) => (a -> b) -> f1 (f a) -> f1 (f b)
f <$$> x = fmap (fmap  f) x

(<$$$>) :: (Functor f2, Functor f1, Functor f) => 
         (a -> b) -> f2 (f (f1 a)) -> f2 (f (f1 b))
f <$$$> x = fmap (fmap2 f) x 

mapM2 :: (Traversable t1, Traversable t, Monad m) =>
        (a -> m b) -> t1 (t a) -> m (t1 (t b))
mapM2 f = mapM (mapM f)
liftMM :: (Monad m, Monad n) => (a -> b) -> m(n a) -> m(n b)
liftMM = liftM . liftM
concat2 :: (Foldable t, Foldable u, Functor t) => t (u [a]) -> [a]
concat2 = concat . fmap concat
toList2 :: (Foldable t1, Foldable t) => t1 (t a) -> [[a]]
toList2 = map toList . toList
concatMap2 :: (Foldable g, Foldable f) => (a1 -> [a]) -> f (g a1) -> [a]
concatMap2 = concatMap . concatMap
sequence2 :: (Traversable t, Traversable f, Monad m) => f (t (m a)) -> m (f (t a))
sequence2 = sequence . fmap sequence
sequence3 :: (Traversable f, Traversable t, Traversable f1, Monad m) =>
            f1 (f (t (m a))) -> m (f1 (f (t a)))
sequence3 = sequence . fmap sequence2

lift2 :: (Monad (t m), MonadTrans t1, Monad m, MonadTrans t) => m a -> t1 (t m) a
lift2 x = lift (lift  x)
lift3 ::
  (Monad (t1 (t m)),
   MonadTrans t11,
   MonadTrans t,
   Monad m,
   MonadTrans t1,
   Monad (t m)) =>
  m a -> t11 (t1 (t m)) a
lift3 x = lift (lift2 x)

mtry :: (MonadPlus m) => (m a -> m a) -> m a -> m a
mtry f x = f x `mplus` x

atLeast :: (Num t1) => t1 -> [t] -> Bool
atLeast _ []   = False
atLeast 0 _    = True
atLeast n list = atLeast (n-1) (tail list)

(>=:) :: [a] -> [b] -> Bool
_      >=: []     = True
(_:xx) >=: (_:yy) = xx >=: yy
_      >=: _      = False

propLEQCons :: [Int] -> [Int] -> Bool
propLEQCons xx yy = (length xx >= length yy) == xx >=: yy
    where types = (xx::[Int], yy::[Int])

runIdentityT = runErrorT_

runIdentityT, runErrorT_ :: (Functor m) => ErrorT [Char] m a -> m a
runErrorT_ =  fmap noErrors . runErrorT

noErrors :: Either [Char] t -> t
noErrors (Left msg) = error msg
noErrors (Right x)  = x

handleError :: MonadError e m =>  (e -> m a) -> m a -> m a
handleError = flip catchError


trace :: t -> t1 -> t1
trace msg x = 
#ifdef DEBUGTRS
  Debug.Trace.trace msg x 
#else 
  x 
#endif

--instance (Monad m, Error e) => MonadError e (SFKT m) where
--    throwError _ = mzero
--    catchError m f = LogicT.ifte m return (f undefined)

--{-# INLINE msum' #-}
--msum' :: (LogicT.LogicT t, MonadPlus (t m), Monad m) => [t m a] -> t m a
--msum' = Prelude.foldr LogicT.interleave mzero

--(>>-) :: (Monad m, MonadPlus (t m), LogicT.LogicT t) =>
--	    t m a -> (a -> t m b) -> t m b
--(>>-) = LogicT.bindi

