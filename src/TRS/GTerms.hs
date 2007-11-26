{-# OPTIONS_GHC -fglasgow-exts #-}
{-# OPTIONS_GHC -fallow-overlapping-instances #-}
{-# OPTIONS_GHC -fallow-undecidable-instances #-}
{-# OPTIONS_GHC -cpp #-}
module TRS.GTerms where

import Control.Monad
import Control.Monad.ST as ST
import Control.Arrow
import Data.Foldable as Foldable
import Data.Traversable as Traversable
import qualified Data.IntMap as IntMap
import Data.Monoid
import Data.Traversable
import Data.Foldable
import Prelude hiding ( all, maximum, minimum, any, mapM_,mapM, foldr, foldl
                      , and, concat, concatMap, sequence, elem, notElem)
import System.Mem.StableName
import System.IO.Unsafe
import GHC.Exts (unsafeCoerce#)

import TRS.Substitutions
import TRS.Types
import TRS.Utils
import TRS.Tyvars
import TRS.Term

type TermST r = GTE r BasicShape
type Ptr mode r s = Ptr_ r (GT_ mode r s)

-- * Generic Terms
{- | 
     The datatype of 'Generic Terms', where the type variables have the following meaning:
   eq: This is a phantom variable used to switch between syntactic and semantic equality (I could have done the same with a separate newtype wrapper)
   s:  This is a type constructor for the structure of terms (See Terms.hs for an example)
   r:  This is the ST monad thread token
-}

#ifdef __HADDOCK__
data GT_ mode r s = 
   S (s(GT_ mode r s))
 | MutVar (Ptr mode r s)  -- | A Mutable variable
 | GenVar Int                             -- | A type scheme, univ. quantified variable 
 | CtxVar Int                             -- | For internal use

#else
data GT_ (mode :: *)  (r :: *) (s :: * -> *) = 
   S (s(GT_ mode r s))
 | MutVar (Ptr mode r s)
 | GenVar Int
 | CtxVar Int
#endif
-- 'Witness' types for equality. The actual Eq instances for GT_ are not 
--  defined here, but in the Core module
data Syntactic  -- denotes pure syntactic equality
data Semantic   -- denotes syntactic equality modulo variables
data Basic      -- denotes a Basic Narrowing derivation

type GT r s  = GT_ Syntactic r s
type GTE r s = GT_ Semantic r s

genVar :: Int -> GTE r s
genVar = GenVar

mutVar :: Int -> ST r (GT_ mode r s)
mutVar = fmap MutVar . newVar

fresh :: ST r (GT_ mode r s)
fresh = fmap MutVar skolem

-- This pair of functions provides the bridge between GT_ Syntactic and GT_ Semantic types of terms
-- I really should have used a wrapper newtype for this instead of the 
--  phantom variable trick. 
idGT :: GT_ mode r s -> GT r s
idGT = unsafeCoerce#

eqGT :: GT_ mode r s -> GTE r s
eqGT = unsafeCoerce#

basicGT :: GT_ mode r s -> GT_ Basic r s
basicGT = unsafeCoerce#

freeGT :: GT_ mode r s -> GT_ mode2 r s
freeGT = unsafeCoerce#

isGT :: GT r s -> GT r s
isGT x = x

-- ** Accesors
isGenVar, isMutVar, isCtxVar, isTerm :: GT_ eq r s -> Bool
isGenVar GenVar{} = True
isGenVar _ = False
isMutVar MutVar{} = True
isMutVar _ = False
isCtxVar CtxVar{} = True
isCtxVar _ = False
isTerm S{} = True
isTerm _   = False 

-- --------------------
-- GT Term structure
-- --------------------
instance (TermShape s, Foldable s) => Term (GT_ eq r) s where
  {-# SPECIALIZE instance Term (GT_ eq r) BasicShape #-}
  isVar S{}      = False
  isVar _        = True
  mkVar          = GenVar
  varId (GenVar i) = Just i
  varId (CtxVar i) = Just i
  varId (MutVar i) = Nothing -- error "unexpected mutvar"
  subTerms (S x) = toList x
  subTerms _     = []
  synEq (MutVar r1) (MutVar r2) = r1 == r2 
  synEq (GenVar n) (GenVar m)   = m==n
  synEq (CtxVar n) (CtxVar m)   = m==n
  synEq (S x) (S y) | Just pairs <- matchTerm x y 
                    = all (uncurry synEq) pairs 
  synEq _ _         = False
  fromSubTerms (S t) tt = S $ modifySpine t tt
  fromSubTerms t _      = t
  fromGTM _      = return . unsafeCoerce#
  mkGTM _        = return . unsafeCoerce#

---------------------------------------------
-- * Positions. Indexing over subterms.
---------------------------------------------
type Position = [Int]
subtermAt :: (Functor m, MonadPlus m, Traversable s) => GT_ eq r s -> Position -> m (GT_ eq r s)
subtermAt t (0:_) = return t
subtermAt (S t) (i:is) = join . fmap (flip subtermAt is . snd) 
                       . maybe mzero return 
                       . find ((== i) . fst) 
                       . unsafeZipG [1..] 
                       $ t
subtermAt x [] = return x
subtermAt _ _ = mzero

-- | Updates the subterm at the position given 
--   Note that this function does not guarantee success. A failure to substitute anything
--   results in the input term being returned untouched
updateAt  :: (Traversable s) => GT_ eq r s -> Position -> GT_ eq r s -> GT_ eq r s
updateAt _ (0:_) st' = st'
updateAt (S t) (i:is) st' = S . fmap (\(j,st) -> if i==j then updateAt st is st' else st) 
                          . unsafeZipG [1..] 
                          $ t
updateAt _ [] x' = x'
updateAt x _ _ = x


-- | Like updateAt, but returns a tuple with the new term, and the previous subterm at position pos
updateAt'  :: (Functor m, MonadPlus m, Traversable s) => 
             GT_ eq r s -> Position -> GT_ eq r s -> m (GT_ eq r s, GT_ eq r s)
updateAt' x pos x' = go x pos x' >>= \ (t',a) -> a >>= \v->return (t',v)
  where
    go x (0:_) x'       = return (x', return x)
    go (S t) (i:is) st' = fmap (first S . second Foldable.msum . unzipG)
                        . Traversable.sequence
                        . fmap (\(j,u)->if i==j
                                       then go u is st'
                                       else return (u, mzero))
                        . unsafeZipG [1..]
                        $ t
    go x [] x' = return (x', return x)
    go x _ _   = mzero
{-
type STV r a = STRef r (IntMap.IntMap Unique (GT_ mode r s)) -> ST r a
instance VarMonad (STV r) (GT_ mode r s) where
  getVar u table_ref = do
      table <- readSTRef table_ref
      mb_var <- IntMap.lookup u table
      case mb_var of
        Just var -> return var
        Nothing  -> do
          let var    = Empty u
              table' = IntMap.insert u (Empty u) table
          write table_ref table'
          return var
-}
instance (Show (s (GT_ eq r s))) => Show (GT_ eq r s) where
    show (S s)      = show s
    show (GenVar n) = showsVar 0 n "" --TODO 
    show (CtxVar c) = '[' : show c ++ "]" 
    show (MutVar r) = "?" ++ (show . hashStableName . unsafePerformIO . makeStableName$ r) 
                          ++ ":=" ++ (show$  unsafeAll $ ( readSTRef r))
--        where unsafeAll = unsafePerformIO . ST.unsafeSTToIO . lazyToStrictST
        where unsafeAll = unsafePerformIO . ST.unsafeSTToIO 
{-
instance Show (s(GTE r s)) => Show (SubstG (GTE r s)) where
    show = show . subst
-}
-- Oops. Does this instance of Ord honor Semantic equality?
--instance (Eq(GTE r s), TermShape s, Ord (s (GTE r s))) => Ord (GTE r s) where
instance (Eq(GT r s), TermShape s, Ord (s (GT r s))) => Ord (GT r s) where
    compare (S t1) (S t2)
     | S t1 == S t2 = EQ
     | otherwise    = compare t1 t2
    compare S{} _ = GT
    compare _ S{} = LT
    compare MutVar{} MutVar{} = EQ
    compare (GenVar m) (GenVar n) = compare m n
    compare GenVar{} MutVar{} = GT
    compare MutVar{} GenVar{} = LT
    compare _ CtxVar{} = GT
    compare CtxVar{} _ = LT

