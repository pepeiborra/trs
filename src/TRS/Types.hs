{-# OPTIONS_GHC -fglasgow-exts -fallow-undecidable-instances #-}
{-# OPTIONS_GHC -fallow-overlapping-instances #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  TRS.Types
-- Copyright   :  (c) Pepe Iborra 2006-2007
--                (c) Universidad Politécnica de Valencia 2006-2007
-- License     :  BSD-style (see LICENSE)
--
-- Maintainer  :  pepeiborra@gmail.org
-- Stability   :  experimental
-- Portability :  portable
--
-- Home for all types and helpers. Internal
-----------------------------------------------------------------------------

module TRS.Types ( ST, runST, stToIO, RealWorld
		 , STRef, newSTRef, readSTRef, writeSTRef
		 , module TRS.Types) where

import TRS.Utils
import Control.Applicative
import Control.Arrow
import Data.Foldable as Foldable
import Data.Maybe
import Data.Monoid
import Data.Traversable as Traversable
import Control.Monad       hiding (msum, mapM)
import Control.Monad.Error (MonadError, Error(..))
import Control.Monad.Fix
import Control.Monad.Trans
import Control.Monad.State (gets, modify, evalState)
import Control.Monad.ST
import qualified Control.Monad.ST as ST
import Data.STRef
import System.Mem.StableName
import System.IO.Unsafe
import Test.QuickCheck hiding (collect)
import Prelude hiding ( all, maximum, minimum, any, mapM_,mapM, foldr, foldl
                      , and, concat, concatMap, sequence, elem, notElem)

import GHC.Exts

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
 | MutVar (STRef r (Maybe (GT_ eq r s)))  -- | A Mutable variable
 | GenVar Int                             -- | A type scheme, univ. quantified variable 
 | CtxVar Int                             -- | For internal use

#else
data GT_ (eq :: *)  (r :: *) (s :: * -> *) = 
   S (s(GT_ eq r s))
 | MutVar (STRef r (Maybe (GT_ eq r s)))
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

type Ptr_ eq r s = STRef r (Maybe (GT_ eq r s))
type Ptr r s     = STRef r (Maybe (GT r s))
type GTm m r s   = m (ST r) (GT r s)

-- ** MutVars
fresh	  :: ST r (GT_ eq r s)
readVar   :: STRef s a -> ST s a
write     :: STRef s a -> a -> ST s ()
isEmptyVar:: GT_ eq r s -> ST r (Bool)

fresh     = newSTRef Nothing >>= return . MutVar
readVar r = readSTRef r
write r x = writeSTRef r x
isEmptyVar (MutVar r) = liftM isNothing (readVar r)

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

-- -------------------------------------------
-- * Static Terms
-- --------------------------------------------
-- | The datatype of static terms, terms with no mutable vars
--   A generic term is converted to a static term with @zonkTerm@
--   and the other way around with @instTerm@
data TermStatic_ i s = Term (s (TermStatic_ i s)) | Var i
--  deriving (Show)
type TermStatic s = TermStatic_ Int s

s :: s(TermStatic s) -> TermStatic s
s      = Term

-- --------------------------
-- * Basic Shape of Terms
-- --------------------------

data BasicShape a = T !String [a]
    deriving Eq

type TermST r = GTE r BasicShape
type Term = TermStatic BasicShape

type RewRule = Rule BasicShape


---------------------------------------------------------
-- Instantiation of BasicShape classes
---------------------------------------------------------

instance Traversable BasicShape where
    traverse f (T s tt) = T s <$> traverse f tt
instance Functor BasicShape where
    fmap = fmapDefault
instance Foldable BasicShape where
    foldMap = foldMapDefault

instance TermShape BasicShape where
  matchTerm (T s1 tt1) (T s2 tt2) = if s1==s2 && length tt1 == length tt2
              then Just (zip tt1 tt2)
              else Nothing

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


-----------------------------
-- * The Class of Match-ables
-----------------------------
class (Traversable s) => TermShape s where
    matchTerm     :: s x -> s x -> Maybe [(x,x)]

-- | Match two static terms
--   1st arg is the template
matchStatic (Term x) (Term y) 
  | Nothing <- matchTerm x y = Nothing
  | Just pairs <- matchTerm x y
  = concatMapM (uncurry matchStatic) pairs
matchStatic (Var v) (Term y) = return [(v,y)]
matchStatic _ _ = Nothing
----------------------
-- * Substitutions
----------------------
newtype SubstG a = Subst {subst::[a]}
   deriving (Foldable, Functor, Traversable)
--newtype Subst r s = Subst {subst::[GT r s]}

type Subst r s     = SubstG (GT r s)
type Subst_ eq r s = SubstG (GT_ eq r s)
type SubstM x      = SubstG (Maybe x)

--emptyS = Subst [GenVar n | n <- [0..]]
emptyS = Subst mempty

-----------------------
-- * Exceptions
-----------------------
data TRSException = Match (MatchException)
                  | Unify (UnifyException)
                  | Stuck
  deriving (Show,Eq)
data MatchException = GenErrorMatch
                    | ShapeErrorMatch
  deriving (Show,Eq)
#ifdef __HADDOCK__
data UnifyException = 
    GenErrorUnify   |
    ShapeErrorUnify |
    OccursError     
#else
data UnifyException where 
    GenErrorUnify   :: UnifyException
    ShapeErrorUnify :: Show a => a -> a -> UnifyException
    OccursError     :: UnifyException
#endif
instance Show UnifyException where
  show GenErrorUnify = "Unification: general error"
  show OccursError   = "Unification: occurs  error"
  show (ShapeErrorUnify x y) = "Can't unify " ++ show x ++ " and " ++ show y

instance Eq UnifyException where
  GenErrorUnify == GenErrorUnify = True
  OccursError   == OccursError   = True
  ShapeErrorUnify _ _ == ShapeErrorUnify _ _ = True
  _ ==  _ = False

instance Error TRSException where
  noMsg    = Match GenErrorMatch
  strMsg _ = Match GenErrorMatch

genErrorMatch   = Match GenErrorMatch
shapeErrorMatch = Match ShapeErrorMatch

genErrorUnify   = Unify GenErrorUnify
shapeErrorUnify :: Show a => a -> a -> TRSException
shapeErrorUnify = (Unify.) . ShapeErrorUnify
occursError     = Unify OccursError

--------------------------------
-- Other Instances and base operators
--------------------------------

liftSubst f (Subst s) = Subst (f s)

varNames = "XYZWJIKHW"
showsVar p n = if n < length varNames 
                         then ([varNames !! n] ++)
                         else ('v' :) . showsPrec p n

instance (Show (s (TermStatic s))) => Show (TermStatic s) where
    showsPrec p (Term s) = showsPrec p s
    showsPrec p (Var  i) = showsVar p i 

instance (Show (s (GT_ eq r s))) => Show (GT_ eq r s) where
    show (S s)      = show s
    show (GenVar n) = showsVar 0 n "" --TODO 
    show (CtxVar c) = '[' : show c ++ "]" 
    show (MutVar r) = "?" ++ (show . hashStableName . unsafePerformIO . makeStableName$ r) 
                          ++ ":=" ++ (show$  unsafeAll $ ( readSTRef r))
--        where unsafeAll = unsafePerformIO . ST.unsafeSTToIO . lazyToStrictST
        where unsafeAll = unsafePerformIO . ST.unsafeSTToIO 

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

instance Show (s(GT r s)) => Show (Subst r s) where
    show = show . subst

instance Show (a) => Show (RuleG (a)) where
    show (a:->b) = show a ++ " -> " ++ show b
--    showList  = unlines . map show
{-
instance Show(GTE r s) => Show(GT r s) where
    show = show . eqGT  

instance (Functor s, Show(s(GTE r s))) => Show(s(GT r s)) where
    show = show . fmap eqGT 
-}
--instance Arbitrary(GTE r s) => Arbitrary(GT r s) where
--    arbitrary = fmap idGT arbitrary 

----------
-- * Rules
----------
type Rule s  = RuleG (TermStatic s)
type RuleI r s = RuleG (GT r s)
data RuleG a = a :-> a

instance (Eq (RuleG a),Ord a) => Ord (RuleG a) where
  compare (l1 :-> r1) (l2 :-> r2) = case compare l1 l2 of
                                      EQ -> compare r1 r2
                                      x  -> x

instance Traversable RuleG where
  traverse f (l :-> r) = (:->) <$> f l <*> f r

instance Foldable RuleG where
  foldMap = foldMapDefault

instance Functor RuleG where
  fmap = fmapDefault

--swap :: Rule r s -> Rule r s
swap (lhs:->rhs) = rhs:->lhs

