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
import Data.Foldable
import Data.Maybe
import Data.Monoid
import Data.Traversable
import Control.Monad
import Control.Monad.Error
import Control.Monad.Fix
import Control.Monad.Trans
import Control.Monad.ST
import qualified Control.Monad.ST as ST
import Data.STRef
import System.Mem.StableName
import System.IO.Unsafe
import Test.QuickCheck
import Prelude hiding ( all, maximum, minimum, any, mapM_,mapM, foldr, foldl
                      , and, concat, concatMap, sequence, elem, notElem)

import GHC.Exts

{-
The datatype of 'Generic Terms', where the type variables have the following meaning:
   eq: This is a phantom variable used to switch between syntactic and semantic equality (I could have done the same with a separate newtype wrapper)
   s:  This is a type constructor for the structure of terms (See Terms.hs for an example)
   r:  This is the ST monad thread token
-}

data GT_ (eq :: *) (s :: * -> *) (r :: *) = 
   S (s(GT_ eq s r))
 | MutVar (STRef r (Maybe (GT_ eq s r)))
 | GenVar Int
 | CtxVar Int

-- 'Witness' types for equality. The actual Eq instances for GT_ are not 
--  defined here, but in the Core module
data Syntactic  -- denotes pure syntactic equality
data Semantic   -- denotes syntactic equality modulo variables

type GT s r  = GT_ Syntactic s r
type GTE s r = GT_ Semantic s r

s :: s(GTE s r) -> GTE s r
s      = S
genVar :: Int -> GTE s r
genVar = GenVar

-- This pair of functions provides the bridge between GT_ Syntactic and GT_ Semantic types of terms
-- I really should have used a wrapper newtype for this instead of the 
--  phantom variable trick. 
idGT :: GTE s r -> GT s r
idGT = unsafeCoerce#

eqGT :: GT s r -> GTE s r
eqGT = unsafeCoerce#

type Ptr_ eq s r = STRef r (Maybe (GT_ eq s r))
type Ptr s r     = STRef r (Maybe (GT s r))
type GTm m s r   = m (ST r) (GT s r)

data Fix s  = Fix (s (Fix s)) | Var Int

-- ** MutVars
fresh	  :: ST r (GT_ eq s r)
readVar   :: STRef s a -> ST s a
write     :: STRef s a -> a -> ST s ()
isEmptyVar:: GT_ eq s r -> ST r (Bool)

fresh     = newSTRef Nothing >>= return . MutVar
readVar r = readSTRef r
write r x = writeSTRef r x
isEmptyVar (MutVar r) = liftM isNothing (readVar r)

-- ** Accesors
isGenVar, isMutVar, isCtxVar, isTerm :: GT_ eq s r -> Bool
isGenVar GenVar{} = True
isGenVar _ = False
isMutVar MutVar{} = True
isMutVar _ = False
isCtxVar CtxVar{} = True
isCtxVar _ = False
isTerm S{} = True
isTerm _   = False 

-- | Ought to call colGT before this to make sure all the variables have
--   been dereferenced 
collect_   :: Foldable s  => (GT_ eq s r -> Bool) -> GT_ eq s r -> [GT_ eq s r]
collect_ p (S x) = foldr (\t gg -> collect_ p t ++ gg) [] x
collect_ p x = if p x then [x] else []

vars :: Foldable s => GT_ eq s r -> [GT_ eq s r]
vars = collect_ (\x->isGenVar x || isMutVar x)

noCVars, noGVars, noMVars :: Foldable s => GT_ eq s r -> Bool
noGVars = null . collect_ isGenVar
noMVars = null . collect_ isMutVar 
noCVars = null . collect_ isCtxVar 

-----------------------------
-- * The Class of Match-ables
-----------------------------
class (Traversable s) => RWTerm s where
    matchTerm     :: s x -> s x -> Maybe [(x,x)]

----------------------
-- * Substitutions
----------------------
newtype SubstG a = Subst {subst::[a]}
   deriving (Foldable, Functor, Traversable)
--newtype Subst s r = Subst {subst::[GT s r]}

type Subst s r = SubstG (GT s r)
type Subst_ eq s r = SubstG (GT_ eq s r)

--emptyS = Subst [GenVar n | n <- [0..]]
emptyS = Subst mempty

mkVarsForTerm :: Foldable s => GT_ eq s r -> ST r (Subst_ eq s r)
mkVarsForTerm t | null vars_t = return emptyS
                | otherwise   = do
    newvars <- replicateM (topvar+1) fresh 
    return (Subst newvars)
   where vars_t = vars t
         topvar = maximum [ i | GenVar i <- vars_t ]

------------------------
-- * The Omega type class 
------------------------
-- |"Omega is just a Type Class constraint synonym" 
class ( MonadError (TRSException) (m (ST r)), MonadTrans m, Monad (m (ST r)), Functor (m (ST r)), RWTerm s) => 
    Omega (m :: (* -> *) -> * -> *) (s :: * -> *) r

class (Omega m s r, MonadPlus (m (ST r))) => OmegaPlus m s r 

instance ( MonadError (TRSException) (m (ST r)), MonadTrans m, Monad (m (ST r)), Functor (m (ST r)), RWTerm s) => Omega m s r
instance ( MonadError (TRSException) (m (ST r)), MonadTrans m, MonadPlus (m (ST r)), Functor (m (ST r)), RWTerm s) => OmegaPlus m s r

-----------------------
-- * Exceptions
-----------------------
data TRSException = Match (MatchException)
                  | Unify (UnifyException)
  deriving (Show,Eq)
data MatchException = GenErrorMatch
                    | ShapeErrorMatch
  deriving (Show,Eq)

data UnifyException where 
    GenErrorUnify   :: UnifyException
    ShapeErrorUnify :: Show a => a -> a -> UnifyException
    OccursError     :: UnifyException

instance Show UnifyException where
  show GenErrorUnify = "Unification: general error"
  show OccursError   = "Unification: occurs  error"
  show (ShapeErrorUnify x y) = "Can't unify " ++ show x ++ " and " ++ show y

instance Eq UnifyException where
  GenErrorUnify == GenErrorUnify = True
  OccursError   == OccursError   = True
  ShapeErrorUnify _ _ == ShapeErrorUnify _ _ = True
  _ ==  _ = False

instance Error (TRSException) where
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
instance (Show (s (GT_ eq s r))) => Show (GT_ eq s r) where
    show (S s)      = show s
    show (GenVar n) = if n < length varNames 
                         then [varNames !! n] 
                         else ('v' : show n)
    show (CtxVar c) = '[' : show c ++ "]" 
    show (MutVar r) = "?" ++ (show . hashStableName . unsafePerformIO . makeStableName$ r) ++ ":=" ++ (show$  unsafeAll $ ( readSTRef r))
--        where unsafeAll = unsafePerformIO . ST.unsafeSTToIO . lazyToStrictST
        where unsafeAll = unsafePerformIO . unsafeSTToIO 

-- Oops. Does this instance of Ord honor Semantic equality?
instance (Eq(GTE s r), RWTerm s, Ord (s (GTE s r))) => Ord (GTE s r) where
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

instance Show (s(GT s r)) => Show (Subst s r) where
    show = show . subst

instance Show (a) => Show (RuleG (a)) where
    show (a:->b) = show a ++ " -> " ++ show b
--    showList  = unlines . map show
{-
instance Show(GTE s r) => Show(GT s r) where
    show = show . eqGT  

instance (Functor s, Show(s(GTE s r))) => Show(s(GT s r)) where
    show = show . fmap eqGT 
-}
instance Arbitrary(GTE s r) => Arbitrary(GT s r) where
    arbitrary = fmap idGT arbitrary 

----------
-- * Rules
----------
type Rule s r  = RuleG (GTE s r)
type RuleI s r = RuleG (GT  s r)
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

--swap :: Rule s r -> Rule s r
swap (lhs:->rhs) = rhs:->lhs

