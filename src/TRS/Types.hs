{-# OPTIONS_GHC -fglasgow-exts -fallow-undecidable-instances -fallow-overlapping-instances -fallow-incoherent-instances -cpp #-}

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
import Control.Monad.Trans
import Control.Monad.ST
import Data.STRef
import System.Mem.StableName
import System.IO.Unsafe
import Prelude hiding ( all, maximum, minimum, any, mapM_,mapM, foldr, foldl
                      , and, concat, concatMap, sequence, elem, notElem)

import GHC.Exts

data GT_ eq s r = 
   S (s(GT_ eq s r))
 | MutVar (STRef r (Maybe (GT_ eq s r)))
 | GenVar Int
 | CtxVar Int

data Identity 
data Equivalence -- modulo variables

type GT s r = GT_ Identity s r
type GTE s r = GT_ Equivalence s r

s :: s(GTE s r) -> GTE s r
s      = S
genVar :: Int -> GTE s r
genVar = GenVar

idGT :: GTE s r -> GT s r
idGT = unsafeCoerce#

eqGT :: GT s r -> GTE s r
eqGT = unsafeCoerce#

class (Traversable s) => RWTerm s where
    matchTerm     :: s x -> s x -> Maybe [(x,x)]

type Ptr s r   = STRef r (Maybe (GT s r))
newtype Subst s r = Subst {subst::[GT s r]}

--emptyS = Subst [GenVar n | n <- [0..]]
emptyS = Subst mempty


type GTm m s r = m (ST r) (GT s r)

data Fix s  = Fix (s (Fix s)) | Var Int
   deriving Show

type Rule s r  = RuleG (GTE s r)
type RuleI s r = RuleG (GT  s r)
data RuleG a = a :-> a -- (GT s r) :-> (GT s r) -- Switch to a newtype for efficiency
   deriving (Eq, Ord)

--swap :: Rule s r -> Rule s r
swap (lhs:->rhs) = rhs:->lhs

-- "Omega is just a Type Class constraint synonym" 
--             is an unregistered trademark of Pepe Type Hacker enterprises
class ( MonadTrans m, Monad (m (ST r)), Functor (m (ST r)), RWTerm s, 
        Show (s(GTE s r))) => 
    Omega (m :: (* -> *) -> * -> *) (s :: * -> *) r

class (Omega m s r, MonadPlus (m (ST r))) => OmegaPlus m s r 

instance (MonadTrans m, Monad (m (ST r)), Functor (m (ST r)), RWTerm s, Show (s (GTE s r))) => Omega m s r
instance (MonadTrans m, MonadPlus (m (ST r)), Functor (m (ST r)), RWTerm s, Show (s (GTE s r))) => OmegaPlus m s r

--------------------------------
-- Instances and base operators
--------------------------------

liftSubst f (Subst s) = Subst (f s)

vars = "XYZWJIKHW"
instance (Show (s (GT_ eq s r))) => Show (GT_ eq s r) where
    show (S s)      = show s
    show (GenVar n) = if n < length vars then [vars !! n] else ('v' : show n)
    show (MutVar r) = "?" ++ (show . hashStableName . unsafePerformIO . makeStableName$ r) ++ ":=" ++ (show$  unsafePerformIO$ unsafeSTToIO $ ( readSTRef r))
    show (CtxVar c) = '[' : show c ++ "]" 

instance (Eq(GTE s r), RWTerm s, Ord (s (GTE s r))) => Ord (GTE s r) where
    compare (S t1) (S t2) = compare t1 t2
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

instance Functor (RuleG) where
    fmap = fmapDefault              --fmap f (l:->r) = f l :-> f r
instance Foldable (RuleG) where 
    foldMap = foldMapDefault        --foldMap f (l:->r) = f l `mappend` f r
instance Traversable (RuleG ) where
    traverse f (l:->r) = (:->) <$> f l <*> f r

----------------------------
-- Other stuff
----------------------------
--isGenVar, isMutVar, isCtxVar :: GT s r -> Bool
isGenVar GenVar{} = True
isGenVar _ = False
isMutVar MutVar{} = True
isMutVar _ = False
isCtxVar CtxVar{} = True
isCtxVar _ = False

-- | Ought to call colGT before this to make sure all the variables have
--   been dereferenced 
collect_   :: Foldable s  => (GT_ eq s r -> Bool) -> GT_ eq s r -> [GT_ eq s r]
collect_ p (S x) = foldr (\t gg -> collect_ p t ++ gg) [] x
collect_ p x = if p x then [x] else []
