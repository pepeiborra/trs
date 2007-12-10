{-# OPTIONS_GHC -fglasgow-exts #-}
{-# OPTIONS_GHC -fallow-overlapping-instances #-}
{-# OPTIONS_GHC -fallow-undecidable-instances #-}
{-# OPTIONS_GHC -cpp #-}
module TRS.GTerms where

import Control.Applicative
import Control.Monad
import Control.Monad.ST as ST
import Control.Arrow
import Data.Foldable as Foldable
import Data.Traversable as Traversable
import qualified Data.IntMap as IntMap
import Data.Maybe
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
import TRS.Term hiding ( Semantic )

type Ptr user mode r s = Ptr_ r (GT_ user mode r s)

-- * Generic Terms
{- | 
     The datatype of 'Generic Terms', where the type variables have the following meaning:
   eq: This is a phantom variable used to switch between syntactic and semantic equality (I could have done the same with a separate newtype wrapper)
   s:  This is a type constructor for the structure of terms (See Terms.hs for an example)
   r:  This is the ST monad thread token
-}

#ifdef __HADDOCK__
data GT_ user mode r s = 
   S (s(GT_ user mode r s))
 | MutVar (Maybe user) (Ptr user mode r s) -- | A Mutable variable
 | GenVar (Maybe user) Int                 -- | A type scheme, univ. quantified variable 
 | CtxVar Int
 | Skolem (Maybe user) Int                 -- | For internal use
  
#else
data GT_ (user :: *) (mode :: *)  (r :: *) (s :: * -> *) = 
   S (s(GT_ user mode r s))
 | MutVar {note_::Maybe user, ref::Ptr user mode r s}
 | GenVar {note_::Maybe user, unique::Int}
 | CtxVar {unique::Int}
 | Skolem {note_::Maybe user, unique::Int}
-- | Token  {t :: forall s. t s}
 | Top    {note_::Maybe user}
 | Bottom {note_::Maybe user}
#endif

instance TermShape s => Eq (GT_ user mode r s) where
  MutVar{ref=n}    == MutVar{ref=m}    = m==n
  GenVar{unique=n} == GenVar{unique=m} = m==n
  Skolem{unique=n} == Skolem{unique=m} = m==n
  CtxVar{unique=n} == CtxVar{unique=m} = m==n
  Bottom{} == Bottom{} = True
  Top{} == Top{} = True
  S x == S y | Just pairs <- matchTerm x y 
             = all (uncurry (==)) pairs 
  _   ==  _  = False

-- 'Witness' types for equality. The actual Eq instances for GT_ are not 
--  defined here, but in the Core module
data Normal
data Basic      -- denotes a Basic Narrowing derivation

type GT user r s  = GT_ user Normal r s

genVar :: Int -> GT_ mode user r s
genVar = GenVar Nothing

mutVar :: Maybe user -> Int -> ST r (GT_ user mode r s)
mutVar note = fmap (MutVar note) . newVar

top, bottom :: user -> GT_ user mode r s
bottom = Bottom . Just
top = Top . Just

fresh :: ST r (GT_ user mode r s)
fresh = fmap (MutVar Nothing) freshVar

skolem :: Int -> GT_ user mode r s
skolem = Skolem Nothing

note S{} = Nothing
note CtxVar{} = Nothing
note t = note_ t

setNote :: user -> GT_ user mode r s -> GT_ user mode r s
setNote _ t@S{} = t
setNote _ t@CtxVar{} = t
setNote note t = t{note_=Just note}


idGT :: GT_ user mode r s -> GT user r s
idGT = unsafeCoerce#

basicGT :: GT_ user mode r s -> GT_ user Basic r s
basicGT = unsafeCoerce#

freeGT :: GT_ user mode r s -> GT_ user mode2 r s
freeGT = unsafeCoerce#

isGT :: GT user r s -> GT user r s
isGT x = x

-- ** Accesors
isGenVar, isMutVar, isCtxVar, isTerm :: GT_ user eq r s -> Bool
isGenVar GenVar{} = True
isGenVar _ = False
isMutVar MutVar{} = True
isMutVar _ = False
isCtxVar CtxVar{} = True
isCtxVar _ = False
isTerm S{} = True
isTerm _   = False 

isUnboundVar MutVar{ref=ptr} = maybe (return True) isUnboundVar =<< readVar ptr
isUnboundVar v = return (isVar v)

-- ** Predicates
noCVars, noGVars, noMVars :: (TermShape s, Foldable s) => GT_ user mode r s -> Bool
noGVars = null . collect isGenVar 
noMVars = null . collect isMutVar 
noCVars = null . collect isCtxVar

-- --------------------
-- GT Term structure
-- --------------------
instance TermShape s => Term (GT_ user mode r) s user where
  {-# SPECIALIZE instance Term (GT_ () eq r) BasicShape () #-}
  isVar S{}          = False
  isVar Top{}        = False
  isVar Bottom{}     = False
  isVar MutVar{}     = True
  isVar GenVar{}     = True
  isVar CtxVar{}     = True
  isVar Skolem{}     = True
  mkVar              = genVar
  varId (GenVar _ i) = Just i
  varId (CtxVar i)   = Just i
  varId (MutVar _ i) = Nothing -- error "unexpected mutvar"
  contents (S x) = Just x
  contents _     = Nothing
  build          = S
  fromGTM _      = return . return . unsafeCoerce#
  toGTM _        = return . return . unsafeCoerce#

---------------------------------------------
-- * Positions. Indexing over subterms.
---------------------------------------------
type Position = [Int]
subtermAt :: (Functor m, MonadPlus m, Traversable s) => 
             GT_ user eq r s -> Position -> m (GT_ user eq r s)
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
updateAt  :: (Traversable s) => GT_ user eq r s -> Position -> GT_ user eq r s -> GT_ user eq r s
updateAt _ (0:_) st' = st'
updateAt (S t) (i:is) st' = S . fmap (\(j,st) -> if i==j then updateAt st is st' else st) 
                          . unsafeZipG [1..] 
                          $ t
updateAt _ [] x' = x'
updateAt x _ _ = x


-- | Like updateAt, but returns a tuple with the new term, and the previous subterm at position pos
updateAt'  :: (Functor m, MonadPlus m, Traversable s) => 
             GT_ user eq r s -> Position -> GT_ user eq r s -> m (GT_ user eq r s, GT_ user eq r s)
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
type STV r a = STRef r (IntMap.IntMap Unique (GT_ user mode r s)) -> ST r a
instance VarMonad (STV r) (GT_ user mode r s) where
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

instance (Show (s (GT_ user mode r s)), Show user) => Show (GT_ user mode r s) where
    show (S s)      = show s
    show GenVar{unique=n,note_=nt} = showsVar 0 n (showNote nt) --TODO 
    show CtxVar{unique=n} = brackets (show n)
    show Skolem{unique=n,note_=nt} = hash (show n ++ showNote nt)
    show MutVar{ref=r,note_=nt}    = "?" ++ (show . hashStableName 
                                            . unsafePerformIO . makeStableName$ r) 
                                  ++ showNote nt
                                  ++ ":=" ++ (show$ unsafeAll $ ( readSTRef r))
--        where unsafeAll = unsafePerformIO . ST.unsafeSTToIO . lazyToStrictST
        where unsafeAll = unsafePerformIO . ST.unsafeSTToIO 
    show Bottom{note_=nt} = "_|_" ++ showNote nt
    show Top{note_=nt}    = "T" ++ showNote nt

showNote Nothing = ""
showNote (Just t)= parens (show t)

{-
instance Show (s(GTE user r s)) => Show (SubstG (GTE user r s)) where
    show = show . subst
-}

{- NEED A STREF ORD INSTANCE FOR THIS TO WORK 

instance (TermShape s, Ord user, Ord (s (GT_ mode user r s))) => 
    Ord (GT_ mode user r s) where
    compare (S t1) (S t2)
     | S t1 == S t2 = EQ
     | otherwise    = compare t1 t2
    compare S{} _ = GT
    compare _ S{} = LT
    compare MutVar{ref=r1} MutVar{ref=r2} = compare r1 r2
    compare MutVar{} _ = GT
    compare _ MutVar{} = LT
    compare (Token t1) (Token t2) = compare t1 t2
    compare Token{} _ = GT
    compare _ Token{} = LT
    compare m n = (compare `on` unique) m n
-}
