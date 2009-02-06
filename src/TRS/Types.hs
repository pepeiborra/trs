{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, FlexibleContexts, UndecidableInstances, OverlappingInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GADTs, TypeFamilies #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  TRS.Types
-- Copyright   :  (c) Pepe Iborra 2006-
--                (c) Universidad Politcnica de Valencia 2006-2007
-- License     :  BSD-style (see LICENSE)
--
-- Maintainer  :  pepeiborra@gmail.org
-- Stability   :  experimental
-- Portability :  portable
--
-- Home for all types and helpers. Internal
-----------------------------------------------------------------------------

module TRS.Types (module Data.AlaCarte, module TRS.Types) where

import Control.Applicative
import Control.Monad as M hiding (msum, mapM)
import Control.Parallel.Strategies
import Data.AlaCarte hiding (Expr(..), match, inject, reinject)
import Data.Foldable as Foldable
import Data.Int
import Data.Monoid
import Data.Traversable
import Data.HashTable (hashInt, hashString)
import qualified Data.HashTable as HT
import System.IO.Unsafe
import Text.PrettyPrint
import Prelude hiding ( all, maximum, minimum, any, mapM_,mapM, foldr, foldl
                      , and, concat, concatMap, sequence, sum, elem, notElem)

import TRS.Utils hiding ( parens, size )


type Unique = Int

-- --------------------------
-- * A la Carte Terms
-- --------------------------

newtype Term t = In (t (Term t))

--instance Eq (t(Term t)) => Eq (Term t) where t1@(In a) == t2@(In b) = unsafePtrEq t1 t2 || let eq = a == b in if eq then trace "Ptr equality miss" eq else eq
instance Eq (t(Term t)) => Eq (Term t) where t1@(In a) == t2@(In b) = unsafePtrEq t1 t2 || a == b

--deriving instance Eq (f (Term f)) => Eq (Term f)
deriving instance Ord (f (Term f)) => Ord (Term f)

mapTerm :: Functor f => (f (Term f) -> Term f) -> Term f -> Term f
mapTerm f (In t) = f t

foldTerm :: Functor f => (f a -> a) -> Term f -> a
foldTerm f (In t) = f (fmap (foldTerm f) t)

foldTermM :: (Monad m, Traversable f) => (f a -> m a) -> Term f -> m a
foldTermM f (In t) = f =<< mapM (foldTermM f) t

foldTermTop :: Functor f => (f (Term f) -> f(Term f)) -> Term f -> Term f
foldTermTop f (In t)= In (foldTermTop f `fmap` f t)

inject :: (g :<: f) => g (Term f) -> Term f
inject = In . inj

reinject :: (f :<: g, HashConsed g) => Term f -> Term g
reinject = hashCons . foldTerm inject

reinject' :: (f :<: fs, fs :<: gs, HashConsed gs) => f (Term fs) -> f (Term gs)
reinject' = fmap reinject

open :: (g :<: f) => Term f -> Maybe (g (Term f))
open (In t) = prj t

class Crush f where crushF :: (a -> b -> b) -> b -> f a -> b
instance (Crush a, Crush b) => Crush (a :+: b) where
    crushF f z (Inl x) = crushF f z x
    crushF f z (Inr x) = crushF f z x

crush :: Crush f => (Term f -> b -> b) -> b -> Term f -> b
crush f z (In t) = crushF f z t

-- -----------------------------
-- * The first building blocks
-- -----------------------------
type Basic = Var :+: T String

data T id a where T :: Eq id => !(id) -> [a] -> T id a
instance Eq a =>Eq (T id a) where T id1 tt1 == T id2 tt2 = id1 == id2 && tt1 == tt2
instance Functor (T id)     where fmap f (T s aa) = T s (map f aa)
instance Traversable (T id) where traverse f (T s tt) = T s <$> traverse f tt
instance Foldable (T id)    where foldMap  f (T s tt) = mconcat $ map f tt
instance Crush (T id)       where crushF f z (T s tt) = foldr f z tt
instance (Show id, Show a) => Show (T id a) where show (T id tt) =  "T " ++ show id ++ " " ++ show tt

data Var s = Var (Maybe String) Int deriving (Eq, Show)
instance Functor Var     where fmap _ (Var s i) = Var s i
instance Traversable Var where traverse _ (Var s i) = pure (Var s i)
instance Foldable Var    where foldMap = foldMapDefault
instance Ord (Var a)     where compare (Var _ a) (Var _ b) = compare a b
instance Crush Var       where crushF _ z _ = z

var :: (HashConsed s, Var :<: s) => Int -> Term s
var = var' Nothing

var' :: (HashConsed s, Var :<: s) => Maybe String -> Int -> Term s
var' =((hashCons . inject) .) . Var

varLabeled :: (HashConsed s, Var :<: s) => String -> Int -> Term s
varLabeled l = {-# SCC "varLabeled" #-} var' (Just l)

inV :: Var t -> Term Var
inV (Var n i) = In (Var n i)

class Functor f => IsVar f where
    isVarF    :: f x -> Bool
    uniqueIdF :: f x -> Maybe Int

instance IsVar Var where isVarF _ = True; uniqueIdF (Var _ i) = Just i
instance (IsVar a, IsVar b) => IsVar (a:+:b) where
    isVarF (Inr x) = isVarF x
    isVarF (Inl y) = isVarF y
    uniqueIdF (Inr x) = uniqueIdF x
    uniqueIdF (Inl x) = uniqueIdF x

instance Functor otherwise => IsVar otherwise where isVarF _ = False; uniqueIdF _ = Nothing

isVar :: IsVar f => Term f -> Bool
isVar = {-# SCC "isVar" #-} foldTerm isVarF

uniqueId :: IsVar f => Term f -> Maybe Int
uniqueId = foldTerm uniqueIdF

varId :: Var f -> Int
varId (Var _ i) = {-# SCC "varId'" #-} i

instance (Ord id, Ord a) => Ord (T id a) where
    (T s1 tt1) `compare` (T s2 tt2) =
        case compare s1 s2 of
          EQ -> compare tt1 tt2
          x  -> x

-- -----------
-- ZipTerm
--------------
class (Functor f, Foldable f) => Zip f where
  fzipWith  :: Monad m => (a -> b -> m c)  -> f a -> f b -> m (f c)
  fzipWith_ :: Monad m => (a -> b -> m ()) -> f a -> f b -> m ()
  fzipWith_ f v1 v2 = fzipWith f v1 v2 >> return ()

instance (Zip a, Zip b) => Zip (a :+: b) where
    fzipWith  f (Inl x) (Inl y) = Inl `liftM` fzipWith f x y
    fzipWith  f (Inr x) (Inr y) = Inr `liftM` fzipWith f x y
    fzipWith  f _       _       = fail "fzipWith"
    fzipWith_ f (Inl x) (Inl y) = fzipWith_ f x y
    fzipWith_ f (Inr x) (Inr y) = fzipWith_ f x y
    fzipWith_ f _       _       = fail "fzipWith_"
instance Eq id => Zip (T id) where
    fzipWith  f (T s1 tt1) (T s2 tt2) = do
      unless(s1 == s2 && length tt1 == length tt2) $ fail "fzipWith"
      T s1 `liftM` M.zipWithM f tt1 tt2
    fzipWith_ f (T s1 tt1) (T s2 tt2) = do
      unless(s1 == s2 && length tt1 == length tt2) $ fail "fzipWith"
      M.zipWithM_ f tt1 tt2

instance Zip Var where
    fzipWith f (Var u1 i) (Var u2 _) | u1 == u2 = return (Var u1 i)
                                     | otherwise = fail "fzipWith"

fzip :: (Zip f, Monad m) => f a -> f b -> m (f(a,b))
fzip = fzipWith (*) where a * b = return (a,b)

zipTermM :: (Zip f, Monad m) =>
          (Term f -> Term f -> m c) -> Term f -> Term f -> m (f c)
zipTermM f (In t) (In u) = fzipWith f t u

zipTerm :: (Foldable f, Zip f) => Term f -> Term f -> Maybe [(Term f, Term f)]
zipTerm = (fmap toList .) . zipTermM (*) where a * b = return (a,b)

zipTerm' :: (f :<: g, Foldable g, Zip g, HashConsed g) => Term f -> Term g -> Maybe [(Term g, Term g)]
zipTerm' x y = zipTerm (reinject x) y

-----------------
-- Size measures
-----------------


class Size t where size :: t -> Int
instance (Functor f, Foldable f) => Size (Term f) where size = foldTerm (\f -> 1 + sum f)
instance Size t  => Size [t] where size      = sum . fmap size

size' :: (Functor f, Foldable f) => Term f -> [()]
size' = foldTerm ( (():) . Foldable.concat )
------------------------
-- Hash Consing
-- ---------------------
type HashCons f = HT.HashTable ( (Term f)) (Term f)

class Functor f => HashTerm f where hashF :: f Int32 -> Int32
instance HashTerm (T String)  where hashF  (T id tt) = hashString id + sum tt
instance HashTerm Var where hashF (Var (Just n) i) = hashString n + hashInt i
                            hashF (Var _ i) = hashInt i

instance (HashTerm f, HashTerm g) => HashTerm (f :+: g) where
    hashF (Inl l) = hashF l
    hashF (Inr r) = hashF r

--instance (HashTerm t) => HashTerm (Weak t) where hashF w = 

hashTerm :: (HashTerm f) => Term f -> Int32
hashTerm = foldTerm hashF

class  (Eq (Term f), HashTerm f) => HashConsed f where 
    {-# NOINLINE ht #-} 
    ht :: HashCons f
    ht = unsafePerformIO (HT.new (==) hashTerm)

--instance (Eq (Term f), HashTerm f) => HashConsed f
instance HashConsed Basic
instance HashConsed Var
instance HashConsed (T String)

hashCons :: HashConsed f => Term f -> Term f
hashCons t = unsafePerformIO $ do
               mb_t <- HT.lookup ht t
               case mb_t of
                 Just t' -> return t'
                 Nothing -> do 
                           HT.insert ht t t >> return t

-- ----------------
-- NFData instances
-- ----------------

instance NFData (f (Term f)) => NFData (Term f) where rnf (In x) = rnf x
instance NFData a => NFData (T String a) where rnf (T s tt) = rnf s `seq` rnf tt `seq` ()
instance NFData (Var a)  where rnf (Var n s) = rnf n `seq` rnf s `seq` ()
