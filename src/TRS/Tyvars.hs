{-# OPTIONS_GHC -fignore-breakpoints #-}
module TRS.Tyvars where

import Control.Applicative
import Control.Monad
import Control.Monad.ST
import Data.STRef

import TRS.Types

data Mutable a = Empty   {varUnique::Maybe Unique}
               | Mutable {varUnique::Maybe Unique, val::a}
        deriving (Eq, Show, Ord)

type Ptr_ r a = STRef r (Mutable a)

-- ** MutVars
newVar    :: Int -> ST r (Ptr_ r a)
readVar   :: Ptr_ r a -> ST r (Maybe a)
readVar'  :: Ptr_ r a -> ST r (Mutable a)
writeVar  :: Ptr_ r a -> a -> ST r ()
isEmptyVar:: Ptr_ r a -> ST r (Bool)

-- fresh     = MutVar <$> newSTRef DontKnow
freshVar  = newSTRef (Empty Nothing)
newVar    = newSTRef . Empty . Just
readVar r = readVar' r >>= \x -> return$ case x of
                                    Mutable _ y -> Just y
                                    _           -> Nothing
readVar'  = readSTRef
writeVar r v = do
    i <- getUnique r
    writeSTRef r (Mutable i v)

getUnique :: Ptr_ r a -> ST r (Maybe Unique)
getUnique r = liftM varUnique (readVar' r)

isEmptyVar= liftM isEmpty . readVar'
    where isEmpty Mutable{} = False
          isEmpty _ = True

