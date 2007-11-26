module TRS.Tyvars where

import Control.Applicative
import Control.Monad
import Control.Monad.ST
import Data.STRef

import TRS.Types

data Mutable a = Empty   {unique::Unique}
               | Mutable {unique::Unique, val::a}
        deriving (Eq, Show)

type Ptr_ r a = STRef r (Mutable a)

-- ** MutVars
newVar    :: Int -> ST r (Ptr_ r a)
readVar   :: Ptr_ r a -> ST r (Maybe a)
readVar'  :: Ptr_ r a -> ST r (Mutable a)
write     :: Ptr_ r a -> a -> ST r ()
isEmptyVar:: Ptr_ r a -> ST r (Bool)

-- fresh     = MutVar <$> newSTRef DontKnow
newVar    = newSTRef . Empty
readVar r = readVar' r >>= \x -> return$ case x of
                                    Mutable _ y -> Just y
                                    _           -> Nothing
readVar'  = readSTRef
write r v = do
    i <- getUnique r
    writeSTRef r (Mutable i v)

getUnique :: Ptr_ r a -> ST r Unique
getUnique r = liftM unique (readVar' r)

isEmptyVar= liftM isEmpty . readVar'
    where isEmpty Empty{} = True
          isEmpty _ = False

