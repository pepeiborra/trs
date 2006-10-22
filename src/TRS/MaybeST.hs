-----------------------------------------------------------------------------------------
{-| Module      : TRS.MaybeST
    Copyright   : 
    License     : All Rights Reserved

    Maintainer  : 
    Stability   : 
    Portability : 
-}
-----------------------------------------------------------------------------------------

module TRS.MaybeST where
import TRS.Core
import Control.Monad.ST.Lazy	
import Control.Monad.Trans
import Data.STRef.Lazy
import MaybeT


type MaybeST s = MaybeT (ST s)

runMaybeST :: (forall s. MaybeST s a) -> Maybe a
runMaybeST c = runST (runMaybeT c)

partial :: RSclass s (STRef a) (MaybeST a)
partial = RSclass 
    { sameVarRS  = (==)
    , writeVarRS = \v x -> lift (writeSTRef v x)
    , readVarRS  = lift . readSTRef
    , newVarRS   = lift . newSTRef 
    , errorRS    = fail
    }

