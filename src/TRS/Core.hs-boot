module TRS.Core where
import Data.STRef
import Data.Foldable
import Data.Traversable	
import Control.Monad.ST

data GT s r = 
   S (s (GT s r))
 | MutVar (STRef r (Maybe (GT s r)))
 | GenVar Int
 | CtxVar Int

type Ptr s r   = STRef r (Maybe (GT s r))
--type Subst s r = [GT s r]
type GTm m s r = m (ST r) (GT s r)

isGenVar, isMutVar, isCtxVar :: GT s r -> Bool
collect   :: Foldable s => (GT s r -> Bool) -> GT s r -> [GT s r]

class (Traversable s) => RWTerm s where
    matchTerm     :: s x -> s x -> Maybe [(x,x)]
    toVar         :: Int -> s a
