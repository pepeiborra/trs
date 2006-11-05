module TRS.Core where
import Data.STRef.Lazy
import Data.Foldable
import Data.Traversable	
import Control.Monad.ST.Lazy

data GT_ eq s r = 
   S (s (GT_ eq s r))
 | MutVar (STRef r (Maybe (GT_ eq s r)))
 | GenVar Int
 | CtxVar Int

type GT s r = GT_ Identity s r
data Identity
type GTm m s r = m (ST r) (GT s r)

isGenVar, isMutVar, isCtxVar :: GT_ eq s r -> Bool
collect_  :: Foldable s => (GT_ eq s r -> Bool) -> GT_ eq s r -> [GT_ eq s r]

class (Traversable s) => RWTerm s where
    matchTerm     :: s x -> s x -> Maybe [(x,x)]
