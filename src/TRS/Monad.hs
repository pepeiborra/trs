{-# OPTIONS_GHC -fglasgow-exts #-}
-----------------------------------------------------------------------------------------
{-| Module      : TRS.Monad
    Copyright   : 
    License     : All Rights Reserved

    Maintainer  : 
    Stability   : 
    Portability : 
-}
-----------------------------------------------------------------------------------------
module TRS.Monad (
        module TRS.Monad,
        module TRS.Utils,
        GT(..),
        RuleG(..), Rule, swap
     ) where
import TRS.Core
import TRS.Utils
import Control.Monad
import Data.Traversable

newtype TRS s r a = TRS {unTRS::MonadPlus m => [Rule s r] -> m a}

-- The TRS monad. It is already a Monad because of (-> s) instance,
-- But I want to customize 'return'

instance Monad (TRS s r) where
    c >>= t2 = let TRS t1 = c in 
               TRS$ \rules -> t1 rules >>= \v1 -> unTRS (t2 v1) rules
    return t = TRS$ \_ -> return t

instance MonadPlus (TRS s r) where
    c1 `mplus` c2 = let
                        c1 = TRS t1
                        c2 = TRS t2
             in TRS$ \lib rr -> t1 lib rr `mplus` t2 lib rr
    mzero = TRS$ \_ -> mzero

runTRS :: (Traversable s, Functor m, MonadPlus m, Show (s (GT s r))) => 
          [Rule s r] -> TRS s r a -> m a
runTRS rules trs = let
    in unTRS trs rules

equal :: GT s r -> GT s r -> TRS s r Bool
equal t1 t2 = TRS$ \lib rules -> return$ equal t1 t2

equalR :: Rule s r -> Rule s r -> TRS s r Bool
equalR (l1:->r1) (l2:->r2) = do 
    l <- l1 `equal` l2
    r <- r1 `equal` r2
    return (l && r)

-- | Unbounded/Big-step Rewriting (to N.F.)
rewrite :: GT s r -> TRS s r (GT s r) 
rewrite t = TRS$ \rules -> fixM (rewrite rules) t

-- | One-step rewriting
rewrite1 :: GT s r -> TRS s r (GT s r)
rewrite1 t = TRS$ \rules -> rewrite rules t

-- | Unbounded narrowing
narrow :: GT s r -> TRS s r (GT s r)
narrow t = TRS$ \rules -> fixM (narrow rules) t

-- | One-step narrowing
narrow1 :: GT s r -> TRS s r (GT s r)
narrow1 t = TRS$ \rules -> narrow rules t

narrowAll :: GT s r -> TRS s r [(Subst s r, GT s r)]
narrowAll t = TRS$ \rules -> narrowAll rules t

generalize :: GT s r -> TRS s r (GT s r)
generalize t = TRS$ \_ -> generalize t

fresh :: TRS s r (GT s r)
fresh = TRS$ \_ -> fresh

instan ::  [GT s r] -> GT s r -> TRS s r (GT s r)
instan vars t = TRS$ \_ -> instan vars t

getRules :: TRS s r [Rule s r]
getRules = TRS$ \rules -> return rules

withRules :: [Rule s r] -> TRS s r a -> TRS s r a
withRules rules c = TRS$ \_ -> unTRS c rules


-- Esto ya es un experimento, el no va más... NB: I still can't figure out the types
{-
runTRS' :: (Traversable s, Functor (n a), MonadPlus (n a), Show (s (GT s r)), Functor t, Functor (TRS s r)) => 
           RSclass s r (n a) -> [Rule s r] -> ((forall a1. (n a1) (t (Fix s))) -> t (Fix s)) -> 
           (forall s1. TRS s1 r (t (GT s r))) -> t (GT s r)
runTRS' gts rules runM trs = let
       lib = makeUnify gts
    in fromFixG $ runM (unTRS (fmap2 toFix trs) lib rules)
-}
-------------------------------
-- Idea for SYB based rewriting
-------------------------------
{-
I got this idea while I was thinking about rewriting strategies.
In the implementation of the narrowing and rewrite commands, I have 
started with a rewriteTop function, which does the actual job at the
top position, and then generalized this to inner positions. The 
generalization can be abstracted both for narrowing and rewriting and
constitutes the rewriting(resp. narrowing) strategy employed.

This brings SYB to my mind. I should read SYB again and see what their
work on strategies may have in common with the TRS system here. Maybe there
is opportunity for reuse.
How many times have I read SYB, and still I keep coming back?

* NOTE: I've been trying to play with this, but got discouraged because
        it's not possible to derive Typeable/Data for the GT type
-}

-------------------------
-- Idea for a TRS Monad
-------------------------
{-
Based on the TRS type above, encapsulate it in a monad whose run command is:

runTRS :: GTstruct s r m -> [Rule s r] -> TRS s r a -> a 

And additionally provides the following monadic operations, 
extracted from the GTstruct thing: 
rewrite :: TRS s r ()
narrow  :: TRS s r ()
unify, inst, freshv ...etc

This buys us some extra abstraction. A refinement could be:
runTRS :: RSClass s r m -> [Rule s r] -> TRS s r a -> a

So the user doesn't even need to instantiate the machine.

This one might be my long time sought Rewriting Monad.
We could transform RSClass back into a type class and in such way 
have a better integration with autoderivable type classes.
Actually, now my question would be: why are we using these first-order
modules when we could be using a regular type class?
  * NOTE: Because that would probably run into issues with MPTC and FD.
-}