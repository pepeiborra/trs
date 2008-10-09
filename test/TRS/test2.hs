{-# LANGUAGE TypeOperators, FlexibleContexts, PatternSignatures #-}

module TRS.Test2 where

import Control.Applicative
import Data.Foldable (concat, toList)
import Data.List (intersect)
import Data.Maybe
import System.Environment
--import Test.QuickCheck hiding (variant)
import Test.SmallCheck as Small
import Prelude hiding (concat)

import TRS
import TRS.Rules
import TRS.Types
import TRS.Rewriting
import TRS.Narrowing
import TRS.UMonad
import TRS.Unification
import TRS.Utils
import TRS.Context
import TRS.Test.Peano
import TRS.Test.Instances

{-
main = do
  [i] <- getArgs
  print $ fromJust $ narrowFib (read i)
-}

main = do
{-
  putStrLn "Variant" >> quickCheck propVariant
  putStrLn "Narrowing Soundness 1 " >> quickCheck (propNarrowingSoundness peanoTRS)
  putStrLn "Narrowing Soundness 2 " >> quickCheck (propNarrowingSoundness peanoTRS')
  putStrLn "Reduce gives Normal Forms 1" >> quickCheck (propReduceNF peanoTRS )
  putStrLn "Reduce gives Normal Forms 2" >> quickCheck (propReduceNF peanoTRS')
-}
  putStrLn "Variant" >> Small.smallCheck 8 propVariant
  putStrLn "Narrowing Soundness 1 " >> Small.smallCheck 8 propNarrowingSoundness
  putStrLn "Reduce gives Normal Forms 1" >> Small.smallCheck 8 propReduceNF
  putStrLn "Narrowing gives idempotent subts" >> smallCheck 8 propSubstitutionIdempotency

reduceFib,narrowFib :: MonadPlus1 m => Int -> m (Term PeanoTH)
reduceFib i = reduce fibTRS (fib $ (iterate s z) !! i)
narrowFib i = fst <$> narrow fibTRS (fib $ (iterate s z) !! i)

peanoTRS = [ x +: s(y) :-> s(x +: y)
           , y +: z    :-> y         ] :: [Rule PeanoT]
peanoTRS'= [ s x +: y :-> s(x +: y)
           , z   +: y :-> y         ] :: [Rule PeanoT]

fibTRS = peanoTRS ++
         [ fib z :-> s z
         , fib (s z) :-> s z
         , fib (s (s x)) :-> fib (s x) +: fib x]

x,y :: (Var :<: f) => Term f
x = var 0
y = var 1

------------------
-- Properties
------------------

propSubstitutionIdempotency (rr :: [Rule PeanoT]) (t :: Term PeanoTH) =
    isValidTRS rr ==> and $ do
      (t', theta) <- take 100 $ narrows rr t
      return (t' // theta == t' // theta // theta)

propVariant l r t = concat (vars <$> r') `intersect` vars t == []
  where Just r' = evalN (variant (l:->r) t)
        types = ([l,r,t ]:: [Term PeanoT])

propNarrowingVars rr t = isVar t && isValidTRS rr ==> isNothing $ narrow1 rr (reinject t :: Term PeanoTH)
 where types = (rr :: [Rule PeanoT], t :: Term PeanoT)

propNarrowingSoundness rr t = isValidTRS rr ==> and $ do
    (t', sigma) <- take 100 $ narrows rr (reinject t :: Term PeanoTH)
    return ( EqModulo t'  `elem` map EqModulo (rewrites rr (t // sigma)))
  where types = (rr :: [Rule PeanoT], t :: Term PeanoT)

propReduceNF rr t = isValidTRS rr ==> Prelude.and $ do
    t' <- reduce rr t
    return (isNothing $ rewrite1 rr t')
  where types = (rr :: [Rule PeanoT], t :: Term PeanoT)

--------------------------
-- Testing Reductions
--------------------------

-- Testing rewriting
t_two   = s(s(z)) :: Term PeanoTH
t_five  = s(s(s(t_two))) :: Term PeanoTH
t_seven = t_two +: t_five  :: Term PeanoTH


--seven' :: Monad m => m PeanoTH
t_seven' = rewrite1 peanoTRS t_seven :: [Term PeanoTH]
t_eight' = rewrite1 peanoTRS (t_seven +: s(z)) `asTypeOf` Nothing
test1 = TRS.Rewriting.match z (z :: Term PeanoTH) `asTypeOf` Nothing

narr = fst `map` narrow1 peanoTRS t_seven

sx = s x :: Term PeanoTH

sz = s z :: Term PeanoTH

--v = In $ Inr $ Inr $ Var 0 :: PeanoTH  -- In (Inl (Succ (In (Inr (Inr (Var 0))))))

--h = In $ Inr $ Inl $ Hole 0 :: PeanoTH -- In (Inl (Succ (In (Inl Zero))))

f :: Unifyable f => Term f -> ()
f _ = ()

bleh = f t_seven