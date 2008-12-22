{-# LANGUAGE OverlappingInstances, UndecidableInstances #-}
{-# LANGUAGE NoMonoPatBinds, NoMonomorphismRestriction #-}
{-# LANGUAGE  DisambiguateRecordFields #-}
{-# LANGUAGE TemplateHaskell #-}

module TRS.Test (PeanoT, PeanoTH) where

import Data.AlaCarte.Instances ()
import Control.Monad.Logic

import qualified Prelude
import Prelude hiding ( all, maximum, minimum, any, mapM_,mapM, foldr, foldl
                      , and, concat, concatMap, sequence, notElem
                      , (+) )

import Test.HUnit
import Test.QuickCheck (Arbitrary(..), quickCheck, oneof, sized, resize, frequency)
import Test.QuickCheck.Test (quickCheckResult, isSuccess)
import Test.SmallCheck hiding (two, three, four, test)
import qualified Test.SmallCheck     as Small
import qualified Test.LazySmallCheck as LS
import Text.PrettyPrint
import Text.Show.Functions
import Debug.Trace
import System.IO.Unsafe
import GHC.Exts

import TRS
import TRS.Rewriting
import TRS.Narrowing
import TRS.Context
import TRS.Utils
import TRS.Types

import TRS.Test.Instances
import TRS.Test.Peano
import TRS.Test.TermRef

htests = TestList
        [ TestLabel "testRewriting" testRewriting
--        , TestLabel "testNarrowing" testNarrowing
--        , TestLabel "testEquality"  testEquality
        , testProperties qtests
        ]

testProperties = TestList . map (uncurry (flip (~?)))

main   =  runTestTT htests

qtests = [
          ("Contexts Identity", q propCIdentity)
         ,("Contexts Transitivity", q propCTransiti)
         ,("Contexts Totality", q propCSubterms)
--         ,("Semantic Equality", q propSemanticEquality)
--         ,("Rule Equality"    , q propRuleEquality)
--         ,("Full Narrowing Normal Forms", q propNarrowFullNF)
         ]
    where q = fmap isSuccess . quickCheckResult

{-
-------------------------
-- Testing Equality
-------------------------
propSemanticEquality :: Smart(PeanoT) -> Bool
propSemanticEquality (Smart _ t) = let 
    vars_t   = vars t
    new_vars = [ Var (succ i) | Var i<- vars_t]
    new_term = replace (zip vars_t new_vars) t
    in new_term `TRS.semEq` t
--        where types = t :: PeanoT


propRuleEquality :: RuleS Peano -> Bool
propRuleEquality t@(l1:->r1) = t == t

rule1 = x +: y :-> x
rule2 = x +: y :-> y

-}
----------------------------
-- Peano numbers
----------------------------
peanoTRS = [ x +: s(y) :-> s(x +: y)
           , y +: z    :-> y        ] :: [Rule PeanoTH]
peanoTRS'= [ s x +: y :-> s(x +: y)
           , z   +: y :-> y         ] :: [Rule PeanoTH]

--------------------------
-- Testing Reductions
--------------------------
testRewriting = TestLabel "Test Rewriting" $ TestList
        [ testRewriting0
        , testRewriting1
        , testRewriting2
        , testRewriting3
        , testRewriting4
        , testRewNoRules ]

-- Testing rewriting
two   = s(s(z)) :: Term PeanoTH
five  = s(s(s(two))) :: Term PeanoTH
seven = two +: five  :: Term PeanoTH

seven' :: MonadPlus m => m (Term PeanoTH)
seven' = rewrite1 peanoTRS seven
eight' = rewrite1 peanoTRS (seven +: s(z)) :: [Term PeanoTH]

-- One Step rewriting
testRewriting0 = [s(s(s(z)) +: s(s(s(s(z)))))] ~=? seven'
testRewriting1 = TestLabel "One step" $ TestList 
 [ length eight' ~=? 2
 , (s(seven +: z) `elem` eight') ~? "2"
 , ((s(s(s(z)) +: s(s(s(s(z))))) +: s(z)) `elem` eight') ~? "3"
 ]

-- Normal Rewriting
testRewriting2 = s(s(five))    ~=? observe (reduce peanoTRS seven)
testRewriting3 = s(s(s(five))) ~=? observe (reduce peanoTRS ((seven +: s(z))))

-- Non confluent rewriting
sillyRules = [ z :-> s(z), z :-> s(s(z)) ]

testRewriting4 = test (assert True) --TODO

-- Corner cases
testRewNoRules = TestLabel "No Rules" $ rewrite1 ([] :: [Rule PeanoT]) seven ~?= []


------------------------
-- Testing Narrowing
------------------------
peanoTRS2 = [ s(s(z)) +: s(x) :-> s(s(s(x)))
            , z +: s(x) :-> s(x)
            ] :: [Rule PeanoTH]


testNarrowing = TestList [ [s(s(s(s(z)))), s(s(z))] ~=? fourN1
--                         , [s(s(s(s(z)))), s(s(z))] ~=? fourNFull
--                       , [s(s(s(s(s(z))))), s(s(s(z)))] ~=? fiveN
                         , [] ~=? noNarrow'
--                         , [two] ~=? noNarrowFull'
--                         , testAngryTerm
--                         , testNarrowIssue
--                         , fst <$> narrow1 [g (g x) :-> x :: RuleG PeanoTH] (f (g x) x :: PeanoTH) ~?= [f x (g x :: PeanoTH) :: PeanoTH]
--                         , testPropagation
                         ]
four = y +: s(s(z)) :: Term PeanoTH

fourN1 = fst `map` narrow1 peanoTRS2 four
--fourNFix =(fixM (fmap snd $ narrow1 peanoTRS2) four)

fiveN = fst `map` narrow1 peanoTRS2 (s(four))
noNarrow' = fst `map` narrow1 peanoTRS2 two

--fourNFull = fst `map` narrowFull peanoTRS2 four 
--noNarrowFull' = fst `map` narrowFull peanoTRS2 two
{-
-------------------------------
-- The TRS for testing narrowBU
-------------------------------
f = term2 "f"
g :: (T :<: f) => Term f -> Term f
g = term1 "g"
h = term1 "h"
[a,b,c,d] = map constant (map unit "abcd")
    where unit x = [x]

buTRS = [ f b c :-> d
        , g x   :-> f x x
        , a :-> b
        , a :-> c ]

angryTerm = f x x

angryTermFull  = sndM $narrowFull buTRS angryTerm
--angryTermFullv = sndM $narrowFullV buTRS angryTerm

testAngryTerm = TestLabel "Angry Term narrowing" $ 
                TestList [ angryTermFull  ~?= [angryTerm] 
                    --   , angryTermFullv ~?= [c] 
                         ]

--------------------------
-- The narrow issues
--------------------------

isSNF' rr = (fmap null . runListT') 
         . ( ({-Core.-}narrow1 rr =<<) . lift . generalize)
isSNF rr = isNothing . narrow1 rr 

u = ts(x + y)
narrowTrs = [ ts(cero) + y :-> ts(y)
            , ts(ts(cero)) + x :-> ts(ts(x))
            , cero + x :-> x 
            , x + cero :-> x]

u' = snd <$> narrowFull narrowTrs u

-- This one uses the peano System. Tests narrowFullBounded, 
-- using the first step of Tp Forward, where the Interpretation is only
-- one equation long
tpForward1 = snd <$> narrowFullBounded  (isSNF peanoTRS)
                                        [z +: x :-> x] 
                                        (s(x +: y))

tpBackward1 = snd <$> narrow1 (map swap peanoTRS) (s(z) +: x)
    where swap (lhs :-> rhs) = rhs :-> lhs

testNarrowIssue = TestLabel "Narrowing Issues" $ TestList 
        [ Semantic <$> u'     ~?= Semantic <$> [ts(ts(y)),ts(ts(ts(y))),ts(y),ts(x)]
        , Semantic <$> tpForward1 ~?= Semantic <$> [s(x)] 
        , Semantic . isTermRef . snd <$> isList (narrow1 trs_x t)
                              ~=? (Semantic . snd <$> narrow1 trs_y t)
--        , snd <$> narrow1' trs_x' t' ~=? snd <$> narrow1' trs_y' t'
        ]
    where t = z +: y
          trs_x = [x :-> (z +: x)]
          trs_y = [y :-> (z +: y)]
          t' = cero + y
          trs_x' = [x :-> (cero + x)]
          trs_y' = [y :-> (cero + y)]
------------------------
-- Narrowing Properties
------------------------
--propNarrow' :: PeanoT -> Bool
{-
propNarrow' x = let
    aa = snd <$> narrow1  peanoTRS x
    bb = snd <$> narrow1' peanoTRS x
    in (aa =|= bb)
-}
propNarrowFullNF   = forAll (arbitraryPeano (map Var [0..2]) False 3) $ \x ->
                     isSNF peanoTRS x ==> 
                     Semantic (snd $ head$ narrowFull peanoTRS x) == Semantic x
       where types = (x :: PeanoT)

a =|= b = a `intersect` b == a && b `intersect` a == b
-}
{-
propNarrowDefinition x rules = and$ do
               x'    <- narrow1 rules x
               sigma <- get
               someM rules $ \(lhs:->rhs) -> do
                          (subst,lhs') <- autoInst lhs
                          unify lhs' x
                          rhs' <- instan subst rhs
                          return (rhstheta == 
-}
---------------------------------
-- Testing equality modulo vars 
---------------------------------
-- 'macros'
x + y = term "+" [x,y]
cero = term "0" []
ts x = term "s" [x]

testEquality = TestLabel "test equality" $
               TestList [ -- x   ==  y    ~? "Eq modulo Vars"
                           (s x ::Term PeanoT) `equal` (s y :: Term PeanoT)  ~? "With a context"
                        ,  (x+y ::Term Basic)  `equal` (y+x) ~? "Same Name, but unrelated"
                        ]

-----------------------------------------------
-- Verifying the new implementation of contexts
-----------------------------------------------
 -- REVIEW these properties
propCIdentity, propCTransiti :: Term PeanoTH -> Bool
propCIdentity x = and [ ct|>y == x | (y,ct) <- contexts x ]

propCTransiti x = and [ ct|>y|>y1 == x | (y1,ct1) <- contexts x
                                       , (y,ct) <- contexts ct1]

propCSubterms :: Term PeanoT -> Bool
propCSubterms x@(In f) = length (toList f) == length (contexts (reinject x :: Term PeanoTH))

--nSubterms :: Term f -> Int
nSubterms = foldTerm (\x -> 1 Prelude.+ Data.Foldable.sum x)

{-
--------------------------------
-- Propagation of substitutions
--------------------------------

sort   = term1 "sort"
insert = term2 "insert"
cons   = term2 "cons"
nil    = constant "nil"
zero   = constant "zero"
s'     = term1 "succ"

subst_trs = 
    [ insert (s' x) (cons zero nil) :-> cons zero (cons (s' x) nil)
    , sort (cons x nil) :-> cons x nil
      ]

subst_term = insert x (sort y)

{- The narrowing derivation is as follows
1. {y/[x']}, t ~> insert x (cons x' nil)
2. {x/s(x''), x'/zero}

The composed substitution is {x/s(x''), y/[zero]}
-}

testPropagation = let [(s,_)] = narrowFull subst_trs subst_term -- [0, sX]
                      in applySubst s y == cons zero nil
          ~? "Substitutions do not propagate correctly in narrowFull"

-- We can derive a property: a narrowFull derivation must produce
-- the same substitution as the composition of the substitutions of
-- the one step derivations that compose it
-- TODO write this property.

testReplaceM = runST $ do
  t   <- mutableTerm (isTermRef (Ref$ s $ s x))
  let [x] = TRS.collect isMutVar t
  t'  <- replaceM [(x, templateTerm z)] t
  return$ noMVars t'

testDupSubst = runST $ do
  t   <- mutableTerm (( s' $ s' x))
  let [x] = TRS.collect isMutVar t
      subst = SubstM [Just (cons x nil)]
  (subst', _, t') <- dupTermWithSubst subst [] t
  let [x'] = TRS.collect isMutVar t'
  writeVar (ref x') zero
  zonkSubst subst' --(toList subst' == [ (cons zero nil)])

--------------------------
-- Other properties
-------------------------
propDuplication1 :: PeanoT -> Bool
propDuplication1 t = runST (do 
                        t1           <- mutableTerm t 
                        (vars',_,t') <- dupTermWithSubst emptySubstM [] (idGT t1)
                        t''          <- zonkTerm' =<< col t'
                        semeq        <- t1 `semEq` t'
                        return$ Semantic t == Semantic t'' && semeq )
-}
---------------
-- helpers
---------------
sndM :: Functor m => m(a,b) -> m b
sndM = fmap snd

sndM2 = fmap2 snd
sndM3 = fmap3 snd
{-
urunIO  = unsafePerformIO . runIO
urunLIO = unsafePerformIO . runLIO
urunEIO = unsafePerformIO . runEIO

gen x = x >>= (lift . generalize)
gsndM = gen . sndM
-}

{-
-- ----------------
-- Generators
-- ----------------

arbitraryLLCS sig size = do
  Symbol f arity <- elements (defined sig)
  lhs <- term f <$> replicateM arity ( 
                       oneof [var <$> arbitrary
                             ,arbitraryTerm (constructors sig) size])
  rhs <- arbitraryTerm (defined sig ++ constructors sig) size
  return (lhs :-> rhs)

arbitraryTerm :: [Symbol String] -> Int -> Gen BasicTerm
arbitraryTerm sig 0 = Var <$> arbitrary
arbitraryTerm sig size = do 
  Symbol c arity <- elements sig
  term c <$> replicateM arity 
                 (oneof [var <$> arbitrary
                        ,arbitraryTerm sig size2])
      where size2 = size `div` 2

-}

-- $( derive makeSerial ''Var)
-- $( derive makeSerial ''RuleG)
