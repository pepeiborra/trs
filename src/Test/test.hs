{-# OPTIONS_GHC -fglasgow-exts -fno-mono-pat-binds -fno-monomorphism-restriction #-}
module Test where
import TRS.Core
import TRS.Utils
import Data.Foldable
import Data.Traversable
import Control.Applicative

import Prelude hiding ( all, maximum, minimum, any, mapM_,mapM, foldr, foldl
                      , and, concat, concatMap, sequence, elem, notElem)

import Test.HUnit
import Debug.Trace 

tests = TestList
        [ testRewriting1
        , testRewriting2
        , testRewriting3
        , testRewriting4
        , testRewriting5
        , testNarrowing ]

main = runTestTT tests


------------------------
-- The Terms dataType
------------------------
type PeanoT r = GT Peano r

data Peano a = a :+ a
             | Succ a
             | Zero
             | V Int
    deriving (Eq, Ord, Show)

-- helper constructors
x +: y = S (x :+ y)
s = S . Succ
z = S Zero

instance Traversable Peano where
    traverse f Zero = pure Zero
    traverse f (Succ a) = Succ <$> f a
    traverse f (a :+ b) = (:+) <$> f a <*> f b
    traverse f (V i)    = pure (V i)
instance Functor Peano where
    fmap = fmapDefault
instance Foldable Peano where
    foldMap = foldMapDefault

instance RWTerm Peano where 
    matchTerm Zero Zero = Just []
    matchTerm (Succ x) (Succ y) = Just [(x,y)]
    matchTerm (a :+ b) (c :+ d) = Just [(a,c),(b,d)]
    matchTerm x y = Nothing
    toVar = V

p (Succ _) = "succ"
p (_ :+ _) = "+"
p Zero     = "0"
----------------------------
-- a TRS 
----------------------------
peanoTRS = [  x +: s(y) :-> s(x +: y)
            , x +: z    :-> x         ]

(x,y) = (GenVar 1, GenVar 2)

-- Testing rewriting
two   = s(s(z))
five  = s(s(s(two)))
seven = two +: five

seven' = runL (rewrite1 peanoTRS seven)
eight' = runL (rewrite1 peanoTRS (seven +: s(z)))

-- One Step rewriting
testRewriting1 = [s(s(s(z)) +: s(s(s(s(z)))))] ~=? seven'
testRewriting2 = TestLabel "One step" $ TestList 
 [ length eight' ~=? 2 
 , (s(seven +: z) `elem` eight') ~? "2"
 , ((s(s(s(z)) +: s(s(s(s(z))))) +: s(z)) `elem` eight') ~? "3" ]

-- Normal Rewriting
testRewriting3 = s(s(five)) ~=? runE (rewrite peanoTRS (seven))
testRewriting4 = s(s(s(five))) ~=? runE (rewrite peanoTRS (seven +: s(z)))

-- Non confluent rewriting
sillyRules = [ z :-> s(z), z :-> s(s(z)) ]

testRewriting5 = test (assert True) --TODO

-- Testing Narrowing
peanoTRS2 = [ s(s(z)) +: s(x) :-> s(s(s(x)))
             , z +: s(x) :-> s(x)
            ]

four = y +: s(s(z))

fourN1 = runL (sndM $ narrow1 peanoTRS2 four)
--fourNFix = runL (fixM (fmap snd $ narrow1 peanoTRS2) four)
fourNFull = runG (fmap3 snd (narrowFull peanoTRS2) four)

fiveN = runL (sndM $ narrow1 peanoTRS2 (s(four)))
noNarrowFull' = runG (fmap3 snd (narrowFull peanoTRS2) two)
noNarrow' = runL (sndM$ narrow1 peanoTRS2 two)

testNarrowing = TestList [ [s(s(s(s(z)))), s(s(z))] ~=? fourN1
                         , [s(s(s(s(z)))), s(s(z))] ~=? fourNFull 
                         ]


-- helpers
msg ==> assertion = TestLabel msg . TestCase $ assertion

sndM :: Functor m => m(a,b) -> m b
sndM = fmap snd

infixl 0 ==>
infixl 2 ? 
infixl 2 =?

(?) = (Test.HUnit.@?)
(=?) = (Test.HUnit.@=?)