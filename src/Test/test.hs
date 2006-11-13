{-# OPTIONS_GHC -fglasgow-exts -fno-mono-pat-binds -fno-monomorphism-restriction  -fallow-undecidable-instances #-}
module Test where
import TRS.Core 
import TRS.Types hiding (s)
import qualified TRS.Types as TRS
import TRS.Terms
import TRS.Utils
import Data.Char
import Data.Foldable
import Data.List (intersect)
import Data.Traversable
import Control.Applicative
import Control.Monad.List (ListT(..), liftM, liftM2, lift)
import Control.Monad.ST.Lazy (ST)
import Prelude hiding ( all, maximum, minimum, any, mapM_,mapM, foldr, foldl
                      , and, concat, concatMap, sequence, elem, notElem
                      , (+) )

import Test.HUnit
import Test.QuickCheck hiding (two,three,four,test)
import Text.PrettyPrint
import Debug.Trace 
import System.IO.Unsafe
import GHC.Exts

tests = TestList
        [ testRewriting1
        , testRewriting2
        , testRewriting3
        , testRewriting4
        , testRewriting5
        , testNarrowing
        , testEquality ]

main = runTestTT tests


------------------------
-- The Terms dataType
------------------------
type PeanoT r = GTE Peano r

data Peano a = a :+ a
             | Succ a
             | Zero
    deriving (Eq, Ord, Show)

instance Enum (PeanoT r) where
   succ(x) = s(x)
--   pred(s(Succ x)) = x
   toEnum n = iterate succ z !! n

-- helper constructors
x +: y = TRS.s (x :+ y)
s = TRS.s . Succ
z = TRS.s Zero

instance Traversable Peano where
    traverse f Zero = pure Zero
    traverse f (Succ a) = Succ <$> f a
    traverse f (a :+ b) = (:+) <$> f a <*> f b

instance Functor Peano where
    fmap = fmapDefault
instance Foldable Peano where
    foldMap = foldMapDefault

instance RWTerm Peano where 
    matchTerm Zero Zero = Just []
    matchTerm (Succ x) (Succ y) = Just [(x,y)]
    matchTerm (a :+ b) (c :+ d) = Just [(a,c),(b,d)]
    matchTerm x y = Nothing

p (Succ _) = "succ"
p (_ :+ _) = "+"
p Zero     = "0"
----------------------------
-- a TRS 
----------------------------
peanoTRS = [  x +: s(y) :-> s(x +: y)
            , y +: z    :-> y         ]

(x,y) = (genVar 0, genVar 1)

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
fourNFull = runL (sndM2(narrowFull peanoTRS2) four)

fiveN = runL (sndM $ narrow1 peanoTRS2 (s(four)))
noNarrowFull' = runL (sndM2(narrowFull peanoTRS2) two)
noNarrow' = runL (sndM$ narrow1 peanoTRS2 two)

testNarrowing = TestList [ [s(s(s(s(z)))), s(s(z))] ~=? fourN1
                         , [s(s(s(s(z)))), s(s(z))] ~=? fourNFull 
                         , testAngryTerm
                         , testNarrowIssue
                         ]

-------------------------------
-- The TRS for testing narrowBU
-------------------------------
[f,g] = map term ["f","g"]
[a,b,c,d] = map constant (map unit "abcd")
    where unit x = [x]
          constant x = term x []
buTRS = [ f [b,c] :-> d
        , g [x]   :-> f [x,x]
        , a :-> b
        , a :-> c ]

angryTerm = f [x,x]
angryTermFull  = runL (sndM2(narrowFull buTRS) angryTerm)
angryTermFullv = runL (sndM2(narrowFullV buTRS) angryTerm)

testAngryTerm = TestLabel "Angry Term narrowing" $ 
                TestList [ angryTermFull  ~?= [] 
                      --   , angryTermFullv ~?= [c] 
                         ]

--------------------------
-- The narrow issues
--------------------------
u = ts(x + y)
narrowTrs = [ ts(cero) + y :-> ts(y)
            , ts(ts(cero)) + x :-> ts(ts(x))
            , cero + x :-> x 
            , x + cero :-> x]

u' = runE (sndM2(narrowFull narrowTrs) u >>= generalize)

-- This one uses the peano System. Tests narrowFullBounded, 
-- using the first step of Tp Forward, where the Interpretation is only
-- one equation long
tpForward1 = runL(sndM2(narrowFullBounded isNF [z +: x :-> x]) (s(x +: y)) >>= generalize)
    where isNF = (fmap null . runListT) . ((narrow1 peanoTRS =<<) . generalize)

tpBackward1 =runL(sndM(narrow1 (map swap peanoTRS) (s(z) +: x)) >>= generalize)


testNarrowIssue = TestLabel "Narrowing Issues" $ TestList 
        [ u' ~?= ts(ts(x)) 
        , tpForward1 ~?= [s(x)] 
        , runL(gsndM$narrow1 trs_x t) ~=? runL(gsndM$ narrow1 trs_y t) 
        , runL(gsndM$narrow1' trs_x' t') ~=? runL(gsndM$ narrow1' trs_y' t') 
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
--propNarrow' :: PeanoT r -> Bool
propNarrow' x = let
    aa = urunLIO$ sndM(narrow1 peanoTRS x) 
    bb = urunLIO$ sndM(narrow1' peanoTRS x)
    in (aa =|= bb)

a =|= b = a `intersect` b == a && b `intersect` a == b
{-
propNarrowDefinition x rules = and$ urunLIO$ do
               (theta, x') <- narrow1 rules x
               someM rules $ \(lhs:->rhs) -> do
                          (subst,lhs') <- autoInst lhs
                          unify lhs' x
                          rhs' <- instan subst rhs
                          return (rhstheta == 
-}
---------------------------------
-- Testing equality modulo vars 
---------------------------------

testEquality = TestLabel "test equality" $
               TestList [ -- x   ==  y    ~? "Eq modulo Vars"
                          s(x) == s(y)  ~? "With a context"
                        , x+y  == y+x   ~? "Same Name, but unrelated"
                        ]

--------------------------
-- Other properties
-------------------------
propDuplication1 t = and$ urunLIO$ do 
                        (vars,t1)   <- autoInst_ t 
                        (vars',_,t') <- lift$ dupTermWithSubst emptyS [] t1
                        return$ eqGT' t == eqGT' t' && eqGT' t1 == eqGT' t'
                        
    where types = (t::GT Peano RealWorld)

propDuplication2 t = and$ urunLIO$ do 
                        (vars,t1)   <- autoInst_ t 
                        (Subst vars',_,t') <- lift$dupTermWithSubst emptyS [] t1
                        mapM (\(MutVar r) -> write r (Just (eqGT z))) vars'
                        t'' <- col t'
                        return$ eqGT' t == eqGT' t1 


---------------
-- helpers
---------------
msg ==> assertion = TestLabel msg . TestCase $ assertion

sndM :: Functor m => m(a,b) -> m b
sndM = fmap snd

sndM2 = fmap2 snd
sndM3 = fmap3 snd

urunIO  = unsafePerformIO . runIO
urunLIO = unsafePerformIO . runLIO
urunEIO = unsafePerformIO . runEIO

gen x = x >>= generalize
gsndM = gen . sndM

infixl 0 ==>
infixl 2 ? 
infixl 2 =?

(?) = (Test.HUnit.@?)
(=?) = (Test.HUnit.@=?)

instance Arbitrary (PeanoT r) where
    arbitrary = 
            frequency [ (3,return z)
                      , (2,liftM2 (+:) arbitrary arbitrary)
                      , (2,liftM s arbitrary)
                      , (1,liftM genVar (choose (0,2)))]

