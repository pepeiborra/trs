{-# OPTIONS_GHC -fglasgow-exts -fno-mono-pat-binds #-}
{-# OPTIONS_GHC -fno-monomorphism-restriction #-}
{-# OPTIONS_GHC -fallow-undecidable-instances #-}

module Test where
import TRS.Core  hiding (collect)
import TRS.Types hiding (s)
import qualified TRS.Types as TRS
import TRS.Terms
import TRS.Utils
import Data.Char
import Data.Foldable
import Data.List (intersect)
import Data.Traversable
import Control.Applicative
import Control.Monad (guard, unless, replicateM)
import Control.Monad.List (ListT(..), liftM, liftM2, lift)
import Control.Monad.ST.Lazy (ST)
import Prelude hiding ( all, maximum, minimum, any, mapM_,mapM, foldr, foldl
                      , and, concat, concatMap, sequence, elem, notElem
                      , (+) )

import Test.HUnit
import Test.QuickCheck 
import Text.PrettyPrint
import Debug.Trace 
import System.IO.Unsafe
import GHC.Exts

tests = TestList
        [ testRewriting
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
-- Peano numbers
----------------------------
peanoTRS = [  x +: s(y) :-> s(x +: y)
            , y +: z    :-> y         ]

(x,y) = (genVar 0, genVar 1)

-------------------------
-- Testing Equality
-------------------------
propSemanticEquality :: Smart(PeanoT r) -> Bool
propSemanticEquality (Smart _ t) = let 
    vars_t   = vars (idGT t)
    new_vars = [ GenVar (succ i) | GenVar i<- vars_t]
    new_term = eqGT$ replaceAll (zip vars_t new_vars) (idGT t) 
    in new_term == t
--        where types = t :: PeanoT r

propRuleEquality :: Rule Peano r -> Rule Peano r -> Property
propRuleEquality t@(l1:->r1) s@(l2:->r2) = l1 == l2 && r1 == r2 ==> 
                                           equal_rule' t s

rule1 = x +: y :-> x
rule2 = x +: y :-> y

--------------------------
-- Some axioms in the framework
--------------------------

propGeneralize (PeanoClean t) = runST $ do
    newvars <- mkVarsForTerm t
    t'  <- instan_ newvars t
    t'' <- generalize t
    (idGT t') `equal_sem` (idGT t'')

--propAutoInstGeneralize 

propAutoInst1 (PeanoClean t) = (not$ null (vars t)) ==> collect (length$ vars t) $ runST (do
   (_,t1) <- autoInst_ t'
   (_,t2) <- run_autoInstG_ autoInst1 t'
   t1 `equal_sem` t2)
       where t' = idGT t

propAutoInstMutVars (PeanoClean t) = (not$ null (vars t)) ==> collect (length$ vars t) $ runST $ do
    (_,t1) <- autoInst_ t'
    return (noGVars t1)
        where t' = idGT t

propAutoInst1MutVars (PeanoClean t) = (not$ null (vars t)) ==> collect (length$ vars t) $ runST $ do
    (_,t1) <- run_autoInstG_ autoInst1 t'
    return (noGVars t1)
        where t' = idGT t
--------------------------
-- Testing Reductions
--------------------------
testRewriting = TestLabel "Test Rewriting" $ TestList
        [ testRewriting1
        , testRewriting2
        , testRewriting3
        , testRewriting4
        , testRewriting5
        , testRewNoRules ]

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

-- Corner cases
testRewNoRules = TestLabel "No Rules" $ runL (rewrite [] seven) ~?= []

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
angryTermFull  = runL (gen$ sndM2(narrowFull buTRS) angryTerm)
angryTermFullv = runL (sndM2(narrowFullV buTRS) angryTerm)

testAngryTerm = TestLabel "Angry Term narrowing" $ 
                TestList [ angryTermFull  ~?= [angryTerm] 
                      --   , angryTermFullv ~?= [c] 
                         ]

--------------------------
-- The narrow issues
--------------------------

isSNF rr = (fmap null . runListT') . ( (narrow1 rr =<<) . lift . generalize)

u = ts(x + y)
narrowTrs = [ ts(cero) + y :-> ts(y)
            , ts(ts(cero)) + x :-> ts(ts(x))
            , cero + x :-> x 
            , x + cero :-> x]

u' = runE (gen$ sndM2(narrowFull narrowTrs) u)

-- This one uses the peano System. Tests narrowFullBounded, 
-- using the first step of Tp Forward, where the Interpretation is only
-- one equation long
tpForward1 = runL(gen$ sndM2(narrowFullBounded (isSNF peanoTRS) [z +: x :-> x]) (s(x +: y)))

tpBackward1 =runL(gen$ sndM(narrow1 (map swap peanoTRS) (s(z) +: x)))


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

propNarrowFullNF x = urunIO(isSNF peanoTRS x) ==> narrowFull x == [x]
    where narrowFull x = urunLIO (sndM(TRS.Core.narrowFull peanoTRS x) )

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
-- 'macros'
x + y = term "+" [x,y]
cero = term "0" []
ts x = term "s" [x]

testEquality = TestLabel "test equality" $
               TestList [ -- x   ==  y    ~? "Eq modulo Vars"
                          s(x) == s(y)  ~? "With a context"
                        , x+y  == y+x   ~? "Same Name, but unrelated"
                        ]

--------------------------
-- Other properties
-------------------------
propDuplication1 :: PeanoClean -> Bool
propDuplication1 (PeanoClean t) = runST$ do 
                        (vars,t1)    <- autoInst t 
                        (vars',_,t') <- dupTermWithSubst emptyS [] (idGT t1)
                        return$ t == (eqGT t') && t1 == (eqGT t')

propDuplication2 (PeanoClean t) = runST$ do 
                        (vars,t1)   <- autoInst t 
                        (Subst vars',_,t') <- dupTermWithSubst emptyS [] (idGT t1)
                        mapM (\(MutVar r) -> write r (Just$ GenVar 1)) vars'
                        t'' <- col t'
                        return$ t == t1 


---------------
-- helpers
---------------
sndM :: Functor m => m(a,b) -> m b
sndM = fmap snd

sndM2 = fmap2 snd
sndM3 = fmap3 snd

urunIO  = unsafePerformIO . runIO
urunLIO = unsafePerformIO . runLIO
urunEIO = unsafePerformIO . runEIO

gen x = x >>= (lift . generalize)
gsndM = gen . sndM

infixl 2 ? 
infixl 2 =?

(?) = (Test.HUnit.@?)
(=?) = (Test.HUnit.@=?)

instance Arbitrary (PeanoT r) where
    arbitrary = arbitraryPeano (map genVar [0..2])
    shrink (S (a :+ b)) = [a,b]
    shrink x = []

arbitraryPeano [] =
            frequency [ (3,return z)
                      , (2,liftM2 (+:) (arbitraryPeano []) (arbitraryPeano []))
                      , (2,liftM s (arbitraryPeano [])) ]

arbitraryPeano vars =
            frequency [ (3,return z)
                      , (2,liftM2 (+:) (arbitraryPeano vars) (arbitraryPeano vars))
                      , (2,liftM s (arbitraryPeano vars))
                      , (1, elements vars)]

data PeanoClean = PeanoClean {peanoClean::forall r. PeanoT r}

mkPeanoClean :: PeanoT r -> PeanoClean
mkPeanoClean p = PeanoClean (fromFix(toFix p))

instance Arbitrary PeanoClean where
  arbitrary = arbitraryPeano (map genVar [0..2]) >>= \p -> 
              return (mkPeanoClean p)
  shrink (PeanoClean t) = map mkPeanoClean (shrink t)

instance Arbitrary (Rule Peano r) where
  arbitrary = arbitraryRule
  shrink (a :-> b) = (:->) <$> (shrink a) <*> (shrink b)

instance Show PeanoClean where
  show (PeanoClean t) = show t

--arbitraryRule :: (Arbitrary (GT_ eq s r), Eq (GT_ eq s r))
arbitraryRule = do
  l <- arbitrary
  r <- arbitraryPeano (vars l)
  return (l:->r)