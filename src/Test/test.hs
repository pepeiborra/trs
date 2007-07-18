{-# OPTIONS_GHC -fglasgow-exts -fno-mono-pat-binds #-}
{-# OPTIONS_GHC -fno-monomorphism-restriction #-}
{-# OPTIONS_GHC -fallow-undecidable-instances #-}

module Test.Test where
import Data.Char
import Data.Foldable hiding (elem)
import Data.List (intersect)
import Data.Maybe
import Data.Traversable
import Control.Applicative
import Control.Arrow hiding (pure)
import Control.Monad (guard, unless, replicateM, mplus, foldM)
import Control.Monad.Error (runErrorT)
import Control.Monad.List (ListT(..), liftM, liftM2, lift)
import Prelude hiding ( all, maximum, minimum, any, mapM_,mapM, foldr, foldl
                      , and, concat, concatMap, sequence, notElem
                      , (+) )

import Test.HUnit
import Test.QuickCheck ( Arbitrary(..), (==>), collect, elements
                       , frequency, Property, Smart(..), variant
                       , sized, CoArbitrary(..), oneof, Gen)
import Test.QuickCheck.Test
import Text.PrettyPrint
import Text.Show.Functions
import Debug.Trace 
import System.IO.Unsafe
import GHC.Exts

import qualified TRS.Core as Core
import TRS.Core hiding (narrow1', rewrite1, rewrite, narrow1, narrowFull, narrowFullBounded, run)
import TRS.Types hiding (s)
import qualified TRS.Types as TRS
import TRS.Term hiding (collect)
import qualified TRS.Term
import TRS.Terms
import TRS.Utils
import TRS.Signature
import TRS.Context

htests = TestList
        [ TestLabel "testRewriting" testRewriting
        , TestLabel "testNarrowing" testNarrowing
        , TestLabel "testEquality"  testEquality
        , testProperties qtests ] 

testProperties = TestList . map (uncurry (flip (~?)))

main   =  runTestTT htests
qtests = [("Semantic Equality", q propSemanticEquality)
         ,("Rule Equality"    , q propRuleEquality)
         ,("Generalize"       , q propGeneralize)
         ,("AutoInst Mutvars" , q propAutoInstMutVars)
         ,("AutoInstGMutvars" , q propAutoInstGMutVars)
         ,("Reimpl. collect"  , q propReCollect)
--         ,("Reimpl. vars"     , q propReVars)
         ,("Re. mutableTerm"  , q propReMutable)
         ,("Reimpl. semEq", q propReSemEq)
         ]
    where q = quickCheck'

------------------------
-- The Terms dataType
------------------------
type PeanoT = TermStatic Peano
type PeanoM r = GTE r Peano 

data Peano a = a :+ a
             | Succ a
             | Zero
    deriving (Eq, Ord)

prec_succ = 3
prec_plus = 1

instance Show x => Show (Peano x) where
  showsPrec p (Succ x) = showParen (p>prec_succ) $ 
                         ("s " ++ ) . showsPrec (succ prec_succ) x
  showsPrec p Zero     = ('0' : )
  showsPrec p (a :+ b) = showParen (p>prec_plus) 
                       $ showsPrec (succ prec_plus) a 
                       . (" + " ++) 
                       . showsPrec (succ prec_plus) b

instance Enum (PeanoT) where
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

instance TermShape Peano where 
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
peanoTRS = [ x +: s(y) :-> s(x +: y)
           , y +: z    :-> y        ]
peanoTRS'= [ s x +: y :-> s(x +: y)
           , z   +: y :-> y         ]

(x,y) = (Var 0, Var 1)

-------------------------
-- Testing Equality
-------------------------
propSemanticEquality :: Smart(PeanoT) -> Bool
propSemanticEquality (Smart _ t) = let 
    vars_t   = vars t
    new_vars = [ Var (succ i) | Var i<- vars_t]
    new_term = replace (zip vars_t new_vars) t
    in new_term == t
--        where types = t :: PeanoT

propRuleEquality :: Rule Peano -> Bool
propRuleEquality t@(l1:->r1) = t == t

rule1 = x +: y :-> x
rule2 = x +: y :-> y

--------------------------
-- Some axioms in the framework
--------------------------

propGeneralize t_ = runST (do
    t   <- mutableTerm t_
    t'  <- generalize_ t
    t `semEq` t')
        where types = t_ :: PeanoT

propAutoInstMutVars t =
  not(null (vars t)) ==> collect (length$ vars t) $ 
    runST (noGVars <$> mutableTerm t)
        where types = t :: PeanoT

propAutoInstGMutVars l r =
  not(null (vars l) && null (vars r)) ==> collect (length$ vars l ++ vars r) $ 
    runST (all noGVars <$> mutableTermG (l:->r))
        where types = l :: PeanoT

propAutoInstGMutVars2 l r =
  not(null (vars l) && null (vars r)) ==> collect (length$ vars l ++ vars r) $ 
    runST (do
       (_,[l,r]) <- autoInstG_ [templateTerm l, templateTerm r]
       return (isGT l)
       return (noGVars l))
        where types = l :: PeanoT
--------------------------------------
-- Proving reimplementations correct
--------------------------------------
propReCollect p_ f | p <- eqGT$ templateTerm p_ 
                   = (templateTerm <$> TRS.Term.collect f p_) == 
                     collect_ (f . fromJust . zonkTerm) p
       where types = p_ :: PeanoT
                  
-- | Ought to call colGT before this to make sure all the variables have
--   been dereferenced 
collect_   :: Foldable s  => (GT_ eq r s -> Bool) -> GT_ eq r s -> [GT_ eq r s]
collect_ p (S x) = foldr (\t gg -> collect_ p t ++ gg) [] x
collect_ p x = if p x then [x] else []
{-
prop_autoInst p = runST (do
    let p' = templateTerm p
    (s1,p1) <- autoInst_ p' 
    (s2,p2) <- autoInst_old p'
    return (idGT p1 == p2 {-TODO && s1 == s2-}))
-}
-- autoInst_old :: TermShape s => GT r s -> ST r (Subst r s, GT r s)
autoInst_old x@MutVar{} = return (emptyS, x)
autoInst_old x
    | null gvars = return (emptyS, x)
    | otherwise  = do
           freshv <- fmap (Subst . reverse) $ 
                    foldM (\rest gv -> liftM (:rest) $
                             if gv`elem`gvars then fresh else return gv) 
                          []
                          (map GenVar [0..succ n_newvars])
           x' <- instan_ freshv x 
--           assert (noGVars x') (return ())
           x' `seq` return (freshv, x')
    where gvars = TRS.Term.collect isGenVar x
          n_newvars :: Int
          n_newvars = maximum [ n | GenVar n <- [GenVar 10]]

propReMutable p = runST (do
  p1 <- mutableTerm p
  p2 <- mutableTerm' p
  (p1 `semEq` p2))
        where types = p :: PeanoT

--mutableTerm' :: (TermShape s, Functor s) => TermStatic s -> ST r (GT r s)
mutableTerm' = (snd <$>) . autoInst_ . templateTerm' 


--templateTerm' :: Functor s =>  TermStatic s -> GT r s -- PEPE be careful with equality
templateTerm' (Term x) = S(templateTerm' <$> x)
templateTerm' (Var n)  = GenVar n


{- TODO: prove all these

autoInstG_ = run_autoInstG_ (mapM autoInst1)
autoInstGG_ = run_autoInstG_ (mapM2 autoInst1)

run_autoInstG_ autoInst1 = fmap swap . (emptyS `runStateT`) . autoInst1 
  where 
   swap (a,b) = (b,a)
   autoInst1 x = do
           freshv <- createFreshs x
           lift$ instan_ freshv x
     where createFreshs t | null vars_t = get 
                          | otherwise   = do
             freshv <- gets subst
             let have_enough_vars = (topIndex `atLeast` freshv)
             unless have_enough_vars $ do
                extra_freshv <- replicateM (topIndex - length freshv + 1) 
                                           (lift fresh)
                put (Subst$ freshv ++ extra_freshv)
             get
               where
                  vars_t = vars t
                  topIndex = maximum [ i | GenVar i <- vars_t ]


propAutoInst1 t_ =
  not (null (vars t)) ==> collect (length$ vars t) $ runST (do
   (_,t1) <- autoInst_ t'
   (_,t2) <- run_autoInstG_ autoInst1 t'
   t1 `semEq` t2)
       where t  = templateTerm t_
             t' = idGT t

propAutoInst1MutVars t =
  not(null (vars t)) ==> collect (length$ vars t) $
    runST (noGVars . snd <$> run_autoInstG_ autoInst1 (templateTerm t))


--equal_rule :: TermShape s => RuleI r s -> RuleI r s -> ST r Bool
equal_rule s1 s2 = fmap(either (return False) id) $ runErrorT$ do
   (theta1, l1:->r1) <- lift$ autoInstG_ (fmap idGT s1)
   (theta2, l2:->r2) <- lift$ autoInstG_ (fmap idGT s2)
   unify_ l1 l2 >> unify_ r1 r2
   lift$ isARenaming (subst theta1) &>& allM isEmptyVar (subst theta2)
   where (&>&) = liftM2 (&&)
         isARenaming = allM (\(MutVar m) -> readVar m >>= 
                       return . maybe True (not . isTerm))
-}


-- |Semantic equality (equivalence up to renaming of vars) 
semEq_old :: (TermShape s) => GT r s -> GT r s -> ST r Bool
semEq_old x y = fmap (either (return False) id) $ runErrorT $ do
    (theta_x, x') <- lift$ autoInst_ x
    (theta_y, y') <- lift$ autoInst_ y
    unify_ x' y'
    theta_x' <- lift (mapM col theta_x) 
    theta_y' <- lift (mapM col theta_y)
    return (none isTerm theta_x' && none isTerm theta_y')
  where none = (not.) . any

propReSemEq s t | False, Var _ <- s = undefined
propReSemEq s t = 
       (s == t) == runST(templateTerm s `semEq_old` templateTerm t)
        where types = (s :: PeanoT, t :: PeanoT)
{-
propReSemEq s t = runST$ do
    let [n_s, n_t] = map (length . collect isGenVar) [s,t]
    v_s <- vector n_s
    v_t <- vector n_t
    let _ = catMaybes v_t ++ catMaybes v_s 
    s' <- instan (v_s) s
    t' <- instan (v_t) t
    return (
         s  `semEq` t  == s  `semEq_old` t &&
         s' `semEq` t' == s' `semEq_old` t' &&
         s  `semEq` s' == s  `semEq_old` s' &&
         t  `semEq` t' == t  `semEq_old` t')
-}
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

seven' = rewrite1 peanoTRS seven
eight' = rewrite1 peanoTRS (seven +: s(z))

-- One Step rewriting
testRewriting1 = [s(s(s(z)) +: s(s(s(s(z)))))] ~=? seven'
testRewriting2 = TestLabel "One step" $ TestList 
 [ length eight' ~=? 2 
 , (s(seven +: z) `elem` eight') ~? "2"
 , ((s(s(s(z)) +: s(s(s(s(z))))) +: s(z)) `elem` eight') ~? "3" ]

-- Normal Rewriting
testRewriting3 = Just (s(s(five)))    ~=? rewrite peanoTRS (seven)
testRewriting4 = Just (s(s(s(five)))) ~=? rewrite peanoTRS (seven +: s(z))

-- Non confluent rewriting
sillyRules = [ z :-> s(z), z :-> s(s(z)) ]

testRewriting5 = test (assert True) --TODO

-- Corner cases
testRewNoRules = TestLabel "No Rules" $ rewrite [] seven ~?= [seven]

-- Testing Narrowing
peanoTRS2 = [ s(s(z)) +: s(x) :-> s(s(s(x)))
             , z +: s(x) :-> s(x)
            ]

four = y +: s(s(z))

fourN1 = snd `map` narrow1 peanoTRS2 four
--fourNFix = runL (fixM (fmap snd $ narrow1 peanoTRS2) four)
fourNFull = snd `map` narrowFull peanoTRS2 four 

fiveN = snd `map` narrow1 peanoTRS2 (s(four))
noNarrowFull' = snd `map` narrowFull peanoTRS2 two
noNarrow' = snd `map` narrow1 peanoTRS2 two

testNarrowing = TestList [ [s(s(s(s(z)))), s(s(z))] ~=? fourN1
                         , [s(s(s(s(z)))), s(s(z))] ~=? fourNFull 
                         , [] ~=? noNarrow'
                         , [] ~=? noNarrowFull'
                         , testAngryTerm
                         , testNarrowIssue
                         , snd <$> narrow1 [g (g x) :-> x] (f (g x) x) ~?= [f x (g x)]
                         ]

-------------------------------
-- The TRS for testing narrowBU
-------------------------------
f = term2 "f"
g = term1 "g"
h = term1 "h"
[a,b,c,d] = map constant (map unit "abcd")
    where unit x = [x]
          constant x = term x []
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
         . ( (Core.narrow1 rr =<<) . lift . generalize_)
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


testNarrowIssue = TestLabel "Narrowing Issues" $ TestList 
        [ u' ~?= [ts(ts(x))]
        , tpForward1 ~?= [s(x)] 
        , snd <$> narrow1 trs_x t ~=? (snd <$> narrow1 trs_y t :: [PeanoT])
        , snd <$> narrow1' trs_x' t' ~=? snd <$> narrow1' trs_y' t'
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
propNarrow' x = let
    aa = snd <$> narrow1  peanoTRS x
    bb = snd <$> narrow1' peanoTRS x
    in (aa =|= bb)

propNarrowFullNF x = isSNF peanoTRS x ==> (snd <$> narrowFull peanoTRS x) == [x]

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
-----------------------------------------------
-- Verifying the new implementation of contexts
-----------------------------------------------
contexts' (S t) = --(CtxVar 0, S t) : 
                 catMaybes (map (context (S t) c) [0..size t - 1])
    where c = (length . TRS.Term.collect isCtxVar) (S t)
--          context :: Traversable t => GT t r -> Int -> Int -> Maybe (GT t r,Context t r)
          context (S t) depth i 
             | (a, t') <- first (msum . toList) . unzipG $
                        fmap (\(j,u)->if i==j && not (isCtxVar u) 
                                       then (Just u, CtxVar depth) 
                                       else (Nothing,u)) 
                             (unsafeZipG [0..] t)
             = a >>= \a'->return (a',S t')   -- in the Maybe monad
contexts' _ = []


propContexts :: PeanoT -> Bool
propContexts t_ = contexts' t == contexts t
    where t = idGT$ templateTerm t_

 -- REVIEW these properties
propCIdentity, propCTransiti :: PeanoT -> Bool
propCIdentity x_ = and [ ct|>y == x | (y,ct) <- contexts x ]
  where x = idGT$ templateTerm x_

propCTransiti x_ = and [ ct|>y|>y1 == x | (y1,ct1) <- contexts x
                                         , (y,ct) <- contexts ct1]
  where x = idGT$ templateTerm x_ 

--------------------------
-- Other properties
-------------------------
propDuplication1, propDuplication2 :: PeanoT -> Bool
propDuplication1 t = runST (do 
                        t1           <- mutableTerm t 
                        (vars',_,t') <- dupTermWithSubst emptyS [] (idGT t1)
                        Just t''     <- zonkTerm <$> col t'
                        return$ t == t'' && t1 `semEq'` t')

propDuplication2 t = runST (do 
                        t1   <- mutableTerm t 
                        (Subst vars',_,t') <- dupTermWithSubst emptyS [] (idGT t1)
                        mapM (\(MutVar r) -> write r (Just$ GenVar 1)) vars'
                        Just t'' <- zonkTerm <$> col t' 
                        return$ t == t'')

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

-- ----------------
-- Generators
-- ----------------
instance Arbitrary (PeanoT) where
    arbitrary = sized$ arbitraryPeano (map Var [0..2])
    shrink (Term (a :+ b)) = [a,b]
    shrink x = []

instance CoArbitrary PeanoT where
    coarbitrary (Var i)  = variant 0 . coarbitrary i
    coarbitrary (Term f) = variant 1 . coarbitrary (toList f)

arbitraryPeano [] 0   = return z
arbitraryPeano vars 0 = frequency [(1,return z), (1, elements vars)]
arbitraryPeano vars size | size2 <- size `div` 2 =
  frequency [ (2,liftM2 (+:) (arbitraryPeano vars size2) (arbitraryPeano vars size2))
            , (2,liftM s (arbitraryPeano vars size))]


instance Arbitrary (Rule Peano) where
  arbitrary = arbitraryRule
  shrink (a :-> b) = (:->) <$> (shrink a) <*> (shrink b)

--arbitraryRule :: (Arbitrary (GT_ eq r s), Eq (GT_ eq r s))
arbitraryRule = do
  l <- arbitrary
  r <- sized$ arbitraryPeano (vars l)
  return (l:->r)

arbitraryLLCS sig size = do
  Symbol f arity <- elements (defined sig)
  lhs <- term f <$> replicateM arity ( 
                       oneof [var <$> arbitrary
                             ,arbitraryTerm (constructors sig) size])
  rhs <- arbitraryTerm (defined sig ++ constructors sig) size
  return (lhs :-> rhs)

arbitraryTerm :: [Symbol String] -> Int -> Gen TRS.Types.Term
arbitraryTerm sig 0 = Var <$> arbitrary
arbitraryTerm sig size = do 
  Symbol c arity <- elements sig
  term c <$> replicateM arity 
                 (oneof [var <$> arbitrary
                        ,arbitraryTerm sig size2])
      where size2 = size `div` 2