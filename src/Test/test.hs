{-# OPTIONS_GHC -fglasgow-exts -fno-mono-pat-binds #-}
{-# OPTIONS_GHC -fno-monomorphism-restriction #-}
{-# OPTIONS_GHC -fallow-undecidable-instances #-}
{-# LANGUAGE  DisambiguateRecordFields #-}

module Test.Test where
import Data.Char
import Data.Foldable hiding (elem)
import Data.List (intersect)
import Data.Maybe
import Data.Traversable
import Control.Applicative
import Control.Arrow hiding (pure)
import Control.Monad (guard, unless, replicateM, mplus, foldM, zipWithM)
import Control.Monad.Error (runErrorT)
import MaybeT (runMaybeT)
import Control.Monad.List (ListT(..), liftM, liftM2, lift)
import Prelude hiding ( all, maximum, minimum, any, mapM_,mapM, foldr, foldl
                      , and, concat, concatMap, sequence, notElem
                      , (+) )

import Test.HUnit
import Test.QuickCheck ( Arbitrary(..), (==>), collect, elements
                       , frequency, Property, Smart(..), variant
                       , sized, CoArbitrary(..), oneof, Gen, forAll)
import Test.QuickCheck.Test
import Text.PrettyPrint
import Text.Show.Functions
import Debug.Trace 
import System.IO.Unsafe
import GHC.Exts

import TRS hiding (collect, semEq)
import qualified TRS
import TRS.Core hiding (run, narrowFull, narrowFullBounded)
import qualified TRS.Core as Core
import TRS.Utils
import TRS.Signature
import TRS.Context
import TRS.GTerms
import TRS.Tyvars

import Test.Peano
import Test.TermRef

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
         ,("AutoInstGMutvars2" , q propAutoInstGMutVars2)
         ,("zonkSubst"        , q propZonkSubst)
         ,("Reimpl. collect"  , q propReCollect)
--         ,("Reimpl. vars"     , q propReVars)
         ,("Re. mutableTerm"  , q propReMutable)
         ,("Reimpl. semEq", q propReSemEq)
         ,("Full Narrowing Normal Forms", q propNarrowFullNF)
         ,("Reimpl. contexts" , q propContexts)
         ,("Contexts Identity", q propCIdentity)
         ,("Contexts Transitivity", q propCTransiti)
         ,("dup(t) == t", q propDuplication1)
         ]
    where q = quickCheck'

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

--------------------------
-- Some axioms in the framework
--------------------------

propZonkSubst subst_ = runST (do
    subst  <- templateGT'  `mapM` subst_
    subst' <- zonkSubst subst
    and <$> sequence (semEq <$> subst <*> subst'))
     where types = subst_ :: SubstM PeanoT
            
propGeneralize (Refs t_) = runST (do
    t   <- mutableTerm t_
    t'  <- generalize t
    t `semEq` t')
        where types = t_ :: PeanoT

propAutoInstMutVars (Refs t) =
  not(null (vars t)) ==> collect (length$ vars t) $ 
    runST (noGVars <$> mutableTerm t)
        where types = t :: PeanoT

propAutoInstGMutVars (Refs l) (Refs r) =
  not(null (vars l) && null (vars r)) ==> collect (length$ vars l ++ vars r) $ 
    runST (all noGVars <$> mutableTermG (l:->r))
        where types = l :: PeanoT

propAutoInstGMutVars2 (Refs l) (Refs r) =
  not(null (vars l) && null (vars r)) ==> collect (length$ vars l ++ vars r) $ 
    runST (do
       (_,[l,r]) <- autoInstG [templateTerm l, templateTerm r]
       return (noGVars (isGT l)))
        where types = l :: PeanoT
--------------------------------------
-- Proving reimplementations correct
--------------------------------------
propReCollect (Refs p_) f | p <- idGT$ templateTerm p_ 
                   = (templateTerm <$> TRS.collect f p_) == 
                     collect_ (f . fromJust . zonkTerm) p
       where types = p_ :: PeanoT
                  
-- | Ought to call colGT before this to make sure all the variables have
--   been dereferenced 
collect_   :: Foldable s  => (GT_ user eq r s -> Bool) -> GT_ user eq r s -> [GT_ user eq r s]
collect_ p (S x) | p (S x) = S x : concatMap (collect_ p) x -- foldr (\t gg -> collect_ p t ++ gg) [] x
collect_ p (S x) = concatMap (collect_ p) x -- foldr (\t gg -> collect_ p t ++ gg) [] x
collect_ p x = if p x then [x] else []
{-
prop_autoInst p = runST (do
    let p' = templateTerm p
    (s1,p1) <- autoInst_ p' 
    (s2,p2) <- autoInst_old p'
    return (idGT p1 == p2 {-TODO && s1 == s2-}))
-}
-- autoInst_old :: TermShape s => GT user r s -> ST r (Subst r s, GT user r s)
autoInst_old x@MutVar{} = return (emptyS, x)
autoInst_old x
    | null gvars = return (emptyS, x)
    | otherwise  = do
           freshv <- fmap (Subst . reverse) $ 
                    foldM (\rest gv -> liftM (:rest) $
                             if gv`elem`gvars then fresh else return gv) 
                          []
                          (map genVar [0..succ n_newvars])
           x' <- instan freshv x 
--           assert (noGVars x') (return ())
           x' `seq` return (freshv, x')
    where gvars = TRS.collect isGenVar x
          n_newvars :: Int
          n_newvars = maximum [ n | GenVar{unique=n} <- [genVar 10]]  --- ?????

propReMutable (Refs p) = runST (do
  p1 <- mutableTerm p
  p2 <- mutableTerm_old p
  (p1 `semEq` p2))
        where types = p :: PeanoT

--mutableTerm' :: (TermShape s, Functor s) => TermStatic s -> ST r (GT user r s)
mutableTerm_old = (snd <$>) . autoInst . templateTerm_old


--templateTerm' :: Functor s =>  TermStatic s -> GT user r s -- PEPE be careful with equality
templateTerm_old (Term x) = S(templateTerm_old <$> x)
templateTerm_old (Var n)  = genVar n
templateTerm_old (Ref x)  = templateTerm_old x

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
semEq_old :: (GoodShape s) => GT user r s -> GT user r s -> ST r Bool
semEq_old x y = fmap (either (return False) id) $ runErrorT $ do
    (theta_x, x') <- lift$ autoInst x
    (theta_y, y') <- lift$ autoInst y
    unify x' y'
    theta_x' <- lift (mapM col theta_x) 
    theta_y' <- lift (mapM col theta_y)
    return (none (fromMaybe False . fmap isTerm) (fromSubstM theta_x') && 
            none (fromMaybe False . fmap isTerm) (fromSubstM theta_y'))
  where none = (not.) . any

semEq_old' :: (GoodShape s) => GT user r s -> GT user r s -> ST r Bool
semEq_old' x y = do
    (_,x') <- second idGT <$> autoInst x
    (_,y') <- second idGT <$> autoInst y
    let xy_vars = TRS.collect isMutVar x' ++ TRS.collect isMutVar y'
    runMaybeT $ unify x' y'
    mapM col xy_vars
    andM [ (maybe True isVar <$> readVar v)
                       | MutVar{ref=v} <- xy_vars]


propReSemEq1 (Refs s) (Refs t) | False, Var _ <- s = undefined
propReSemEq1 (Refs s') (Refs t') = runST $ do
       let [s,t] = map templateTerm [s',t']
       new <- s  `semEq` isGT t
       old <- s `semEq_old'` t
       return $ new == old
        where types = (s' :: PeanoT, t' :: PeanoT)

propReSemEq (Refs s) (Refs t) | False, Var _ <- s = undefined
propReSemEq (Refs s') (Refs t') = runST $ do
       let [s,t] = map templateTerm [s',t']
       new <- s  `semEq` isGT t
       old <- s `semEq_old` t
       return $ new == old
        where types = (s' :: PeanoT, t' :: PeanoT)

testSemEq (Refs s) (Refs t) | False, Var _ <- s = undefined
testSemEq (Refs s') (Refs t') = runST $ do
       let [s,t] = map templateTerm [s',t']
       new <- s  `semEq` isGT t
       return new
        where types = (s' :: PeanoT, t' :: PeanoT)

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

----------------------------
-- Peano numbers
----------------------------
peanoTRS = [ x +: s(y) :-> s(x +: y)
           , y +: z    :-> y        ]
peanoTRS'= [ s x +: y :-> s(x +: y)
           , z   +: y :-> y         ]

x :: forall s. TermRef s
x = Var 0
y = Var 1

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
two   = s(s(z)) :: PeanoT
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
testRewNoRules = TestLabel "No Rules" $ 
                 (rewrite ([] :: [RuleS Peano]) seven) ~?= [seven]
  
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
                         , [two] ~=? noNarrowFull'
                         , testAngryTerm
                         , testNarrowIssue
                         , snd <$> narrow1 [g (g x) :-> x] (f (g x) x) ~?= 
                                                                       [f x (g x)]
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


testNarrowIssue = TestLabel "Narrowing Issues" $ TestList 
        [ Semantic u'         ~?= Semantic [ts(ts(y)),ts(ts(ts(y))),ts(y),ts(x)]
        , Semantic tpForward1 ~?= Semantic [s(x)] 
        , Semantic . snd <$> narrow1 trs_x t 
                              ~=? (Semantic . snd <$> narrow1 trs_y t :: [Semantic PeanoT])
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
                     (snd <$> narrowFull peanoTRS x) == [x]
       where types = (x :: PeanoT)

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
                          s(x) `TRS.semEq` s(y)  ~? "With a context"
                        , (x+y)  `TRS.semEq` (y+x)   ~? "Same Name, but unrelated"
                        ]
-----------------------------------------------
-- Verifying the new implementation of contexts
-----------------------------------------------
contexts' (S t) = --(CtxVar 0, S t) : 
                 catMaybes (map (context (S t) c) [0..size t - 1])
    where c = (length . TRS.collect isCtxVar) (S t)
--          context :: Traversable t => GT user t r -> Int -> Int -> Maybe (GT user t r,Context t r)
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
propDuplication1 :: PeanoT -> Bool
propDuplication1 t = runST (do 
                        t1           <- mutableTerm t 
                        (vars',_,t') <- dupTermWithSubst emptySubstM [] (idGT t1)
                        t''          <- zonkTerm' =<< col t'
                        semeq        <- t1 `semEq` t'
                        return$ t == t'' && semeq )
                             
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