{-# OPTIONS_GHC -fglasgow-exts #-}
{-# OPTIONS_GHC -fallow-undecidable-instances #-}
{-# OPTIONS_GHC -fallow-overlapping-instances #-}
module TRS.Term where


import Control.Applicative
import Control.Arrow (first, second) 
import Control.Monad hiding ( mapM, sequence )
import Control.Monad.State (gets, modify, evalState, MonadTrans(..))
import Control.Monad.Identity (runIdentity)
import MaybeT (MaybeT(..))
import Data.List (nub, nubBy, elemIndex)
import Data.Foldable (toList, Foldable)
import Data.Maybe (fromMaybe, fromJust, catMaybes)
import Data.Traversable (Traversable, mapM, sequence)
import Prelude hiding (mapM, sequence)
import qualified Prelude

import TypeCastGeneric

import {-# SOURCE#-} TRS.Core   hiding ( semEq )
import {-# SOURCE#-} qualified TRS.Core as Core
import {-# SOURCE#-} TRS.GTerms
import {-# SOURCE#-} TRS.Rules
import TRS.Tyvars
import TRS.Types
import TRS.Substitutions
import TRS.Utils

-- ---------------------------------------
-- * The class of terms
-- ----------------------------------------
class (TermShape s, Eq (t s)) => Term (t :: (* -> *) -> *) (s :: * -> *) (user :: *) | t -> user where
        isVar        :: t s -> Bool
        mkVar        :: Int -> t s
        varId        :: t s -> Maybe Int
        contents     :: t s -> Maybe (s(t s))
        build        :: s(t s) -> t s
--        mkGT mkVar t = runST (runIdentityT (mkGTM (return . mkVar) t))
        toGTM        :: (Monad m, Traversable m) => 
                        (forall r. t s -> m(GT_ user eq r s)) -> 
                            t s -> ST r (m(GT_ user eq r s))
        toGTM        = defaultToGTM
        fromGTM      :: (Term t s user, Monad m) => 
                        (Mutable (GT_ user md r s) -> m (t s)) -> 
                        GT_ user md r s -> ST r (m(t s))
        fromGTM      = defaultFromGTM

term :: Term t BasicShape user => String -> [t BasicShape] -> t BasicShape
term = (build.) . T
term1 f t       = term f [t]
term2 f t t'    = term f [t,t']
term3 f t t' t''= term f [t,t',t'']
constant f      = term f []

var :: Term t BasicShape user => Int -> t BasicShape
var  = mkVar 

defaultFromGTM ::  (Term t s user, Monad m) => 
                        (Mutable (GT_ user md r s) -> m (t s)) -> 
                            GT_ user md r s -> ST r (m(t s))
defaultFromGTM mkVar (S y) = build `liftMM` ((liftMM sequence . mapM) 
                                              (fromGTM mkVar) y)
defaultFromGTM mkVar MutVar{ref=ref} = do
  var <- readVar' ref
  return (mkVar var)
defaultFromGTM mkVar var = return . return . fromJust $ zonkVar var 

toGT :: Term t s user => (forall r. t s -> GT_ user eq r s) -> t s -> GT_ user eq r s
toGT mkVar t | isVar t = mkVar t
             | otherwise
             = S (toGT mkVar `fmap` fromMaybe (error "defaultToGT")
                                              (contents t))
             

defaultToGTM :: (Term t s user, Monad m, Traversable m) => 
                (forall r. t s -> m(GT_ user eq r s)) -> t s -> ST r (m(GT_ user eq r s))
defaultToGTM mkV t 
    | not (isVar t) 
    = S `liftMM` ((liftMM sequence . mapM) (toGTM mkV) 
                                           (fromMaybe (error "defaultToGTM")
                                            (contents t)))
    | otherwise = return(mkV t)

fromSubTerms :: Term t s user => t s -> [t s] -> t s
fromSubTerms t tt = -- build$ modifySpine (fromMaybe (error "fromSubTerms") $ contents t) tt
                    liftTerm (`modifySpine` tt) t

subTerms, children :: Term t s user => t s -> [t s]
subTerms = fixM children
children = fromMaybe [] . fmap toList . contents

liftTerm    ::(Term t s user) => (s (t s) -> s (t s)) -> t s -> t s
liftTerm f t = maybe t (build . f) . contents $ t

liftTermM    ::(Term t s user, Monad m) => (s (t s) -> m( s (t s))) -> t s -> m(t s)
liftTermM f t = maybe (return t) (liftM build . f) . contents $ t

applySubst   :: Term t s user => SubstM (t s) -> t s -> t s
applySubst sm t = s `seq` mutateTerm f t where 
     s = fromSubstM sm
     f t' | Just i <- varId t', i`inBounds` s, Just v <- s !! i = v
          | otherwise = mutateTerm f t'

mutateTerm f t  | Just tt <- contents t = build $ fmap f tt
                | otherwise = t
mutateTermM f t | Just tt <- contents t = build <$> mapM f tt
                | otherwise = return t
  
-- TODO: TEST THAT THIS RULE FIRES
{-# RULES "castTerm/identity" castTerm = id #-}

castTerm :: forall t1 t2 s user . 
            (Term t1 s user, Term t2 s user) => t1 s -> t2 s
castTerm t = runST(templateGT' t >>= zonkTerm')


class Term t s user => TRS t s m user where
        rewrite      :: Term t1 s user => [Rule t1 s] -> t s -> m(t s)
        unify        :: t s -> t s -> m(SubstM (t s))
        rewrite1     :: Term t1 s user => [Rule t1 s] -> t s -> m(t s)
        narrow1      :: Term t1 s user => [Rule t1 s] -> t s -> m(SubstM(t s), t s)

class Term t s user => TRSN t s user where
--        narrow1'     :: Term t1 s => [Rule t1 s] -> t s -> [(SubstM(t s), t s)]
        narrowFull   :: Term t1 s user => [Rule t1 s] -> t s -> [(SubstM(t s), t s)]
        -- | Basic Narrowing
        narrowBasic  :: Term t1 s user => [Rule t1 s] -> t s -> [(SubstM(t s), t s)]
        -- | Full Narrowing restricted by a predicate.
        --   Stops as soon as the predicate is positive or the 
        --   derivation finishes
        narrowFullBounded :: Term t1 s user => (t s -> Bool) -> [Rule t1 s] -> t s 
                                    -> [(SubstM(t s), t s)]

{-
instance (TermShape s, Traversable s) => Term (s a) where
  isVar _      = False
  contents     = toList
  synEq x y    = Just True == (all (uncurry synEq) <$> matchTerm x y)
  fromSubTerms = modifySpine
-}
vars :: Term t s user => t s -> [t s]
vars t | isVar t   = [t]
       | Just tt <- toList <$> contents t 
                   = nub (vars =<< tt)
       | otherwise = []

collect :: Term t s user => (t s -> Bool) -> t s -> [t s] 
collect pred t | Just tt <- toList <$> contents t
               = nub ([t' | t' <- t : tt, pred t'] ++
                              concatMap (collect pred) tt)
               | otherwise = filter pred [t]

{-
-- * Syntactic equality
newtype SynEqTerm (t :: (* -> *) -> *) s = SynEq {unSynEq::t s} --deriving Show
instance Term t s user => Eq (SynEqTerm t s) where SynEq t1 == SynEq t2 = t1 `synEq` t2

instance Show (t s) => Show (SynEqTerm t s) where 
    showsPrec p (SynEq t) = ("SynEqTerm " ++) . showsPrec p t
-}
-- | Replace (syntactically) subterms using the given dictionary
--   Do not confuse with substitution application. @replace@ makes no 
--   effort at avoiding variable capture
--   (you could deduce that from the type signature)
replace :: (Term t s user) => [(t s,t s)] -> t s -> t s
replace []   = id
replace dict = fromJust . go 
  where 
    go t  = lookup t dict 
            `mplus` 
            mutateTermM go t
     
-- ¿mutateTermM en Maybe no debería fallar con un Nothing? 
-- No falla, porque, viendo un termino como un arbol,
--  go siempre tiene éxito en las hojas, y por induccion en
--  todos los nodos 

--------------------------------------------------------------------------
-- * Semantic Equality
--------------------------------------------------------------------------
newtype Semantic (t :: (* -> *) -> *) (s :: * -> *) = Semantic {semantic :: t s} 

instance Show (t s) => Show (Semantic t s) where show (Semantic a) = show a

instance Term t s user => Eq (Semantic t s) where
    Semantic a == Semantic b = a `semEq` b

instance Term t s user => Term (Semantic t) s user where
  varId = varId . semantic
  mkVar = Semantic . mkVar
  isVar = isVar . semantic
  contents = fmap2 Semantic . contents . semantic
  build = Semantic . build . fmap semantic

instance (Ord (t s), Term t s user) => Ord (Semantic t s) where
  compare (Semantic a) (Semantic b) = compare a b

--instance TermShape s => Eq (TermStatic s) where
semEq :: (Term t s user, TermShape s) => t s -> t s -> Bool
t1 `semEq` t2 = runST (do
   [t1',t2'] <- mapM templateTerm' [t1,t2]
   return (isGT t1')
   t1' `Core.semEq` t2')

--------------------------------------------------------------------------
-- * Out and back of GT, purely
--------------------------------------------------------------------------
-- | Tries to return a term without mut. vars, fails if it finds any mut var.
zonkTerm :: Term t s user => GT_ user mode r s -> Maybe (t s)
zonkTerm = zonkTermWith zonkVar

zonkTermUnsafe :: (Term t s user, Term (GT_ user mode r) s user) => 
                  GT_ user mode r s -> t s
zonkTermUnsafe t = 
  let mvars        = [r | MutVar{ref=r} <- collect isMutVar t]
      n_gvars      = length$ collect isGenVar t
      f MutVar{ref=r} = Just$ mkVar (fromJust(elemIndex r mvars) + n_gvars)
      f v = zonkVar v
   in fromJust $ zonkTermWith f t

zonkTermWith zvar (S tt) = build <$> (zonkTermWith zvar `mapM` tt)
zonkTermWith zvar var   = zvar var



-- | Replaces any mut. var with its current substitution, or a (clean) GenVar if none
zonkTerm' :: (Prune mode, Term (GT_ user mode r) s user, Term t s user) => 
             GT_ user mode r s -> ST r (t s)
zonkTerm' t = do
  t' <- col t
  let mvars        = collect isMutVar t'
      n_gvars      = length$ collect isGenVar t'
  mvars_indexes <- catMaybes <$> forM mvars (getUnique . ref)
  let skolem_offset = n_gvars + maximum (0:mvars_indexes)
  forM mvars $ \m@MutVar{ref=v, note_=n} -> 
       readVar' v >>= \x -> case x of
            Empty Nothing -> writeVar v (Skolem n $ 
                                      fromJust(elemIndex m mvars) + skolem_offset)
            Empty (Just i)-> writeVar v (GenVar n i)
            Mutable{}-> return ()
  runIdentity <$> fromGTM f t'
  where f = return . mkVar . fromJust . varUnique
{-
zonkTermWithM :: (Prune mode, Term t s user, Term (GT_ user mode r) s) => 
                (forall a. Mutable a -> ST r (t s)) ->
                GT_ user mode r s -> ST r (t s)
zonkTermWithM f t = do
  t' <- col t
  let mvars        = [r | MutVar r <- collect isMutVar t]
      n_gvars      = length$ collect isGenVar t
  mvars_indexes <- catMaybes <$> forM mvars getUnique
  let skolem_offset = n_gvars + maximum (0:mvars_indexes)
  forM mvars $ \v -> 
       readVar' v >>= \x -> case x of
            Skolem _ -> writeSTRef v (Skolem $
                                   (skolem_offset +) <$> elemIndex v mvars)
            Empty i  -> write v (GenVar i)
            Mutable{}-> return ()
  join (fromGTM f t')
-}

zonkVar :: Term t s user => GT_ user mode r s -> Maybe (t s)
zonkVar (MutVar _ r) = Nothing -- error "zonkTerm: No vars" 
zonkVar (GenVar _ n) = Just $ mkVar n
zonkVar (CtxVar n)   = Just $ mkVar n
zonkVar (Skolem _ n) = Just $ mkVar n
zonkVar x = seq x $ error "ouch!: zonkVar" 


-- | Fails on terms with skolems. What should it do?
templateTerm :: Term t s user => t s -> GT_ user mode r s
templateTerm = toGT (genVar . fromMaybe (error "templateTerm: variable with no id"). varId)


templateTerm' :: Term t s user => t s -> ST r (GT_ user mode r s)
templateTerm' = fmap fromJust -- Identity is not Traversable ^.^
              . toGTM (return . maybe (skolem 0) genVar . varId)

templateGT' :: Term t s user => t s -> ST r (GT user r s)
templateGT' = templateTerm'
