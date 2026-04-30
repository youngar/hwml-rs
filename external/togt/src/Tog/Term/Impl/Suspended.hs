{-# LANGUAGE NoImplicitPrelude #-}
module Tog.Term.Impl.Suspended (Suspended) where

import           System.IO.Unsafe                 (unsafePerformIO)

import           Data.PhysEq
import           Tog.Prelude
import           Tog.Term.Types
import           Tog.Term.Impl.Common
import           Tog.Term.Impl.Common.Nadathur
import           Tog.Term.Subst
import           Tog.Unify.Common

-- Base terms
------------------------------------------------------------------------

type Suspended = ITerm
newtype ITerm = S { unS :: Susp ITerm (TermView ITerm) }
    deriving (Show, Typeable)

-- Environments
-------------------

instance Eq ITerm where
  (==) = (==) `on` unS

instance Hashable ITerm where
  hashWithSalt s = hashWithSalt s . unS

pureUnview :: TermView ITerm -> ITerm
pureUnview = S . idSusp

instance IsVarNotFree ITerm ITerm where

instance HasVar ITerm where
  varP Nothing    idx = pureUnview$ App (Var (mkVar "_" idx)) []
  varP (Just dir) idx = pureUnview$ App (Twin dir (mkVar "_" idx)) []

instance HasSusp ITerm ITerm where
  susp     = S . joinSusp . fmap unS
  viewSusp = unS

instance Nf ITerm ITerm where
  nf = genericNf

instance ExpandMetas ITerm ITerm where
  expandMetas = genericExpandMetas

instance PrettyM ITerm ITerm where
  prettyPrecM = genericPrettyPrecM

instance ApplySubst ITerm ITerm where
  safeApplySubst (S t) σ = genericSafeApplySubst (S t) σ {- return$ S$ substToSusp σ t -}
  safeStrengthen = genericSafeStrengthen
  applySubst t σ = useSuspension
      where
        useSuspension = pure$ S$ substToSusp σ (unS t)

instance SynEq ITerm ITerm where
  synEq = genericSynEq

instance FreeVars ITerm ITerm where
  freeVars t = fastFreeVars t

instance PhysEq ITerm  where
  physEq = genericPhysEq `on` unS

instance HasSubst ITerm where
  newtype Subst ITerm = SSubst (GenericSubst ITerm) deriving (IsSubst ITerm)

instance IsTerm ITerm where
  shortName = "P"
  longName  = "Suspended"

  whnf = genericWhnf
  whnfMeta = genericWhnfMeta

  view = return . fmap susp . commute . unS
  unview = return . pureUnview

  set = S (idSusp Set)
  refl = S (idSusp Refl)

  termIsHashable = return (Just (Dict))

  {-# NOINLINE typeOfJ #-}
  typeOfJ = unsafePerformIO $ genericTypeOfJ

instance IsTermE ITerm where

instance Prune ITerm ITerm where

instance KillTwins ITerm ITerm where killTwinsE = fastKillTwinsE

{-
suspendedFreeVars :: ITerm -> FreeVarSet
suspendedFreeVars t = genericLazyFreeVars (view t) suspendedFreeVars

suspendedIsVarFree :: ITerm -> Var -> Bool
suspendedIsVarFree t var = fvIsFree var (suspendedFreeVars t)
-}

