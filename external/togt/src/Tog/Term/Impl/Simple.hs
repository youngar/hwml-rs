module Tog.Term.Impl.Simple (Simple) where

import           System.IO.Unsafe                 (unsafePerformIO)

import           Data.PhysEq
import           Tog.Prelude
import           Tog.Term.Types
import           Tog.Term.Impl.Common
import           Tog.Term.Subst
import           Tog.Term.FreeVars
import           Tog.Unify.Common

-- Base terms
------------------------------------------------------------------------

type ITerm = Simple
newtype Simple = S {unS :: TermView Simple}
    deriving (Eq, Show, Typeable, NFData, Hashable)

instance IsTermE ITerm where

instance ExpandMetas ITerm ITerm where
  expandMetas = genericExpandMetas

instance Nf Simple Simple where
  nf = genericNf

instance PrettyM Simple Simple where
  prettyPrecM = genericPrettyPrecM

instance ApplySubst Simple Simple where
  safeApplySubst = genericSafeApplySubst
  applySubst = genericApplySubst
  safeStrengthen = genericSafeStrengthen

instance SynEq Simple Simple where
  synEq = genericSynEq

instance FreeVars ITerm ITerm where freeVars = fastFreeVars  

instance PhysEq Simple  where
  physEq = genericPhysEq `on` unS

instance HasSubst Simple where
  newtype Subst Simple = SSubst (GenericSubst Simple) deriving (IsSubst Simple)

instance IsTerm Simple where
  shortName = "S"
  longName  = "Simple"

  whnf = genericWhnf
  whnfMeta = genericWhnfMeta

  view = return . unS
  unview = return . S

  set = S Set
  refl = S Refl

  termIsHashable = return (Just (Dict))

  {-# NOINLINE typeOfJ #-}
  typeOfJ = unsafePerformIO $ genericTypeOfJ

instance Prune Simple Simple where

instance IsVarNotFree ITerm ITerm where

instance KillTwins ITerm ITerm where killTwinsE = fastKillTwinsE
