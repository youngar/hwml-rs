module Tog.Term.Impl.HashConsed2 where

import           System.IO.Unsafe                 (unsafePerformIO)

import           Tog.Names
import           Tog.Term.Types
import           Tog.Term.Synonyms
import           Tog.Term.Impl.Common
import           Tog.Term.Subst
import           Tog.Unify.Common
import           Tog.Prelude

import           System.Mem.StableName


import           Data.Interned (Id, Interned(..), Cache, mkCache, intern, Uninternable(..), cacheSize)
import           Data.Vector
import qualified Data.Vector as V
import           Data.PhysEq

import           Tog.Instrumentation.Conf (Conf(..), readConf)
import           Tog.Instrumentation.Debug (printRaw)

import qualified Tog.Term.Impl.HashConsed4 as HC4

type HashConsed2 = ITerm

newtype ITerm = IT { getITerm :: HC4.ITerm }

deriving instance Show ITerm

internalId :: _
internalId = HC4.internalId . getITerm

type UITerm = TermView ITerm

instance Interned ITerm where
  type    Uninterned ITerm   =  UITerm
  newtype Description ITerm  = DITerm { getDITerm :: Description HC4.ITerm }

  describe = DITerm . describe . coerce
  identify i ui = IT$ identify i (coerce ui)
  cache = iTermCache

instance Uninternable ITerm where
  unintern = coerce . HC4.internalCell . getITerm

{-# NOINLINE iTermCache #-}
iTermCache :: Cache ITerm
iTermCache = mkCache

deriving instance Generic (Description ITerm)
deriving instance Show    (Description ITerm)
deriving instance Eq      (Description ITerm)

instance Hashable (Description ITerm)

instance Hashable ITerm where
  hashWithSalt s i = hashWithSalt s (internalId i)

instance Eq ITerm where
  a == b = internalId a == internalId b

instance Nf ITerm ITerm where
  nf = genericNf

instance ExpandMetas ITerm ITerm where
  expandMetas = genericExpandMetas

instance FreeVars ITerm ITerm where freeVars = fastFreeVars

instance PrettyM ITerm ITerm where
  prettyPrecM = genericPrettyPrecM

instance ApplySubst ITerm ITerm where
  safeApplySubst t sub = genericSafeApplySubst t sub
  applySubst t sub = genericApplySubst t sub
  safeStrengthen t sub = genericSafeStrengthen t sub

instance PhysEq ITerm where
  physEq = (pure.) . (==) `on` internalId
               
instance SynEq ITerm ITerm where
  synEq x y = ((internalId x == internalId y) ||) <$> genericSynEq x y

instance HasSubst ITerm where
  newtype Subst ITerm = HC2Subst (GenericSubst ITerm) deriving (IsSubst ITerm, Hashable, Eq)

instance IsTermE ITerm where

-- Perhaps memoize
instance IsTerm ITerm where
  shortName = "HC2"
  longName  = "HashConsed2"

  whnf t = genericWhnf t
  whnfMeta t = genericWhnfMeta t

  view = return . unintern
  unview = return . intern

  set = intern Set
  refl = intern Refl

  {-# NOINLINE typeOfJ #-}
  typeOfJ = unsafePerformIO $ genericTypeOfJ

  termIsHashable = return (Just Dict)

  type SignatureMixin ITerm = ()

  -- Initialization
  termReprInitialize = return ()
  termReprFinalize   = do
    sz <- liftIO$ cacheSize iTermCache
    (confStats <$> readConf) >>= flip when (printRaw ("stats.cache.size " <> show sz))

instance Prune ITerm ITerm where

instance KillTwins ITerm ITerm where killTwinsE = fastKillTwinsE

instance IsVarNotFree ITerm ITerm where
