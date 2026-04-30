-- | Implementation that also hash-conses environments
{-# LANGUAGE NoImplicitPrelude #-}
module Tog.Term.Impl.SuspendedHCI (SuspendedHCI) where

import           System.IO.Unsafe                 (unsafePerformIO)

import           Data.PhysEq
import           Tog.Prelude
import           Tog.Term.Synonyms
import           Tog.Term.Types
import           Tog.Names (QName(..))
import           Tog.Term.Impl.Common
import           Tog.Term.Impl.Common.Nadathur
import           Tog.Term.Subst
import           Tog.Unify.Common

import qualified Data.Vector as V
import Data.Vector (Vector)

import Data.Interned (Id, Interned(..), Cache, mkCache, intern, Uninternable(..), cacheSize)

import           Tog.Instrumentation.Conf (Conf(..), readConf)
import           Tog.Instrumentation.Debug (printRaw)

-- Base terms
------------------------------------------------------------------------

type SuspendedHCI = ITerm

data ITerm = IT { internalId   :: {-# UNPACK #-} !Id
                , internalCell :: Susp ITerm (TermView ITerm)
                }
    deriving (Show, Typeable)

{-# NOINLINE iTermCache #-}
iTermCache :: Cache ITerm
iTermCache = mkCache

type QNameId = Id
type MetaId = Int
type IElims = (Vector (Elim TId))
type TId = Id

data DITerm =
      DPi {-# UNPACK #-} !(Type TId) {-# UNPACK #-} !(Abs (Type TId))
    | DLam {-# UNPACK #-} !(Abs TId)
    | DEqual {-# UNPACK #-} !(Type TId) {-# UNPACK #-} !(Term TId) {-# UNPACK #-} !(Term TId)
    | DRefl
    | DSet
    | DCon {-# UNPACK #-} !QNameId {-# UNPACK #-} !(Vector (Term TId)) {-# UNPACK #-} !(Vector (Term TId))
    | DAppV !Var {-# UNPACK #-} !IElims
    | DAppT !Dir !Var {-# UNPACK #-} !IElims
    | DAppD {-# UNPACK #-} !QNameId {-# UNPACK #-} !(Vector (Term TId)) {-# UNPACK #-} !IElims
    | DAppM {-# UNPACK #-} !MetaId {-# UNPACK #-} !IElims
    | DAppJ {-# UNPACK #-} !IElims
    deriving (Generic, Eq)

instance Hashable DITerm where

instance Interned ITerm where
  type Uninterned ITerm = Susp ITerm (TermView ITerm)
  data Description ITerm = D { dTerm  :: !DITerm
                             , dEnv   :: {-# UNPACK #-} !(Vector (Maybe TId, Nat))
                             , dNl    :: {-# UNPACK #-} !Int
                             } deriving (Eq, Generic)
  
  describe Susp{term,nl,env}  = D{dTerm,dEnv,dNl}
    where 
    dNl   = natToInt nl
    dEnv  = V.fromList $ [(fmap i t ,n) | (t,n) <- envToList env]
    dTerm = case term of
              Pi a b -> DPi (i a) (fmap i b)
              Lam a  -> DLam (fmap i a)
              Equal a b c -> DEqual (i a) (i b) (i c)
              Refl -> DRefl
              Set  -> DSet

              Con (Tagged (Opened k a)) b -> DCon (qNameId k) (V.fromList$ fmap i a) (V.fromList$ fmap i b)

              App (Var v) a -> DAppV v (V.fromList$ fmap ielim a)
              App (Twin dir v) a -> DAppT dir v (V.fromList$ fmap ielim a)
              App (Def (Opened k a)) b -> DAppD (qNameId k) (V.fromList$ fmap i a) (V.fromList$ fmap ielim b)
              App (Meta m) a -> DAppM (metaId m) (V.fromList$ fmap ielim a)
              App J a -> DAppJ (V.fromList$ fmap ielim a)

    i :: ITerm -> Id
    i = internalId
    ielim = fmap i

  identify internalId internalCell = IT {
     internalId   
    ,internalCell 
    }

  cache = iTermCache

instance Hashable (Description ITerm)

instance Uninternable ITerm where
  unintern = internalCell

-- Environments
-------------------

-- These two instances must agree. They are used for hash tables
-- They should also run in O(1)
instance Eq ITerm where (==) = (==) `on` internalId
instance Hashable ITerm where hashWithSalt s = hashWithSalt s . internalId

pureUnview :: TermView ITerm -> ITerm
pureUnview = intern . IdSusp

pureView :: ITerm -> TermView ITerm
pureView IT{internalCell = IdSusp t} = t
pureView IT{internalCell} = fmap susp . commute $ internalCell

instance HasVar ITerm where
  varP Nothing    idx = pureUnview$ App (Var (mkVar "_" idx)) []
  varP (Just dir) idx = pureUnview$ App (Twin dir (mkVar "_" idx)) []

instance HasSusp ITerm ITerm where
  susp     = intern . joinSusp . fmap internalCell
  viewSusp = internalCell

instance Metas ITerm ITerm where
  foldMetas = genericFoldMetas

instance Nf ITerm ITerm where
  nf = genericNf

instance ExpandMetas ITerm ITerm where
  expandMetas = genericExpandMetas

instance PrettyM ITerm ITerm where
  prettyPrecM = genericPrettyPrecM

instance ApplySubst ITerm ITerm where
  safeApplySubst t σ = genericSafeApplySubst t σ {- return$ S$ substToSusp σ t -}
  safeStrengthen = genericSafeStrengthen
  applySubst = (pure.) . useSuspension
    {-
    case σ of

      Id                    -> useSuspension 
      Weaken _ Id           -> useSuspension
      Weaken _ (Instantiate _ Id)           -> useSuspension
      Instantiate _ Id      -> useSuspension
      Instantiate _ (Instantiate _ Id)      -> useSuspension
      Instantiate _ (Weaken _ Id)       -> useSuspension
      Strengthen _ Id       -> useSuspension
      Strengthen _ (Instantiate _ Id)       -> useSuspension
      Strengthen _ (Weaken _ Id)       -> useSuspension
      Lift _ Id             -> useSuspension
      Lift _ (Weaken _ Id)  -> useSuspension
      Lift _ (Instantiate _ Id)  -> useSuspension
      _ -> useSuspension
      -- _ -> genericApplySubst t σ
      -}
      where
        useSuspension IT{internalCell=t} σ = intern$ substToSusp σ t

instance SynEq ITerm ITerm where
  synEq = genericSynEq

instance FreeVars ITerm ITerm where
  freeVars t = fastFreeVars t

instance PhysEq ITerm  where
  physEq = genericPhysEq `on` internalId

instance IsTerm ITerm where
  shortName = "PHI"
  longName  = "SuspendedHCI"

  newtype Subst ITerm = SSubst (GenericSubst ITerm) deriving (IsSubst ITerm)

  whnf = genericWhnf
  whnfMeta = genericWhnfMeta

  view = return . pureView 
  unview = return . pureUnview

  set = pureUnview Set
  refl = pureUnview Refl

  termIsHashable = return (Just (Dict))

  {-# NOINLINE typeOfJ #-}
  typeOfJ = unsafePerformIO $ genericTypeOfJ

  -- Initialization
  termReprInitialize = return ()
  termReprFinalize   = do
    sz <- liftIO$ cacheSize iTermCache
    (confStats <$> readConf) >>= flip when (printRaw ("stats.cache.size " <> show sz))

instance Prune ITerm ITerm where

instance KillTwins ITerm ITerm where killTwinsE = fastKillTwinsE

{-
suspendedFreeVars :: ITerm -> FreeVarSet
suspendedFreeVars t = genericLazyFreeVars (view t) suspendedFreeVars

suspendedIsVarFree :: ITerm -> Var -> Bool
suspendedIsVarFree t var = fvIsFree var (suspendedFreeVars t)
-}

