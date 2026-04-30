{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE NoImplicitPrelude #-}
-- | This module assumes single-threaded usage
module Tog.Term.Impl.HashConsed4P where

import qualified Data.HashTable.IO                as HT
import           System.IO.Unsafe                 (unsafePerformIO)
import           Data.PhysEq

import           Tog.Names
import           Tog.Term.Types
import           Tog.Term.Synonyms
import           Tog.Term.Impl.Common
import           Tog.Term.Subst
import           Tog.Term.FreeVars
import           Tog.Monad
import           Tog.Prelude
import           Tog.Unify.Common

import           Control.Monad.Reader (ask, runReaderT)
import           Control.Monad.Writer.Strict (WriterT, runWriterT, writer)

import           Data.Interned (Id, Interned(..), Cache, mkCache, intern, Uninternable(..), cacheSize)
import           Data.Maybe (maybeToList, fromMaybe)
import           Data.List (nub)
import           Data.Vector (Vector)
import qualified Data.Vector as V

import qualified Data.ISet as I
import qualified Data.BitSet as B

import           Tog.Term.Impl.Common.Nadathur

import           Tog.Instrumentation.Conf (Conf(..), readConf)
import           Tog.Instrumentation.Debug (printRaw)

import qualified Tog.Instrumentation.Debug.Label as DL
import           Tog.Instrumentation.Debug

type HashConsed4P = ITerm

data VTerm = VT  { vInternalId    :: {-# UNPACK #-} !Id
                 , vInternalCell  :: TermView HTerm
                 } deriving (Show)

data HTerm = HT  { internalId    :: {-# UNPACK #-} !Id
                 , internalCell  :: Susp HTerm VTerm
                 } deriving (Show)

type ITerm = HTerm

-- newtype ITerm = IT { susp :: Susp ITerm (TermView HTerm)  } deriving (Show, Hashable, Eq)

-- It could be worthwhile replacing these lists by strict lists.
type IElim = Elim Id

{-# NOINLINE iTermCache #-}
iTermCache :: Cache ITerm
iTermCache = mkCache

instance Metas ITerm ITerm where
  foldMetas a = do
    ask >>= \case
      OccursShallow mv -> occursShallowCached  mv a
      MetaSetShallow   -> lift$ metaSetShallowCached a
--      OccursDeep    mv -> lift$ occursDeepCached     mv a
--      MetaSetDeep      -> lift$ metaSetDeepCached    mv a
      _                -> genericFoldMetas a

instance Nf ITerm ITerm where
  nf = nfCached


instance ExpandMetas ITerm ITerm where
  expandMetas = genericExpandMetas

instance FreeVars ITerm ITerm where freeVars = freeVarsCached

instance KillTwins ITerm ITerm where killTwins = killTwinsCached

instance PrettyM ITerm ITerm where
  prettyPrecM = genericPrettyPrecM

instance ApplySubst ITerm ITerm where
  applySubst t σ = pure . intern . substToSusp σ . unintern $ t
  safeApplySubst t sub = safeApplySubstCached t sub
  safeStrengthen = genericSafeStrengthen

instance SynEq ITerm ITerm where
  synEq x y = genericSynEq x y

instance PhysEq ITerm where
  physEq = (return.) . (==) `on` internalId

instance HasVar ITerm where
  varP Nothing    idx = pureUnview$ App (Var (mkVar "_" idx)) []
  varP (Just dir) idx = pureUnview$ App (Twin dir (mkVar "_" idx)) []

instance HasSusp ITerm ITerm where
  susp     = intern . joinSusp . fmap internalCell
  viewSusp = fmap vInternalCell . internalCell

pureUnview :: TermView HTerm -> HTerm
pureUnview = intern @HTerm . idSusp . intern @VTerm

instance IsTerm ITerm where
  shortName = "HC4P"
  longName  = "HashConsed4P"

  {- data Subst ITerm = SSubst (GenericSubst ITerm) -}

  data Subst ITerm = IS {
    subInternalId   :: !Id
   ,subInternalCell :: !(SubstV ITerm ISubst)
   }

  type MonadFreeVars' ITerm m = MonadTerm ITerm m
  monadFreeVarsDict = Sub Dict

  -- Cached!
  whnf = fmap fst . whnfPairCached
  whnfTerm = fmap snd . whnfPairCached
  whnfMeta = genericWhnfMeta

  view = return . fmap susp . commute . fmap vInternalCell . internalCell
  
  unview = return . pureUnview

  set = pureUnview Set
  refl = pureUnview Refl

  {-# NOINLINE typeOfJ #-}
  typeOfJ = unsafePerformIO $ genericTypeOfJ

  termIsHashable = return (Just (Dict))

  type SignatureMixin ITerm = Mixin

  memoize = memoizeCached

  type Taint ITerm = Guard
  taint :: (MonadTerm ITerm m) => Guard -> m ()
  taint g = modifySignatureMixin $ \mix@Mixin{taintSnitch} -> mix{taintSnitch = acc taintSnitch g}

  taintDefinition = taint . qNameGuard

  inspect :: (MonadTerm ITerm m) => m a -> m (a, Guard)
  inspect m = do
    oldSnitch <- taintSnitch <$> askSignatureMixin
    modifySignatureMixin $ \mix -> mix{taintSnitch = yesAcc}
    a <- m
    g <- readAcc . taintSnitch <$> askSignatureMixin
    modifySignatureMixin $ \mix -> mix{taintSnitch = oldSnitch}
    return (a,g)

  scrub :: (MonadTerm ITerm m) => m a -> m a
  scrub m = do
    oldSnitch <- taintSnitch <$> askSignatureMixin
    modifySignatureMixin $ \mix -> mix{taintSnitch = noAcc}
    a <- m
    modifySignatureMixin $ \mix -> mix{taintSnitch = oldSnitch}
    return a

  termReprInitialize = return ()
  termReprFinalize   = do
    sz <- liftIO$ cacheSize iTermCache
    stats <- confStats <$> readConf
    when stats $ printRaw ("stats.cache.size " <> show sz)

data Mixin = Mixin {
    -- The cache fields are lazy so that the hash tables are only created on first use (hopefully).
    killTwinsCache       :: PureCache     ITerm (ITerm, TwinVarSet)
  , prunedCache          :: GuardedCache  (VarSet, ITerm) ITerm
  , freeVarsCache        :: PureCache     ITerm FreeVarSet
  , metaSetShallowCache  :: PureCache     ITerm (ISet Meta)

  , safeApplySubstCache  :: PureCache     (ITerm, Subst ITerm) (Either Var ITerm)
  , nfCache              :: GuardedCache  ITerm ITerm
  , whnfCache            :: GuardedCache  ITerm (Blocked ITerm, ITerm)

  , unrollPiCache        :: GuardedCache  (Type ITerm) (Tel (Type ITerm), Type ITerm)
  , etaExpandMetaCache   :: GuardedCache  ITerm (Maybe (MetaBody ITerm, ITerm)) 
  , etaExpandCache       :: GuardedCache  (Type ITerm :∋ Term ITerm) ITerm                             

  , taintSnitch          :: !(MonoidAcc Guard)
  }

instance MonadIO m => DefaultM m Mixin where
  defM = liftIO$
    Mixin <$> newPureCache
          <*> newCache
          <*> newPureCache
          <*> newPureCache

          <*> newPureCache
          <*> newCache
          <*> newCache

          <*> newCache                             
          <*> newCache                             
          <*> newCache                             

          <*> pure noAcc

type ISubst = Subst ITerm  
instance IsSubst ITerm ISubst where
  viewSub = unintern
  unviewSub = intern

instance Hashable ISubst where
  hashWithSalt s i = hashWithSalt s (subInternalId i)

instance Eq ISubst where  
  (==) = (==) `on` subInternalId  


----
-- Substitution cache
----
instance Interned ISubst where
  type Uninterned ISubst = SubstV ITerm ISubst
  data Description ISubst
    = DId
    | DWeaken !Natural {-# UNPACK #-}  !Id
    | DStrengthen !Natural {-# UNPACK #-} !Id
    | DInstantiate {-# UNPACK #-} !(Term Id) {-# UNPACK #-} !Id
    | DLift !Natural {-# UNPACK #-} !Id
    deriving (Eq, Generic)

  describe t = case t of
    Id_ -> DId
    Weaken_ n σ -> DWeaken n (i σ)
    Strengthen_ n σ -> DStrengthen n (i σ)
    Instantiate_ t σ -> DInstantiate (internalId t) (i σ)
    Lift_ n σ -> DLift n (i σ)
    where
      i = subInternalId

  identify = IS
  cache = iSubstCache

instance Hashable (Description ISubst)

{-# NOINLINE iSubstCache #-}
iSubstCache :: Cache ISubst
iSubstCache = mkCache

instance Uninternable ISubst where
  unintern = subInternalCell


type GuardedCache a b = HT.CuckooHashTable a (Guarded b)
type Key gc = Mixin -> gc

fromKey :: MonadTerm ITerm m => Key k -> m k
fromKey key = key <$> askSignatureMixin

newCache :: IO (GuardedCache a b)
newCache = HT.new

guardedLookupInspect' :: (MonadTerm t m, Eq a, Hashable a) => GuardedCache a b -> a -> m (Either (Maybe b) (b, Guard))
guardedLookupInspect' gc a = do
  cached <- liftIO$ HT.lookup gc a
  case cached of
    Nothing  -> pure$ Left Nothing
    Just  b  -> (bimap Just id) <$> unguardedInspect b

guardedLookup :: (MonadTerm t m, Eq a, Hashable a) => GuardedCache a b -> a -> m (Maybe b)
guardedLookup gc a = guardedLookupInspect' gc a <&> \case
  Left{}  -> Nothing
  Right (b,_) -> Just b

guardedLookupInspect :: (MonadTerm t m, Eq a, Hashable a) => GuardedCache a b -> a -> m (Maybe (b, Guard))
guardedLookupInspect gc a = guardedLookupInspect' gc a <&> \case
  Left{}  -> Nothing
  Right (b,mvs) -> Just (b, mvs)

cached :: (MonadTerm ITerm m, Eq a, Hashable a) => Key (GuardedCache a b) -> (a -> m (b, Guard)) -> a -> m b
cached gck f a = do
  gc <- fromKey gck
  b <- guardedLookupInspect gc a
  case b of
    Nothing -> do
      (!b, mvs) <- scrub$ f a
      liftIO$ HT.insert gc a (Guarded mvs b)
      taint mvs >> return b
    Just (b,mvs) ->
      taint mvs >> return b

notCached :: (MonadTerm ITerm m, Eq a, Hashable a) => (a -> m (b, Guard)) -> a -> m b
notCached f a = do
  (!b,mvs) <- scrub$ f a
  taint mvs >> return b

cachedRefresh :: (MonadTerm ITerm m, Eq a, Hashable a) => Key (GuardedCache a b) -> (a -> Maybe b -> m ([a], Guard, b)) -> a -> m b
cachedRefresh gck f a = do
  gc <- fromKey gck
  guardedLookupInspect' gc a >>= \case
    Left old -> do
      (as, mvs, !b) <- f a old
      liftIO$ forM_ (a:as) $ \a' -> HT.insert gc a' (Guarded mvs b)
      taint mvs >> return b
    Right (b,mvs) -> taint mvs >> return b

cachedRefreshIgnore :: (MonadTerm ITerm m, Eq a, Hashable a) => Key (GuardedCache a b) -> (a -> Maybe b -> m ([a], Guard, b)) -> a -> m b
cachedRefreshIgnore gc f = cached gc (\a -> do
                                           (_,gs,b) <- f a Nothing
                                           return (b,gs))

type PureCache a b = HT.CuckooHashTable a b 

newPureCache :: IO (PureCache a b)
newPureCache = HT.new

cachedPure :: (MonadTerm ITerm m, Eq a, Hashable a) => Key (PureCache a b) -> (a -> m b) -> a -> m b
cachedPure gck f a = do
  gc <- fromKey gck
  b <- liftIO$ HT.lookup gc a
  case b of
    Nothing -> do
      !b <- scrub$ f a
      liftIO$ HT.insert gc a b
      return b
    Just b -> return b


cachedPureRefresh :: (MonadTerm ITerm m, Eq a, Hashable a) => Key (PureCache a b) -> (a -> m ([a], b)) -> a -> m b
cachedPureRefresh gck f a = do
  gc <- fromKey gck
  b <- liftIO$ HT.lookup gc a
  case b of
    Nothing -> do
      !(as,b) <- f a
      liftIO$ forM_ (a:as) $ \a' -> HT.insert gc a' b
      return b
    Just b -> return b

--
-- WHNF caching                                        
-- 
whnfPairCached :: (MonadTerm ITerm m) => ITerm -> m (Blocked ITerm, ITerm)
whnfPairCached =
  cachedRefresh whnfCache $ \t tOld -> do
    let tOldWhnf = snd <$> tOld
    let a = fromMaybe t tOldWhnf
    b <- genericWhnf a
    ub <- ignoreBlocking b
    return ( nub [t,a,ub]
           , fromMaybe mempty $ isBlocked b
           , (b, ub) )

memoizeCached :: (MonadTerm ITerm m)
              => (MemoizeCache ITerm a b) 
              -> (a -> m (b, Guard))
              -> (a -> m b)
memoizeCached k f = do
  (case k of
    UnrollPiCache -> cached unrollPiCache
    EtaExpandMetaCache -> cached etaExpandMetaCache
    EtaExpandCache -> cached etaExpandCache) $ f

--
-- Nf caching                                        
--
nfCached :: (MonadTerm ITerm m) => ITerm -> m ITerm
nfCached = cachedRefresh nfCache $ \t tOldNf -> do
  -- Do not memoize the individual weak-head-normal forms.
  (res, gs) <- inspect $ genericNf $ fromMaybe t tOldNf
  return (res:maybeToList tOldNf, gs, res)

-- 
-- Substitution caching                                        
--
-- Note that whether the result changes depends on whether
-- the confWhnfApplySubst option is enabled
--  reduce <- confWhnfApplySubst <$> readConf
--  tView <- lift $ if reduce then whnfView t else view t
-- 

safeApplySubstCached :: (MonadTerm ITerm m) => ITerm -> Subst ITerm -> ApplySubstM m ITerm
safeApplySubstCached =
  genericSafeApplySubstIdOpt $ 
  genericSafeApplySubstReduce $
  go
  where
    go =
      curry $ (ExceptT.) $ cachedPure safeApplySubstCache $ \(t, subst) -> do
        runExceptT$ genericSafeApplySubst t subst

---- Interning
{-# NOINLINE vTermCache #-}
vTermCache :: Cache VTerm
vTermCache = mkCache

instance Interned VTerm where
  type Uninterned VTerm = TermView HTerm
  data Description VTerm =
      DPi {-# UNPACK #-} !(Type Id) {-# UNPACK #-} !(Abs (Type Id))
    | DLam {-# UNPACK #-} !(Abs Id)
    | DEqual {-# UNPACK #-} !(Type Id) {-# UNPACK #-} !(Term Id) {-# UNPACK #-} !(Term Id)
    | DRefl
    | DSet
    | DCon {-# UNPACK #-} !QName {-# UNPACK #-} !(Vector (Term Id)) {-# UNPACK #-} !(Vector (Term Id))
    | DAppV !Var {-# UNPACK #-} !(Vector IElim)
    | DAppT !Dir !Var {-# UNPACK #-} !(Vector IElim)
    | DAppD {-# UNPACK #-} !QName {-# UNPACK #-} !(Vector (Term Id)) {-# UNPACK #-} !(Vector IElim)
    | DAppM {-# UNPACK #-} !Meta {-# UNPACK #-} !(Vector IElim)
    | DAppJ {-# UNPACK #-} !(Vector IElim)

  describe t = case t of
    Pi a b -> DPi (i a) (fmap i b)
    Lam a  -> DLam (fmap i a)
    Equal a b c -> DEqual (i a) (i b) (i c)
    Refl -> DRefl
    Set  -> DSet

    Con (Tagged (Opened k a)) b -> DCon k (V.fromList$ fmap i a) (V.fromList$ fmap i b)

    App (Var v) a -> DAppV v (V.fromList$ fmap ielim a)
    App (Twin dir v) a -> DAppT dir v (V.fromList$ fmap ielim a)
    App (Def (Opened k a)) b -> DAppD k (V.fromList$ fmap i a) (V.fromList$ fmap ielim b)
    App (Meta m) a -> DAppM m (V.fromList$ fmap ielim a)
    App J a -> DAppJ (V.fromList$ fmap ielim a)

    where
      i :: HTerm -> Id
      i = internalId
      ielim = fmap i

  identify = VT
  cache = vTermCache

instance Uninternable VTerm where
  unintern = vInternalCell


deriving instance Generic (Description VTerm)
deriving instance Show (Description VTerm)
deriving instance Eq (Description VTerm)
instance Hashable (Description VTerm)
instance Hashable VTerm where hashWithSalt s = hashWithSalt s . vInternalId
instance Eq VTerm where (==) = (==) `on` vInternalId

instance Interned HTerm where
  type Uninterned HTerm = Susp HTerm VTerm
  data Description HTerm =
     DEnv   Int (Term Id) (StableName (Env HTerm))

  describe = \case
    Susp{term,ol=_ol,nl,env} -> DEnv (natToInt nl) (vInternalId term) (envStableName env)--V.fromList xs)
--      where
--        xs = [(fmap internalId t, natToInt n) | (t,n) <- take (fromIntegral ol)$ envToList env]

  identify = HT
  cache = iTermCache

instance Uninternable HTerm where
  unintern = internalCell
      
deriving instance Generic (Description HTerm)
-- deriving instance Show (Description HTerm)
deriving instance Eq (Description HTerm)
instance Hashable (Description HTerm)
instance Hashable HTerm where hashWithSalt s i = hashWithSalt s (internalId i)
instance Eq HTerm where a == b = internalId a == internalId b

--------------------
-- Occurs caching --
--------------------

-- Because it is shallow, it will not traverse down definitions, and
-- we can ignore the MonadVisit constraint.
metaSetShallowCached :: (MonadTerm ITerm m, MonadVisit m) => ITerm -> m (ISet Meta)
metaSetShallowCached = cachedPure metaSetShallowCache $ \t -> do
  mvs <- flip runReaderT MetaSetShallow $ genericFoldMetas t
  return mvs

occursShallowCached :: (MonadTerm ITerm m, MonadVisit m) => Meta -> ITerm -> m Any
occursShallowCached mv t = Any . I.member mv <$> metaSetShallowCached t

----------------------------
-- Free variables caching --
----------------------------

freeVarsCached :: (MonadTerm ITerm m) => ITerm -> m FreeVarSet
freeVarsCached = cachedPure freeVarsCache genericFreeVars

-------------------------
-- Pruned term caching --
-------------------------

instance Prune ITerm ITerm where
  prune = debugPruneTerm $ \fv t -> do
    fv' <-
      debugBracket DL.FreeVars (pure mempty) $ ((B.intersect fv . fvAll) <$> freeVars t)
    if fv' /= mempty then
      (cachedRefresh prunedCache $ \(fv'',t) tPrunedOld -> do
        (tPruned, mvs) <- inspect $ genericPruneTerm fv'' (fromMaybe t tPrunedOld)
        let ts = (fv'',) <$> (tPruned:maybeToList tPrunedOld)
        return (ts, mvs, tPruned)
        ) (fv',t)
    else
      return t

---------------------------
-- Twin variable caching --
---------------------------

killTwinsCached :: ITerm -> WriterT TwinVarSet (TC ITerm r s) ITerm
killTwinsCached = (lift . cachedPure killTwinsCache (runWriterT . genericKillTwinsTerm)) >=> writer

-- Memoization logistics
-------------------------


---------------------------------------------------
-- Branch-free optional disable-able accumulator --
---------------------------------------------------

newtype MonoidAcc a =
  MA { monoidAcc :: (a -> (a, MonoidAcc a)) } 

yesAcc, noAcc :: Monoid a => MonoidAcc a
noAcc  = MA (\_ -> (mempty, noAcc))
yesAcc =
  MA (go mempty)  
  where 
    go acc a = let !acc' = a <> acc in (acc', MA$ go acc')

acc :: MonoidAcc a -> a -> MonoidAcc a
acc = (snd .) . monoidAcc

readAcc :: Monoid a => MonoidAcc a -> a
readAcc = fst . ($ mempty) . monoidAcc

{-
whnfCached :: (MonadTerm ITerm m) => ITerm -> m (Blocked ITerm)
whnfCached a = do
  gc <- fromKey whnfCache
  liftIO (HT.lookup gc a) >>= \case
    Nothing -> do
      b <- genericWhnf a
      liftIO$ HT.insert gc a b
      return b
    Just b -> do
      case isBlocked b of
        Nothing -> return b
        Just g  ->
          guardIsInstantiated g >>= \case
            True -> ignoreBlocking b >>= \a' -> do
              b'  <- genericWhnf a'
              b'' <- ignoreBlocking b'
              liftIO$ do
                  HT.insert gc a  b'
                  HT.insert gc a' b'
                  HT.insert gc b'' b'
              return b'
            False -> return b
-}

{-
whnfCached = fmap fst . whnfPairCached
whnfTermCached = fmap snd . whnfPairCached

whnfViewCached = (MonadTerm ITerm m) => ITerm -> m ITerm
whnfViewCached = cachedRefresh whnfViewCache $ \t tOldWhnf ->
  b <- ignoreBlocking <=< genericWhnf (fromMaybe t tOldWhnf)
  
  unsafePerformIO newExpiredCache
-}

