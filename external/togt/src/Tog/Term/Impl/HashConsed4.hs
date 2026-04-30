{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
-- | This module assumes single-threaded usage
module Tog.Term.Impl.HashConsed4 where

import qualified Data.HashTable.IO                as HT
import           System.IO.Unsafe                 (unsafePerformIO)
import           Data.PhysEq

import           Tog.Names
import           Tog.Names.Sorts
import           Tog.Term.Types
import           Tog.Term.MetaVars
import           Tog.Term.Impl.Common
import           Tog.Term.Subst
import           Tog.Term.FreeVars
import           Tog.Monad
import           Tog.Prelude
import           Tog.Unify.Common

import           Control.Monad.Writer.Strict (WriterT(..), runWriterT, writer)

import           Data.Interned (Id, Interned(..), Cache, mkCache, intern, Uninternable(..), cacheSize)
import           Data.Maybe (maybeToList, fromMaybe)
import           Data.List (nub)
import           Data.Vector (Vector)
import qualified Data.Vector as V

import qualified Data.BitSet as B

import           Tog.Instrumentation.Conf (Conf(..), readConf)
import           Tog.Instrumentation.Debug (printRaw)


type HashConsed4 = ITerm
type IMonad m = MonadTerm ITerm m
type ITC a = forall r s. TC ITerm r s
type TermId = Id

-- | prop> getIndex a == getIndex b  ==> a == b 
class (Hashable (Index a), Eq a, Eq (Index a)) => HasIndex a where
  type Index a
  type Index a = a 
  getIndex :: a -> Index a
  default getIndex :: (a ~ Index a) => a -> Index a
  getIndex = id

data ITerm = IT { internalId   :: {-# UNPACK #-} !Id
                , internalCell :: TermView ITerm
                } deriving (Show)

instance HasIndex ITerm where
  type Index ITerm = Id
  getIndex = internalId

instance (HasIndex a, HasIndex b) => HasIndex (a,b) where
  type Index (a,b) = (Index a, Index b)
  getIndex (a,b) = (getIndex a, getIndex b)

-- It could be worthwhile replacing these lists by strict lists.
type IElim = Elim Id

{-# NOINLINE iTermCache #-}
iTermCache :: Cache ITerm
iTermCache = mkCache

deriving instance Generic (Description ITerm)
deriving instance Show (Description ITerm)
deriving instance Eq (Description ITerm)

instance Hashable (Description ITerm)

instance Hashable ITerm where
  hashWithSalt s i = hashWithSalt s (internalId i)

instance Eq ITerm where
  a == b = internalId a == internalId b

instance IsTermE ITerm where
  -- the fast and slow options are interwined
  metaOccurs _ _ = return True
  metaOccursWhnf mv a = occursCached mv a

instance Nf ITerm ITerm where
  nf = nfCached

instance ExpandMetas ITerm ITerm where
  expandMetas = WriterT . expandMetasCached

instance FreeVars ITerm ITerm where freeVars = freeVarsCached

instance KillTwins ITerm ITerm where killTwins = killTwinsCached

instance PrettyM ITerm ITerm where
  prettyPrecM = genericPrettyPrecM

instance ApplySubst ITerm ITerm where
  safeApplySubst t sub = safeApplySubstCached t sub
  applySubst = genericApplySubst
  safeStrengthen = genericSafeStrengthen

instance SynEq ITerm ITerm where
  synEq x y =
    physEq x y >>= \case
      True  -> return True
      False -> genericSynEq x y

instance PhysEq ITerm where
  physEq = (return.) . (==) `on` internalId

instance HasSubst ITerm where
  data Subst ITerm = IS {
    subInternalId   :: !Id
   ,subInternalCell :: !(SubstV ITerm ISubst)
   }

instance IsTerm ITerm where
  shortName = "HC4"
  longName  = "HashConsed4"

  -- Cached!
  whnf = whnfCached
  whnfTerm = whnfTermCached
  whnfMeta = whnfMetaCached
  viewW = viewWCached
  whnfMetaTerm = whnfMetaTermCached

  view = return . unintern
  unview = return . intern

  set = intern Set
  refl = intern Refl

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

  -- Initialization
  termReprInitialize = return ()
  termReprFinalize   = do
    sz <- liftIO$ cacheSize iTermCache
    (confStats <$> readConf) >>= (flip when $ printRaw $ "stats.cache.size " <> show sz)

data NormalGuard = NormalGuard { whnfMetaGuard :: Meta
                               , whnfGuard     :: QNameSet
                               }

data Mixin = Mixin {
    -- The cache fields are lazy so that the hash tables are only created on first use (hopefully).
    killTwinsCache       :: PureCache     ITerm (ITerm, TwinVarSet)
  , prunedCache          :: GuardedCache  (VarSet, ITerm) ITerm
  , freeVarsCache        :: PureCache     ITerm FreeVarSet
  , metaSetShallowCache  :: PureCache     ITerm (ISet Meta)
  , groundTermCache      :: PureCache     ITerm ITerm

  , safeApplySubstCache  :: PureCache     (ITerm, Subst ITerm) (Either Var ITerm)

    
    -- Pros: Reduce redundancy
    -- Cons: Non-determinism (e.g. enabling debug will make terms more normalized overall, f.ex.) 
  , nfCache               :: GuardedCache  ITerm ITerm
  , expandMetasCache      :: GuardedCache  ITerm (ITerm, Guard)
  , whnfCache             :: GuardedCache  ITerm (Blocked ITerm, ITerm)
  , whnfMetaCache         :: PureCache     ITerm ITerm

  , unrollPiCache         :: GuardedCache  (Type ITerm) (Tel (Type ITerm), Type ITerm)
  , etaExpandMetaCache    :: GuardedCache  ITerm (Maybe (MetaBody ITerm, ITerm)) 
  , etaExpandCache        :: GuardedCache  (Type ITerm :∋ Term ITerm) ITerm                             

  , taintSnitch           :: !(MonoidAcc Guard)
  }

instance HasIndex (Type ITerm :∋ Term ITerm) where
  type Index (Type ITerm :∋ Term ITerm) = (TermId :∋ TermId)
  getIndex (a :∈ b) = (getIndex a :∈ getIndex b)

instance HasIndex VarSet where
instance HasIndex (Subst ITerm) where

instance MonadIO m => DefaultM m Mixin where
  defM = liftIO$
    Mixin <$> newPureCache
          <*> newCache     
          <*> newPureCache
          <*> newPureCache
          <*> newPureCache

          <*> newPureCache

          <*> newCache
          <*> newCache
          <*> newCache

          <*> newPureCache                             

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

type GuardedCache a b = HT.CuckooHashTable (Index a) (Guarded b)
type Key gc = Mixin -> gc

instance IsVarNotFree ITerm ITerm where

fromKey :: MonadTerm ITerm m => Key k -> m k
fromKey key = key <$> askSignatureMixin

newCache :: IO (HT.CuckooHashTable a (Guarded b))
newCache = HT.new

guardedLookupInspect' :: (MonadTerm t m, HasIndex a) => GuardedCache a b -> a -> m (Either (Maybe b) (b, Guard))
guardedLookupInspect' gc a = do
  cached <- liftIO$ HT.lookup gc (getIndex a)
  case cached of
    Nothing  -> pure$ Left Nothing
    Just  b  -> (bimap Just id) <$> unguardedInspect b

guardedLookup :: (MonadTerm t m, HasIndex a) => GuardedCache a b -> a -> m (Maybe b)
guardedLookup gc a = guardedLookupInspect' gc a <&> \case
  Left{}  -> Nothing
  Right (b,_) -> Just b

guardedLookupInspect :: (MonadTerm t m, HasIndex a) => GuardedCache a b -> a -> m (Maybe (b, Guard))
guardedLookupInspect gc a = guardedLookupInspect' gc a <&> \case
  Left{}  -> Nothing
  Right (b,mvs) -> Just (b, mvs)

cached :: (MonadTerm ITerm m, HasIndex a) => Key (GuardedCache a b) -> (a -> m (b, Guard)) -> a -> m b
cached gck f a = do
  gc <- fromKey gck
  b <- guardedLookupInspect gc a
  case b of
    Nothing -> do
      (!b, mvs) <- scrub$ f a
      liftIO$ HT.insert gc (getIndex a) (Guarded mvs b)
      taint mvs >> return b
    Just (b,mvs) ->
      taint mvs >> return b

notCached :: (MonadTerm ITerm m, HasIndex a) => (a -> m (b, Guard)) -> a -> m b
notCached f a = do
  (!b,mvs) <- scrub$ f a
  taint mvs >> return b

cachedRefresh :: (MonadTerm ITerm m, HasIndex a) => Key (GuardedCache a b) -> (a -> Maybe b -> m ([a], Guard, b)) -> a -> m b
cachedRefresh gck f a = do
  gc <- fromKey gck
  guardedLookupInspect' gc a >>= \case
    Left old -> do
      (as, mvs, !b) <- f a old
      liftIO$ forM_ (a:as) $ \a' -> HT.insert gc (getIndex a') (Guarded mvs b)
      taint mvs >> return b
    Right (b,mvs) -> taint mvs >> return b

cachedRefreshIgnore :: (MonadTerm ITerm m, HasIndex a) => Key (GuardedCache a b) -> (a -> Maybe b -> m ([a], Guard, b)) -> a -> m b
cachedRefreshIgnore gc f = cached gc (\a -> do
                                           (_,gs,b) <- f a Nothing
                                           return (b,gs))

type PureCache a b = HT.CuckooHashTable (Index a) b 

newPureCache :: IO (HT.CuckooHashTable a b)
newPureCache = HT.new

cachedPure :: (MonadTerm ITerm m, HasIndex a) => Key (PureCache a b) -> (a -> m b) -> a -> m b
cachedPure gck f a = do
  gc <- fromKey gck
  b <- liftIO$ HT.lookup gc (getIndex a)
  case b of
    Nothing -> do
      !b <- scrub$ f a
      liftIO$ HT.insert gc (getIndex a) b
      return b
    Just b -> return b


cachedPureRefresh :: (MonadTerm ITerm m, HasIndex a) => Key (PureCache a b) -> (a -> m ([a], b)) -> a -> m b
cachedPureRefresh gck f a = do
  gc <- fromKey gck
  b <- liftIO$ HT.lookup gc (getIndex a)
  case b of
    Nothing -> do
      !(as,b) <- f a
      liftIO$ forM_ (a:as) $ \a' -> HT.insert gc (getIndex a') b
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

viewWCached :: (IMonad m) => ITerm -> m (TermView ITerm)
viewWCached = whnfMetaTermCached >=> view
 
whnfMetaCached :: (IMonad m) => ITerm -> m (MetaBlocked ITerm)
whnfMetaCached = whnfMetaPairCached >&> snd

whnfMetaTermCached :: (MonadTerm ITerm m) => ITerm -> m ITerm
whnfMetaTermCached = whnfMetaPairCached >&> fst

-- Term must be normalized already
checkMetaBlocked :: MonadTerm t m => t -> m (Maybe (MetaBlocked t))
checkMetaBlocked t = view t >>= \case
    App (Meta mv) els ->
      metaIsInstantiated mv >>= \case
        True  -> return Nothing
        False -> return$ Just (MetaBlockingHead mv els)
    _ -> return$ Just (MetaNotBlocked t)

whnfMetaPairCached :: (MonadTerm ITerm m) => ITerm -> m (ITerm, MetaBlocked ITerm)
whnfMetaPairCached t = do
  checkMetaBlocked t >>= \case
    Just mbt -> return (t,mbt)
    Nothing  -> do
      cacheLookup whnfMetaCache t >>= \case
        Nothing -> do
                  mbt <- genericWhnfMeta t 
                  t'' <- ignoreMetaBlocking_ mbt
                  cacheUpdate whnfMetaCache t t''
                  return (t'',mbt)
        Just t'  -> do
          checkMetaBlocked t' >>= \case
            Just mbt -> return (t', mbt)
            Nothing  -> do
                mbt <- genericWhnfMeta t' 
                t'' <- ignoreMetaBlocking_ mbt
                cacheUpdate whnfMetaCache t  t''
                cacheUpdate whnfMetaCache t' t''
                return (t'',mbt)

whnfCached :: IMonad m => ITerm -> m (Blocked ITerm)
whnfCached = whnfPairCached >&> fst

whnfTermCached :: IMonad m => ITerm -> m ITerm
whnfTermCached = whnfPairCached >&> snd

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
  (res, gs) <- inspect $ genericNf$ fromMaybe t tOldNf
  return (res:maybeToList tOldNf, gs, res)

expandMetasCached :: (MonadTerm ITerm m) => ITerm -> m (ITerm, Guard)
expandMetasCached = cachedRefresh expandMetasCache $ \t (fmap fst -> tOld) -> do
                            (res, gs) <- runWriterT $ genericExpandMetas $ fromMaybe t tOld
                            -- Only the metavariables affect the result of the operation
                            return (res:maybeToList tOld, metasOnly gs, (res, gs)) 

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
instance Interned ITerm where
  type Uninterned ITerm = TermView ITerm
  data Description ITerm =
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

    Con (Opened k a) b -> DCon (getQName k) (V.fromList$ fmap i a) (V.fromList$ fmap i b)

    App (Var v) a -> DAppV v (V.fromList$ fmap ielim a)
    App (Twin dir v) a -> DAppT dir v (V.fromList$ fmap ielim a)
    App (Def (Opened k a)) b -> DAppD (getQName k) (V.fromList$ fmap i a) (V.fromList$ fmap ielim b)
    App (Meta m) a -> DAppM m (V.fromList$ fmap ielim a)
    App J a -> DAppJ (V.fromList$ fmap ielim a)

    where
      i :: ITerm -> Id
      i = internalId
      ielim = fmap i

  identify = IT
  cache = iTermCache

instance Uninternable ITerm where
  unintern = internalCell

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

--------------------
-- Occurs caching --
--------------------
occursCached :: (IMonad m) => Meta -> ITerm -> m DoesNotOccur
occursCached mv t = do
  cache <- liftIO (HT.new :: IO (HT.CuckooHashTable _ _))
  let go1 t = do
        liftIO (HT.lookup cache (getIndex t)) >>= \case
          Nothing -> do
            -- lookup t.
            -- if t is in the cache as 'DoesNotOccur', return t
            res <- genericMetaOccurs FunViewW (runFoldMetas go1) mv t
            liftIO$ HT.insert cache (getIndex t) (case res of
                                                    Any True ->  Nothing
                                                    Any False -> Just DoesNotOccur)
            return res
          Just (Just ~DoesNotOccur) -> return (Any False)
          Just Nothing  -> return (Any True)
  runVisitMetasT (go1 t) >>= \case
    Any False -> return DoesNotOccur
    Any True  ->
      let go2 t =
            liftIO (HT.lookup cache (getIndex t)) >>= \case
              Just (Just res) -> return (Meet res)
              _ -> do
                Meet res <- genericMetaOccursWhnf (runFoldMetas go2) mv t
                liftIO (HT.insert cache (getIndex t) (Just res))
                return (Meet res)
      in getMeet <$> go2 t

    
-- Because it is shallow, it will not traverse down definitions, and
-- we can ignore the MonadVisit constraint.
{-
metaSetShallowCached :: (MonadTerm ITerm m, MonadVisit m) => ITerm -> m (ISet Meta)
metaSetShallowCached = cachedPure metaSetShallowCache $ \t -> do
  mvs <- flip runReaderT MetaSetShallow $ genericFoldMetas t
  return mvs

occursShallowCached :: (MonadTerm ITerm m, MonadVisit m) => Meta -> ITerm -> m Any
occursShallowCached mv t = Any . I.member mv <$> metaSetShallowCached t
-}

----------------------------
-- Free variables caching --
----------------------------

freeVarsCached :: (MonadTerm ITerm m) => ITerm -> m FreeVarSet
freeVarsCached = cachedPure freeVarsCache genericFreeVars

-----------------------------------------
-- Ground terms for syntactic equality --
-----------------------------------------

groundTermCached :: forall m. (MonadTerm ITerm m) => ITerm -> m ITerm
groundTermCached = cachedPureRefresh groundTermCache $ \t -> do
                                                  t' <- go t
                                                  return ([t'],t')
  where
    go :: ITerm -> m ITerm
    go t =
      view t >>= (\case
        Pi a (Abs_ b) -> join$ pi_ <$> go a <*> go b
        Lam (Abs_ a)     -> join$ lam_ <$> go a
        Equal type_ x y  -> join$ equal <$> go type_ <*> go x <*> go y
        App h elims      -> join$ app <$> traverse go h <*> traverse (traverse go) elims
        Set              -> pure t
        Refl             -> pure t
        Con c elims      -> join$ con <$> traverse go c <*> traverse go elims
        )

-------------------------
-- Pruned term caching --
-------------------------

instance Prune ITerm ITerm where
  prune = debugPruneTerm $ \fv t -> do
    fv' <- (B.intersect fv . fvAll) <$> freeVars t
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

cacheLookup :: (HasIndex a, MonadTerm ITerm m) => Key (PureCache a b) -> a -> m (Maybe b)
cacheLookup gck a = do
  gc <- fromKey gck
  liftIO$ HT.lookup gc (getIndex a)

cacheUpdate :: (HasIndex a, MonadTerm ITerm m) => Key (PureCache a b) -> a -> b -> m ()
cacheUpdate gck a b = do
  gc <- fromKey gck
  liftIO$ HT.insert gc (getIndex a) b
