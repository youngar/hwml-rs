{-# LANGUAGE UndecidableInstances #-}
-- | This module assumes single-threaded usage
module Tog.Term.Impl.HashConsed3 where

import           Data.Default (Default)
import qualified Data.Default as D
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

import           Data.Interned (Id, Interned(..), Cache, mkCache, intern, Uninternable(..))
import           Data.Maybe (maybeToList, fromMaybe)
import           Data.List (nub)
import           Data.Vector (Vector)
import qualified Data.Vector as V

import           Data.HashSet (HashSet)

import qualified Data.ISet as I
import qualified Data.BitSet as B
import           Control.Lens ((<&>))

type HashConsed3 = ITerm

data ITerm = IT { internalId   :: !Id
                , internalCell :: TermView ITerm
                } deriving (Show)

data Leaves = Leaves {
   _uninstantiatedMetas :: !(HashSet Meta)
 , _instantiatedMetas   :: !(HashSet Meta)
 , _uninstantiatedDefs  :: !(HashSet QName)
 , _instantiatedDefs    :: !(HashSet QName)
 }                         

$(makeLenses ''Leaves)              

instance Default Leaves where def = Leaves mempty mempty mempty mempty

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
  safeApplySubst t sub = safeApplySubstCached t sub
  applySubst = genericApplySubst
  safeStrengthen = genericSafeStrengthen

instance SynEq ITerm ITerm where
  synEq x y = return$ internalId x == internalId y
  -- Checking for ground terms is way too expensive
  {- do
    if internalId x == internalId y then
      return True
    else do
      x' <- groundTermCached x
      y' <- groundTermCached y
      return$ internalId x' == internalId y' -}

  

instance PhysEq ITerm where
  physEq = (return.) . (==) `on` internalId

instance IsTerm ITerm where
  shortName = "HC3"
  longName  = "HashConsed3"

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

data Mixin = Mixin {
    -- The cache fields are lazy so that the hash tables are only created on first use (hopefully).
    killTwinsCache       :: PureCache     ITerm (ITerm, TwinVarSet)
  , prunedCache          :: GuardedCache  (VarSet, ITerm) ITerm
  , freeVarsCache        :: PureCache     ITerm FreeVarSet
  , metaSetShallowCache  :: PureCache     ITerm (ISet Meta)
  , groundTermCache      :: PureCache     ITerm ITerm

  , safeApplySubstCache  :: PureCache     (ITerm, Subst ITerm) (Either Var ITerm)
  , nfCache              :: GuardedCache  ITerm ITerm
  , whnfCache            :: GuardedCache  ITerm (Blocked ITerm, ITerm)
  , guardCache           :: GuardedCache  ITerm Guard                                         
  , guardHeadCache       :: GuardedCache  (Head ITerm) Guard

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

          <*> newPureCache
          <*> newCache
          <*> newCache
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


mkGuard :: (MonadTerm ITerm m) => ITerm -> m Guard 
mkGuard = cached guardCache $ \t -> do
  gs <- go t
  return (gs,gs)
  where
    go t = do

      -- Using `view` here instead of `whnfView` is kosher because we are looking up
      -- the definition in the signature in `mkGuardHead`.
      tView <- view t
      case tView of
        Lam body           -> goAbs body
        Pi domain codomain -> mappend <$> mkGuard domain <*> goAbs codomain
        Equal type_ x y    -> mconcat <$> mapM mkGuard [type_, x, y]
        App h elims        -> mappend <$> mkGuardHead h <*> (mconcat <$> mapM goElim elims)
        Set                -> return mempty
        Refl               -> return mempty
        Con _ elims        -> mconcat <$> mapM mkGuard elims

    goElim (Apply t) = mkGuard t
    -- Do I need to check for metas in the projection arguments?
    goElim (Proj _)  = return mempty

    goAbs (Abs_ t) = go t


-- The guard is always applied to a normalized term. If a definition/meta
-- was not δ-expanded, then whatever is in its definition will not affect 
-- the result.
mkGuardHead :: (MonadTerm ITerm m) => Head ITerm -> m Guard
mkGuardHead = cached guardHeadCache $ \t -> do
  gs <- go t
  return (gs,gs)
  where
    go (Def (Opened name args)) = do
      sig <- askSignature
      (if sigIsOpenDefinition sig name then
        \gs -> gs <> qNameGuard name
      else
        id) <$> (mconcat <$> mapM mkGuard args)

    go (Meta mv)             = do
      sig <- askSignature
      if sigMetaIsInstantiated sig mv then
        return mempty
      else
        return$ metaGuard mv

    go (Var _)               = return mempty
    go (Twin _ _)            = return mempty
    go (J)                   = return mempty

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
  res <- genericNf$ fromMaybe t tOldNf
  gs <- mkGuard res
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

    Con (Tagged (Opened k a)) b -> DCon k (V.fromList$ fmap i a) (V.fromList$ fmap i b)

    App (Var v) a -> DAppV v (V.fromList$ fmap ielim a)
    App (Twin dir v) a -> DAppT dir v (V.fromList$ fmap ielim a)
    App (Def (Opened k a)) b -> DAppD k (V.fromList$ fmap i a) (V.fromList$ fmap ielim b)
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
        Con c elims      -> join$ con <$> traverse (traverse go) c <*> traverse go elims
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

