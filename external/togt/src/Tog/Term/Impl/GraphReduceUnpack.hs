module Tog.Term.Impl.GraphReduceUnpack (GraphReduceUnpack) where

import           Data.IORef                       (IORef, readIORef, writeIORef, newIORef)
import           System.IO.Unsafe                 (unsafePerformIO)
import           Data.PhysEq 

import           Tog.Names
import           Tog.Names.Sorts
import qualified Tog.Term.Types                   as T
import           Tog.Term.Impl.Common
import           Tog.Prelude
import           Tog.Term.Subst
import           Tog.Unify.Common


-- Base terms
------------------------------------------------------------------------

type ITerm = GraphReduceUnpack
newtype GraphReduceUnpack = GRU {unGRU :: IORef Tm}
  deriving (Eq, Typeable, NFData)

instance IsTermE ITerm where

instance Show GraphReduceUnpack where
  show _ = "<<ref>>"

type Ref = GraphReduceUnpack

data Tm
    = Pi {-# UNPACK #-} !Ref !Name
         {-# UNPACK #-} !Ref
    | Lam !Name {-# UNPACK #-} !Ref
    | Equal {-# UNPACK #-} !Ref
            {-# UNPACK #-} !Ref
            {-# UNPACK #-} !Ref
    | Refl
    | Set
    | Con !(T.Opened ConName Ref) ![Ref]
    | App !(T.Head Ref) ![T.Elim Ref]
    deriving (Show, Eq, Typeable)

instance T.ExpandMetas ITerm ITerm where
  expandMetas = genericExpandMetas

instance T.FreeVars ITerm ITerm where freeVars = fastFreeVars  
instance T.IsVarNotFree ITerm ITerm

instance T.Nf GraphReduceUnpack GraphReduceUnpack where
  nf t = do
    t' <- genericNf t
    tView <- liftIO $ readIORef $ unGRU t'
    liftIO $ writeIORef (unGRU t) (tView)
    return t

instance T.PrettyM GraphReduceUnpack GraphReduceUnpack where
  prettyPrecM = genericPrettyPrecM

instance T.ApplySubst GraphReduceUnpack GraphReduceUnpack where
  safeApplySubst = genericSafeApplySubst
  applySubst = genericApplySubst
  safeStrengthen = genericSafeStrengthen

instance T.SynEq GraphReduceUnpack GraphReduceUnpack where
  synEq (GRU tRef1) (GRU tRef2) | tRef1 == tRef2 = return True
  synEq t1 t2 = genericSynEq t1 t2

instance PhysEq GraphReduceUnpack where
  physEq = (return.) . (==) `on` unGRU

instance HasSubst GraphReduceUnpack where
  newtype Subst GraphReduceUnpack = GRUSubst (GenericSubst GraphReduceUnpack) deriving (IsSubst GraphReduceUnpack)

instance T.IsTerm GraphReduceUnpack where
  shortName = "GRU"
  longName  = "GraphReduceUnpack"

  whnf t = do
    blockedT <- genericWhnf t
    tView <- liftIO . readIORef . unGRU =<< T.ignoreBlocking blockedT
    liftIO $ writeIORef (unGRU t) (tView)
    return $ blockedT

  whnfMeta t = do
    blockedT <- genericWhnfMeta t
    tView <- liftIO . readIORef . unGRU =<< T.ignoreMetaBlocking_ blockedT
    liftIO $ writeIORef (unGRU t) $! (tView)
    return $ blockedT

  view ref = pure$ unsafePerformIO$ do
    t <- liftIO $ readIORef $ unGRU ref
    return $ case t of
      Pi dom name cod -> T.Pi dom (T.Abs name cod)
      Lam name body -> T.Lam (T.Abs name body)
      Equal type_ x y -> T.Equal type_ x y
      Refl -> T.Refl
      Con dataCon args -> T.Con dataCon args
      Set -> T.Set
      App h els -> T.App h els

  unview tView = pure$ unsafePerformIO$ do
    let t = case tView of
          T.Lam (T.Abs name body) -> Lam name body
          T.Pi dom (T.Abs name cod) -> Pi dom name cod
          T.Equal type_ x y -> Equal type_ x y
          T.Refl -> Refl
          T.Con dataCon args -> Con dataCon args
          T.Set -> Set
          T.App h els -> App h els
    GRU <$> liftIO (newIORef t)

  {-# NOINLINE set #-}
  set = unsafePerformIO $ GRU <$> newIORef Set

  {-# NOINLINE refl #-}
  refl = unsafePerformIO $ GRU <$> newIORef Refl

  {-# NOINLINE typeOfJ #-}
  typeOfJ = unsafePerformIO $ genericTypeOfJ

instance Prune ITerm ITerm where

instance KillTwins ITerm ITerm where killTwinsE = fastKillTwinsE
