module Tog.Term.Impl.GraphReduce (GraphReduce) where

import           Data.IORef                       (IORef, readIORef, writeIORef, newIORef)
import           System.IO.Unsafe                 (unsafePerformIO)
import           Data.PhysEq

import           Tog.Term.Types
import           Tog.Term.Impl.Common
import           Tog.Term.Subst
import           Tog.Prelude
import           Tog.Unify.Common

-- Base terms
------------------------------------------------------------------------

type ITerm = GraphReduce           
newtype GraphReduce = GR {unGR :: IORef (TermView GraphReduce)}
  deriving (Typeable, Generic)

instance IsTermE ITerm where

instance ExpandMetas ITerm ITerm where
  expandMetas = genericExpandMetas

instance NFData GraphReduce where
   {-# NOINLINE rnf #-}
   rnf t' = unsafePerformIO$ do
     t <- liftIO $ readIORef $ unGR t'
     liftIO $ writeIORef (unGR t') $! force t
     return ()

instance Show GraphReduce where
  show _ = "<<ref>>"

instance Nf GraphReduce GraphReduce where
  nf t = do
    t' <- genericNf t
    tView <- liftIO $ readIORef $ unGR t'
    liftIO $ writeIORef (unGR t) $! (tView)
    return t

instance PrettyM GraphReduce GraphReduce where
  prettyPrecM = genericPrettyPrecM

instance FreeVars ITerm ITerm where freeVars = fastFreeVars  
instance IsVarNotFree ITerm ITerm

instance ApplySubst GraphReduce GraphReduce where
  safeApplySubst = genericSafeApplySubst
  applySubst = genericApplySubst
  safeStrengthen = genericSafeStrengthen

instance SynEq GraphReduce GraphReduce where
  synEq (GR tRef1) (GR tRef2) | tRef1 == tRef2 = return True
  synEq t1 t2 = genericSynEq t1 t2

instance PhysEq GraphReduce where
  physEq = (return.) . (==) `on` unGR

instance HasSubst GraphReduce where
  newtype Subst GraphReduce = GRSubst (GenericSubst GraphReduce) deriving (IsSubst GraphReduce)

instance IsTerm GraphReduce where
  shortName = "GR"
  longName  = "GraphReduce"


  whnf t = do
    blockedT <- genericWhnf t
    tView <- liftIO . readIORef . unGR =<< ignoreBlocking blockedT
    liftIO $ writeIORef (unGR t) $! (tView)
    return $ blockedT

  whnfMeta t = do
    blockedT <- genericWhnfMeta t
    tView <- ignoreMetaBlocking blockedT
    liftIO $ writeIORef (unGR t) $! (tView)
    return $ blockedT

  view = pure . unsafePerformIO . readIORef . unGR
  unview tView =
    -- “safe”: the ioRef depends on the termView
    -- If we created the ioRef and then wrote to it, now that would be a mess
    pure $ GR $ unsafePerformIO (newIORef $! tView)

  {-# NOINLINE set #-}
  set = unsafePerformIO $ GR <$> newIORef Set

  {-# NOINLINE refl #-}
  refl = unsafePerformIO $ GR <$> newIORef Refl

  {-# NOINLINE typeOfJ #-}
  typeOfJ = unsafePerformIO $ genericTypeOfJ

instance Prune ITerm ITerm where

instance KillTwins ITerm ITerm where killTwinsE = fastKillTwinsE
