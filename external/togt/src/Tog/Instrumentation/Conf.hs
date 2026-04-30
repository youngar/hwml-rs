-- | Global configuration, what we get from the command line.  Every
-- program using tog as a library should start with @'writeConf' conf@.
module Tog.Instrumentation.Conf
  ( Conf(..)
  , confDebug
  , confDisableDebug
  , confDisableSynEquality
  , confExtraSynEquality
  , confTimeLabel
  , SynEqLevel(..)
  , DebugLabel
  , DebugLabels(..)
--  , writeGlobalConf
  , MonadConf(..)
--  , readGlobalConf
  , ConfT
  , runConfT
  , defaultConf
  ) where

{-
import           System.IO.Unsafe                 (unsafePerformIO)
import           Data.IORef                       (IORef, newIORef, atomicModifyIORef', readIORef)
-}
import           Tog.Instrumentation.Debug.Label

import           Tog.Prelude
import           Control.Monad.Reader        (ReaderT, runReaderT, ask)
import           Control.Monad.State.Strict  (StateT)
import           Control.Monad.Writer.Strict (WriterT)
import           Control.Monad.Except        (ExceptT)

-- Configuration
------------------------------------------------------------------------

data Conf = Conf
  { confTermType                :: String
  , confSolver                  :: String
  , confDebugLabels             :: DebugLabels
  , confStackTrace              :: Bool
  , confQuiet                   :: Bool
  , confNoMetasSummary          :: Bool
  , confMetasReport             :: Bool
  , confMetasOnlyUnsolved       :: Bool
  , confNoProblemsSummary       :: Bool
  , confProblemsReport          :: Bool
  , confCheckMetaConsistency    :: Bool
  , confSynEquality             :: SynEqLevel
  , confDontNormalizePP         :: Bool
  , confWhnfApplySubst          :: Bool
  , confTimeSections            :: Bool
  , confWhnfEliminate           :: Bool
  , confPhysicalEquality        :: Bool
  , confNoCheckElaborated       :: Bool
  , confNfInUnifier             :: Bool
  , confFastDebug               :: Bool
  , confPopularityContest       :: Bool
  , confStats                   :: Bool
  , confUnifyAudit              :: Bool
  , confFastElaborate           :: Bool
  , confDelayedDispatch         :: Bool
  , confParanoidSyntacticEquality :: Bool
  , confParanoidContextCurrying :: Bool
  }

defaultConf :: Conf
defaultConf = Conf
  { confTermType                = ""
  , confSolver                  = ""
  , confDebugLabels             = DLSome []
  , confStackTrace              = False
  , confQuiet                   = False
  , confNoMetasSummary          = False
  , confMetasReport             = False
  , confMetasOnlyUnsolved       = False
  , confNoProblemsSummary       = False
  , confProblemsReport          = False
  , confCheckMetaConsistency    = False
  , confSynEquality             = NoSynEq
  , confDontNormalizePP         = False
  , confWhnfApplySubst          = False
  , confTimeSections            = False
  , confWhnfEliminate           = False
  , confPhysicalEquality        = False
  , confNoCheckElaborated       = False
  , confNfInUnifier             = False
  , confFastDebug               = False
  , confPopularityContest       = False
  , confStats                   = False
  , confUnifyAudit              = False
  , confFastElaborate           = False
  , confDelayedDispatch         = False
  , confParanoidSyntacticEquality = False
  , confParanoidContextCurrying = False
  }

data DebugLabels
  = DLAll
  | DLSome [DebugLabel]

data SynEqLevel = NoSynEq
                | OneSynEq
                | AllSynEq
                deriving (Ord, Eq)

confDebug :: Conf -> Bool
confDebug conf = case confDebugLabels conf of
  DLAll     -> True
  DLSome [] -> False
  DLSome _  -> True

confDisableDebug :: Conf -> Conf
confDisableDebug conf = conf{confDebugLabels = DLSome []}

confDisableSynEquality :: Conf -> Bool
confDisableSynEquality conf = confSynEquality conf <= NoSynEq

confExtraSynEquality :: Conf -> Bool
confExtraSynEquality conf = confSynEquality conf >= AllSynEq

confTimeLabel :: DebugLabel -> Conf -> Bool
confTimeLabel lbl = (&&) <$> confTimeSections <*> pure (labelIsTimeable lbl)
  where
    labelIsTimeable Instantiate = False
    labelIsTimeable _           = True

instance Semigroup DebugLabels where
  DLAll     <> _         = DLAll
  _         <> DLAll     = DLAll
  DLSome xs <> DLSome ys = DLSome (xs <> ys)

instance Monoid DebugLabels where
  mempty = DLSome []


{-
{-# NOINLINE confRef #-}
confRef :: IORef (Maybe Conf)
confRef = unsafePerformIO $ newIORef Nothing
-}

class Monad m => MonadConf m where
  readConf :: m Conf 

newtype ConfT m a = ConfT { confT :: ReaderT Conf m a } deriving (Functor, Applicative, Monad, MonadIO)
instance Monad m => MonadConf (ConfT m) where readConf = ConfT ask

runConfT :: ConfT m a -> Conf -> m a
runConfT = runReaderT . confT

instance MonadConf m => MonadConf (ReaderT env m) where readConf = lift readConf
instance MonadConf m => MonadConf (StateT  s   m) where readConf = lift readConf
instance (Monoid s, MonadConf m) => MonadConf (WriterT s   m) where readConf = lift readConf
instance MonadConf m => MonadConf (ExceptT e   m) where readConf = lift readConf
instance MonadConf m => MonadConf (MaybeT m) where readConf = lift readConf


{-                                                   
writeGlobalConf :: (MonadIO m) => Conf -> m ()
writeGlobalConf conf = do
  ok <- liftIO $ atomicModifyIORef' confRef $ \mbConf -> case mbConf of
    Nothing -> (Just conf, True)
    Just c  -> (Just c,    False)
  unless ok $ error "writeConf: already written."

readGlobalConf :: (MonadIO m) => m Conf
readGlobalConf = do
  mbConf <- liftIO $ readIORef confRef
  case mbConf of
    Nothing   -> error "readConf: conf not written"
    Just conf -> return conf
-}
