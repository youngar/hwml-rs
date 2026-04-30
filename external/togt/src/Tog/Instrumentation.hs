module Tog.Instrumentation
  ( -- * Conf
    module Tog.Instrumentation.Conf
    -- * Debug
  , debugBracket
  , debugBracket_
  , debugBracket0
  , debug
  , debug_
  , debugWhenLabel
  , whenDebug
  , fatalError
  , printStackTrace
    -- * Init
  , instrument
  ) where


import           Tog.Instrumentation.Debug
import           Tog.Instrumentation.Timing
import           Tog.Instrumentation.Conf
import           Tog.Prelude

instrument :: (MonadConf m, MonadIO m) => m a -> m a
instrument m = do
  init'
  x <- m
  halt
  return x
  -- bracket init' (\() -> halt) (\() -> m)
  where
    init' = do
      liftIO timingInit
      debugInit

    halt = do
      timing <- confTimeSections `liftM` readConf
      when timing (liftIO timingReport)
