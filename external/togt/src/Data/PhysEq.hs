module Data.PhysEq (PhysEq(..), genericPhysEq) where

import Prelude
import System.Mem.StableName (makeStableName)
import Control.Monad.IO.Class (MonadIO(liftIO))

genericPhysEq :: (MonadIO m) => a -> a -> m Bool
genericPhysEq !a !b = liftIO$ do
  sa <- makeStableName a
  sb <- makeStableName b
  return$ sa == sb

class PhysEq a where
  -- | Physical equality MUST:
  --     - Cost a constant number of operations, regardless of the
  --       size of the data.
  --     - May not give false positives
  --   Physical equality MAY:
  --     - Give false negatives
  --   Physical equality SHOULD:
  --     - Be cheap
  physEq :: (MonadIO m) => a -> a -> m Bool
