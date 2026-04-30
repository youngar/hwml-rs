module Tog.Test.Utils where

enumAll :: (Enum a, Bounded a) => [a]
enumAll = [minBound..]

-- | Test types we support.
--
--   Test types determine the input data and the
---  “pass” conditions.
data TestType = Success
              | Failure
              | Time

passthrough :: (Applicative m) => (a -> m ()) -> (a -> m a)
passthrough f = (*>) <$> f <*> pure
