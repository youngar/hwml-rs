{-# LANGUAGE ForeignFunctionInterface #-}
module Tog.Instrumentation.Timing (timingInit, timingBracket, timingReport, timingRaw) where

import           Data.IORef                       (IORef, newIORef, writeIORef, readIORef, modifyIORef)
import qualified Data.HashTable.IO                as HT
import           Data.List                        (intercalate)
import           System.IO.Unsafe                 (unsafePerformIO)
import qualified Text.PrettyPrint.Boxes           as Boxes
import           Text.Printf                      (printf)
import           Tog.Instrumentation.Debug.Label  (DebugLabel, debugLabelToString)

import           Tog.Prelude

type Key = DebugLabel

{-# NOINLINE cumulativeTimes #-}
cumulativeTimes :: HT.CuckooHashTable Key Double
cumulativeTimes = unsafePerformIO HT.new

data StackItem = StackItem
  { siElapsed :: Double
  , siLeftAt  :: Double
  , siKey     :: Key
  }

_dummy :: a
_dummy = error "UNUSED" siElapsed siLeftAt siKey

type Stack = [StackItem]

{-# NOINLINE stackRef #-}
stackRef :: IORef Stack
stackRef = unsafePerformIO $ newIORef []

readStackRef :: IO Stack
readStackRef = readIORef stackRef

writeStackRef :: Stack -> IO ()
writeStackRef x = writeIORef stackRef x

modifyStackRef :: (Stack -> Stack) -> IO ()
modifyStackRef f = modifyIORef stackRef f

timingInit :: IO ()
timingInit = initializeTime

timingPush :: Key -> IO ()
timingPush key = do
  stack <- readStackRef
  t <- getCPUTime
  case stack of
    [] ->
      return ()
    (StackItem elapsed leftAt oldKey : stack') -> do
      let elapsed' = elapsed + (t - leftAt)
      writeStackRef $ StackItem elapsed' t oldKey : stack'
  modifyStackRef (StackItem 0 t key :)

timingPop :: IO ()
timingPop = do
  StackItem elapsed leftAt key : stack <- readStackRef
  t <- getCPUTime
  let elapsed' = elapsed + (t - leftAt)
  existing <- fromMaybe 0 <$> HT.lookup cumulativeTimes key
  HT.insert cumulativeTimes key (existing + elapsed')
  case stack of
    [] ->
      return ()
    StackItem oldElapsed _oldLeftAt oldKey : oldStack -> do
      writeStackRef $ StackItem oldElapsed t oldKey : oldStack

timingRaw :: (MonadIO m) => m a -> m (a, Double)
timingRaw m = do
  t1 <- liftIO getCPUTime
  a  <- m
  t2 <- liftIO getCPUTime
  return (a, t2-t1)


timingBracket :: (MonadIO m) => Key -> m a -> m a
timingBracket label m = do
  liftIO $ timingPush label
  x <- m
  liftIO $ timingPop
  return x

showMSec :: Double -> String
showMSec = (++ "ms") . showThousandSep . printf "%.0f"
  where
    -- From Agda

    showThousandSep :: String -> String
    showThousandSep = reverse . intercalate "," . chop 3 . reverse

    -- | Chop up a list in chunks of a given length.
    chop :: Int -> [a] -> [[a]]
    chop _ [] = []
    chop n xs = ys : chop n zs
        where (ys,zs) = splitAt n xs



timingReport :: IO ()
timingReport = do
  let msec_per_sec = 1000
  times <- HT.toList cumulativeTimes
  let total  = sum $ map snd times
  let kvs    = reverse . sortBy (comparing snd) $ times
  let fmt n  = showMSec (n * msec_per_sec)
  let perc n = printf "%.4f%%" $ ((n * 100) / total) :: String
  let vcatl  = Boxes.vcat Boxes.left
  let vcatr  = Boxes.vcat Boxes.right
  let (<+>)  = (Boxes.<+>)
  let box    = (\(x, y, z) -> vcatl x <+> vcatr y <+> vcatr z) $ unzip3
               [ (Boxes.text label, Boxes.text (fmt t), Boxes.text (perc t))
               | (label, t) <- ("Total",total):map (first debugLabelToString) kvs
               ]
  putStrLn "------------------------------------------------------------------------"
  putStrLn $ "-- Timing report"
  putStrLn "------------------------------------------------------------------------"
  putStrLn $ Boxes.render box

------------------------------------------------------------------------
-- Timing functions ripped from criterion.

-- | Return the amount of elapsed CPU time, combining user and kernel
-- (system) time into a single measure.
foreign import ccall unsafe "criterion_getcputime" getCPUTime :: IO Double

-- | Set up time measurement.
foreign import ccall unsafe "criterion_inittime" initializeTime :: IO ()
