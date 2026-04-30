module Tog.Test.Utils.RTS (runTogInstrumented) where

import Tog.Test.Utils.DashDash
import Tog.Test.Utils.RunHaskell
import System.IO.Temp
import Control.Lens
import Data.Monoid ((<>), First(..))
import Data.Maybe (fromMaybe)
import Text.Regex
import System.FilePath ((</>))
import Control.DeepSeq (deepseq)

newtype TimeMSec = TimeMSec Rational
newtype MemoryMB = MemoryMB Rational

data ResourceUsage' a b c d = ResourceUsage {
   timeMut   :: a
  ,resident  :: b
  ,timeGC    :: c
  ,timeTotal :: d
  }

type ResourceUsage = ResourceUsage'
                       TimeMSec
                       MemoryMB
                       TimeMSec
                       TimeMSec

instance (Semigroup a
         ,Semigroup b
         ,Semigroup c
         ,Semigroup d
         ) => Semigroup (ResourceUsage' a b c d) where
  (<>) (ResourceUsage a b c d)
       (ResourceUsage a' b' c' d') =
          ResourceUsage (a <> a')
                        (b <> b')
                        (c <> c')
                        (d <> d')

instance (Monoid a
         ,Monoid b
         ,Monoid c
         ,Monoid d
         ) => Monoid (ResourceUsage' a b c d)  where
  mempty  = ResourceUsage mempty mempty mempty mempty

{- 
         278,208 bytes allocated in the heap
           4,600 bytes copied during GC
          94,616 bytes maximum residency (1 sample(s))
          20,072 bytes maximum slop
               1 MB total memory in use (0 MB lost due to fragmentation)

                                     Tot time (elapsed)  Avg pause  Max pause
  Gen  0         0 colls,     0 par    0.000s   0.000s     0.0000s    0.0000s
  Gen  1         1 colls,     0 par    0.000s   0.000s     0.0003s    0.0003s

  INIT    time    0.000s  (  0.000s elapsed)
  MUT     time    0.000s  (  0.045s elapsed)
  GC      time    0.000s  (  0.000s elapsed)
  EXIT    time    0.000s  (  0.000s elapsed)
  Total   time    0.000s  (  0.046s elapsed)

  %GC     time       0.0%  (0.7% elapsed)

  Alloc rate    0 bytes per MUT second

  Productivity 100.0% of total user, 0.0% of total elapsed

-}

mkResourceUsage :: String
  -- ^ Output from RTS file
  -> ResourceUsage
mkResourceUsage str =
  resourceUsageFromFirst $ mconcat $ 
      [ ResourceUsage
      { timeMut   = First (getTime "MUT" line)
      , timeGC    = First (getTime "GC" line)
      , timeTotal = First (getTime "Total" line)
      , resident  = First (getMemory "maximum residency" line)
      }
      | line <- lines str ]
  where
    getDigitsFirst rex = fmap fromDigits . fmap (!! 1) . matchRegex (mkRegex rex)

    getTime prefix = fmap (TimeMSec . (* 1000)) .
      getDigitsFirst (prefix ++ " *time *([0-9.,]+)s") 

    getMemory suffix = fmap (MemoryMB . (/ 1000000)) .
      getDigitsFirst ("([0-9.,]+) bytes " ++ suffix)

    fromDigits = read @Rational . filter (/= ',')

    resourceUsageFromFirst (ResourceUsage{..}) =
      ResourceUsage{
         timeMut   = fromMaybe (TimeMSec 0) $ getFirst timeMut
        ,timeGC    = fromMaybe (TimeMSec 0) $ getFirst timeGC 
        ,timeTotal = fromMaybe (TimeMSec 0) $ getFirst timeTotal
        ,resident  = fromMaybe (MemoryMB 0) $ getFirst resident
        }



runTogInstrumented :: RunTog ->
                      IO (TogResult, ResourceUsage)
runTogInstrumented run = do 

  (res,rtsOutput) <-
    withSystemTempDirectory "rts" $ \dir -> do
      let fname = dir </> "rts.txt"
      res        <- runTog (run & rtsOpts <>~ dd "s" fname)
      rtsOutput  <- readFile fname
      rtsOutput `deepseq` return ()
      return (res,rtsOutput)
  
  return (res, mkResourceUsage rtsOutput)
