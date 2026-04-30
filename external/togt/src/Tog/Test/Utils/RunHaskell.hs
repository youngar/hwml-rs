module Tog.Test.Utils.RunHaskell (
  RunTog(..),
  runTogArguments,
  runTogCommandLine,
  execOpts,
  rtsOpts,
  runTog,
  pattern Valid,
  pattern NotValid,
  pattern TimedOut,
  TogResult(..),
  module Tog.Test.Utils.DashDash,
  Limit(..),
  DiffTime,
  ExitCode(..)
  ) where

import Control.Lens

import Control.DeepSeq
import Control.Concurrent.Async (async, wait)
import System.Exit
import System.Process
import GHC.IO.Handle
import Control.Exception (bracket)
import Data.Time.Clock (DiffTime, diffTimeToPicoseconds)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as T
import Data.String (IsString(..))
import qualified System.Timeout (timeout)
import Data.Ratio ((%))
  
-- Constructing configurations
import Tog.Test.Utils.DashDash

import Data.Aeson (ToJSON, FromJSON)
import GHC.Generics (Generic)

-- Processes
import System.Posix.Process
import System.Posix.Signals (sigINT, sigTERM, signalProcess, signalProcessGroup, sigKILL)

-- | Specifying resource limits
--   If an experiment succeeds under limit `x`, then it will
--   succeed under limit `y`, provided  x ≤ y.
data Limit a = Limit a
             | Unlimited
             deriving (Eq, Ord, Generic, Show)
             {-  Limit x ≤ Unlimited  -}

instance ToJSON a => ToJSON (Limit a)
instance FromJSON a => FromJSON (Limit a)

data RunTog = RunTog {
  _execPath :: FilePath
 ,_execOpts :: DashDash
 ,_rtsOpts  :: DashDash
 ,_timeLimit    :: Limit DiffTime
 }

$(makeLenses ''RunTog)

runTogArguments :: IsString a => RunTog -> [a]
runTogArguments RunTog{_execOpts=conf,_rtsOpts=rts} = 
  dashDash conf ++ ["+RTS"] ++ dashDash rts ++ ["-RTS"]

runTogCommandLine :: IsString a => RunTog -> [a]
runTogCommandLine = (:) <$> (fromString <$> _execPath) <*> runTogArguments

picosPerMicro :: Integer 
picosPerMicro = 1000 * 1000

picosPerSec :: Integer 
picosPerSec = picosPerMicro * microsPerSec
  where
    microsPerSec = 1000 * 1000

timeout :: DiffTime -> IO a -> IO (Maybe a)
timeout t m = do
  let μsecs = (ceiling$ diffTimeToPicoseconds t % picosPerMicro) 
  putStrLn $ "[INFO] Timing out after " <> show μsecs <> " μs"
  System.Timeout.timeout μsecs m 

-- procTime :: _
-- procTime exec args = proc "/usr/bin/time" $ "-f":"\n/usr/bin/time:Mmax=%Mmax kBytes\n":exec:args
-- | Requires GNU Coreutils
procTimeOut :: DiffTime -> (String -> [String] -> a) -> (String -> [String] -> a)
procTimeOut timeout κ exec args =
    let secs = 1 + (ceiling$ diffTimeToPicoseconds timeout % picosPerSec) in
    κ "/usr/bin/timeout" $ "--kill-after":"10":
                             "-s":"INT":
                               show @Integer secs:  exec  :  args

checkTimeOut :: ExitCode -> Maybe ExitCode
checkTimeOut (ExitFailure 124)                = Nothing 
checkTimeOut (ExitFailure i)   | i == 128 + 9 = Nothing 
checkTimeOut e                                = Just e 

-- | Requires GNU coreutils
procTime :: (String -> [String] -> a) -> (String -> [String] -> a)
procTime κ exec args = κ "/usr/bin/time" $ exec:args

runTog :: RunTog -> IO TogResult
runTog run@RunTog{_execPath=exec,_timeLimit} = do

  (stdoutRead, stdoutWrite) <- createPipe
  let args = runTogArguments run
  -- We want to also get time information
  let process = (
        (case _timeLimit of
          Unlimited -> procTime 
          Limit t   -> procTimeOut t . procTime) proc exec args){ 
    -- Bind standard input to /dev/null
    std_in       = NoStream
    -- We write both stdin and stdout to the same pipe
   ,std_out      = UseHandle stdoutWrite
   ,std_err      = UseHandle stdoutWrite
  }

  bracket (createProcess process)
    (\(Nothing, _, _, pHandle) ->
         mapM_ (signalProcess sigKILL) =<< getPid pHandle) $
      (\(Nothing, Nothing, Nothing, pHandle) -> do
        let command = showCommandForUser exec args

        -- Start reading the output, asynchronously
        -- The pipe will be closed when the process is finished
        outputAsync <- async$ do
            output <- T.hGetContents stdoutRead
            output `deepseq` hClose stdoutRead
            return output

        codeAsync   <- async$ waitForProcess pHandle <&> checkTimeOut

        -- Wait for the process
        code   <- wait codeAsync 
        output <- wait outputAsync

        return TogResult { code
                         , output
                         , command
                         , arguments = map T.pack args }
      )

data TogResult = TogResult
                 { code      :: Maybe ExitCode
                 , output    :: Text
                 , command   :: String
                 , arguments :: [Text]
                 }
               deriving (Eq, Show)

pattern Valid :: TogResult
pattern Valid <- TogResult{ code = Just ExitSuccess }

pattern NotValid :: Int -> Text -> TogResult
pattern NotValid n output <- TogResult{ code = Just (ExitFailure n), output }

pattern TimedOut :: TogResult
pattern TimedOut <- TogResult{ code = Nothing }
