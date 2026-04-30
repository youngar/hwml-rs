module Tog.Test.Suite.Utils where

-- Constructing configurations
import Tog.Test.Utils.DashDash
import Tog.Test.Utils.RunHaskell

-- Finding test cases
import System.FilePath (takeBaseName, (-<.>), takeDirectory)

import Control.Monad (forM)

-- Creating test cases
-- import Test.HUnit

import Data.Semigroup ((<>))

import Tog.Test.Config
import Tog.Test.Utils
import Tog.Test.Files.Dirs

import Data.Text (Text)
import qualified Data.Text as T

-- Environment
import System.Environment (lookupEnv)
import System.IO (stderr, hPutStrLn)

-- | Data for holding a test type
data TestCase where
  SuccessCase :: { theFile :: FilePath } -> TestCase 
  FailureCase :: { theFile :: FilePath, goldenFile :: FilePath } -> TestCase 

testCaseName :: TestCase -> String
testCaseName = takeBaseName . theFile 

testCaseFamily :: TestCase -> String
testCaseFamily = takeBaseName . takeDirectory . theFile

getTestCases :: (TestDirSet a)
             => FilePath -- ^ Test directory
             -> IO (a -> [TestCase])
getTestCases dir = do
  files <- forM enumAll $ \family -> do
    paths <- getTestFiles dir family
    let cases = case testDirType family of
          Success -> [ SuccessCase path | path <- paths ]
          Time    -> [ SuccessCase path | path <- paths ]
          Failure -> [ FailureCase{ theFile    = path
                                  , goldenFile = path -<.> "exit"
                                  }
                     | path <- paths ]
    return (family, cases)
  return$ (\(Just c) -> c) . flip lookup files

mkGoldenFile :: TogResult -> Text                        
mkGoldenFile TogResult{code=Nothing,output} = "TIMEOUT" <> "\n" <> output
mkGoldenFile TogResult{code=Just code,output} = T.pack (show code) <> "\n" <> output

mkRunTog :: FilePath -> FilePath -> TogConf -> Limit DiffTime -> RunTog
mkRunTog exec file conf limit = RunTog{_execPath = exec
                                ,_execOpts = conf <> ddPos file
                                ,_rtsOpts  = dd "H" "1G"
                                ,_timeLimit = limit
                                }

-- | Get the version information from the executable
togVersion :: RunTog -> IO Text
togVersion run = do
  TogResult{output} <- 
    runTog run{_execOpts = ddYes "version", _rtsOpts = mempty}
  return output

perhapsLogTogResult :: TogResult -> IO ()
perhapsLogTogResult result = do
  lookupEnv "TOG_TEST_VERBOSE" >>= \case
    Nothing -> return ()
    Just "" -> return ()
    Just _  -> hPutStrLn stderr $ "\n" ++ show result
