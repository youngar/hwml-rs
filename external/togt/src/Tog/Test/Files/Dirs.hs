module Tog.Test.Files.Dirs
where

import Tog.Test.Utils
import System.FilePath.Glob (globDir1, compile)
import System.FilePath (FilePath, (</>))
import Data.List (sort)

-- Configuration
testCaseDir :: FilePath
testCaseDir = "test/cases"

data TestCaseFamily = SucceedAll
                    | SucceedHeterogeneous
                    | SlowAll
                    | SlowHeterogeneous
                    | Fail
                    | Constraints
                    | Benchmark
                    | BenchmarkHeterogeneous
                      deriving (Enum, Bounded, Eq)

class (Enum a, Bounded a, Eq a) => TestDirSet a where
  testDirName :: a -> String
  testDirType :: a -> TestType 

instance TestDirSet TestCaseFamily where 
  testDirName SucceedAll = "succeed-all"
  testDirName SucceedHeterogeneous = "succeed-heterogeneous"
  testDirName Fail = "fail"
  testDirName SlowAll = "slow-all"
  testDirName SlowHeterogeneous = "slow-heterogeneous"
  testDirName Constraints = "constraints"
  testDirName Benchmark = "benchmark"
  testDirName BenchmarkHeterogeneous = "benchmark-heterogeneous"

  testDirType SucceedAll             = Success
  testDirType SucceedHeterogeneous   = Success
  testDirType SlowAll                = Success
  testDirType SlowHeterogeneous      = Success
  testDirType Fail                   = Failure
  testDirType Constraints            = Success
  testDirType Benchmark              = Time
  testDirType BenchmarkHeterogeneous = Time

getTestFiles :: TestDirSet a => FilePath -> a -> IO [FilePath]
getTestFiles dir family = do
    let subDir = testDirName family
    paths <- sort <$> getAgdaFilesIn (dir </> subDir)
    return paths

getAgdaFilesIn :: FilePath -> IO [FilePath]
getAgdaFilesIn dir = do
    paths <- sort <$> globDir1 agdaGlob dir
    return paths
    where
      agdaGlob = compile "*.agda"





