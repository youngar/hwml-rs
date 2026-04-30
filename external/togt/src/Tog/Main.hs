{-# LANGUAGE ApplicativeDo #-}
module Tog.Main (main, processFile) where

import           Prelude                          hiding (interact)

import           Options.Applicative
import           Options.Applicative.Types
import           System.Exit                      (exitWith, ExitCode(ExitFailure,ExitSuccess))
import           System.Environment               (getArgs)
import           Data.List.Split                  (splitOn)
import           Data.List                        (intercalate)

import           Tog.Instrumentation
import           Tog.Instrumentation.Debug.Label  (debugLabelFromString, debugLabelToString)
import           Tog.PrettyPrint                  ((<+>), ($$))
import qualified Tog.PrettyPrint                  as PP
import           Tog.Prelude
import           Tog.Term
import           Tog.Term.Impl
import           Tog.CheckFile
import           Tog.Parse
import           Tog.ScopeCheck
import           Tog.Unify
import           Tog.Error                        (ppScopeError, ppParseError)

import           Development.GitRev

parseTypeCheckConf :: Parser Conf
parseTypeCheckConf = do

  confTermType <- strOption
      ( long "termType" <> short 't' <> value "S" <>
        help ("Available types: " <> documentModules checkers <> ".")
      )

  confSolver <- strOption
      ( long "solver" <> value "S" <>
        help ("Available solvers: " <> documentModules solvers <> ".")
      )

  confDebugLabels <- debugLabelsOption
      ( long "debug" <> short 'd' <> value mempty <>
        help ("Select debug labels to print (separated by |). -d '' will print all the debug messages.\n Available labels:" <>
               (intercalate ", " $ map debugLabelToString $ enumAll))
      )

  confStackTrace <- switch
      ( long "stackTrace" <> short 's' <>
        help "Print a stack trace on error."
      )

  confQuiet <- switch
      (long "quiet" <> short 'q' <> help "Do not print any output.")

  confNoMetasSummary <- switch
      ( long "noMetasSummary" <>
        help "Do not print a summary of the metavariables state."
      )

  confMetasReport <- switch
      ( long "metasReport" <>
        help "Print a detailed report of the metavariables state."
      )

  confMetasOnlyUnsolved <- switch
      ( long "metasOnlyUnsolved" <>
        help "In the metavariable report, only print information about the unsolved metavariables."
      )

  confNoProblemsSummary <- switch
      ( long "noProblemsSummary" <>
        help "Do not print a summary of the unsolved problems."
      )

  confProblemsReport <- switch
      ( long "problemsReport" <>
        help "Print a detailed report of the unsolved problems."
      )

  confCheckMetaConsistency <- switch
      ( long "checkMetaConsistency" <>
        help "Check consistency of instantiated term of a metavar and its type, and double instantiations."
      )

  confSynEquality <- synEqLevelOption
      ( long "synEquality" <> value OneSynEq <>
        help "Syntactic equality level: 0 (None), 1 (When first encountering a constraint), 2 (All the time)."
      )

  confDontNormalizePP <- switch
      ( long "dontNormalizePP" <>
        help "Don't normalize terms before pretty printing them"
      )

  confWhnfApplySubst <- switch
      ( long "whnfApplySubst" <>
        help "Reduce term when applying a substitution"
      )

  confTimeSections <- switch
      ( long "timeSections" <>
        help "Measure how much time is taken by each debug section"
      )

  confWhnfEliminate <- switch
      ( long "whnfEliminate" <>
        help "Reduce term when eliminating a term"
      )

  confPhysicalEquality <- switch
      ( long "physicalEquality" <>
        help "Use physical equality"
      )

  confNoCheckElaborated <- switch
      ( long "noCheckElaborated" <>
        help "Do not check the types of elaborated terms"
      )
  confNfInUnifier <- switch
      ( long "nfInUnifier" <>
        help "Convert terms to WHNF when doing inversion and pruning"
      )
  confFastDebug <- switch
      ( long "fastDebug" <>
        help "Do not compute debug messages for non-enabled labels" )

  confPopularityContest <- switch
      ( long "popularityContest" <>
        help "Report how many times each constraint was encountered." )

  confStats <- switch
      ( long "stats" <>
        help "Report interesting statistics on execution." )

  confUnifyAudit <- switch
      ( long "audit" <>
        help "Audit unification by checking whether both sides of all solved constraints are ηβδ-equal." )

  confFastElaborate <- switch
      ( long "fastElaborate" <>
        help "Shorcuts in the elaboration to reduce the number of metavariables and constraints" )

  confDelayedDispatch <- switch
      ( long "delayedDispatch" <>
        help "Dispatches constraints as soon as they are created" )

  confParanoidSyntacticEquality <- switch
      ( long "paranoidSyntacticEquality" <>
        help "Require constraints with syntactically equal terms to also have syntactically equal contexts and types before being considered solved" )

  confParanoidContextCurrying <- switch
      ( long "paranoidContextCurrying" <>
        help "Require variables in the context to have syntactically equal types on both sides of the context before expanding them (unimplemented, currently disables context currying entirely)" )

  return Conf{..}

parserInfo :: ParserInfo Conf
parserInfo = info parseTypeCheckConf $
  header "Tog⁺"
  <> progDesc "A dependent type-checker prototype"
  <> failureCode 42

defaultConf :: Conf
Just defaultConf = getParseResult$ execParserPure defaultPrefs parserInfo []

debugLabelsOption
  :: Mod OptionFields DebugLabels
  -> Parser DebugLabels
debugLabelsOption = option $ do
  s <- readerAsk
  case s of
    [] -> return DLAll
    _  -> DLSome <$> mapM parseLabel (splitOn "|" s)
  where
    parseLabel s = 
      case debugLabelFromString s of 
        Just lbl -> return lbl
        Nothing  -> fail$ "Unknown debug label: " <> s

synEqLevelOption
  :: Mod OptionFields SynEqLevel
  -> Parser SynEqLevel
synEqLevelOption = option $ do
  s <- readerAsk
  case s of
    "0" -> return NoSynEq
    "1" -> return OneSynEq
    "2" -> return AllSynEq
    _   -> fail$ "Invalid syntactic equality level: " <> s

parseMain :: Parser (IO ())
parseMain =
  typeCheck
    <$> argument str (metavar "FILE")
    <*> parseTypeCheckConf
  where
    typeCheck file conf = flip runConfT conf $ do
      instrument $ do
        silent <- confQuiet <$> readConf
        unless silent $ liftIO $ do
          putStrLn gitRevMsg
          args <- getArgs
          putStrLn$ "Options: " ++ intercalate " " args
        processFile file $ \_ mbErr -> do
          liftIO$ forM_ mbErr $ \PP.Error{errCode,errDoc} -> do
            putStrLn (PP.render errDoc)
            exitWith (ExitFailure errCode)

-- | Parses, scope-checks and type-checks a file, calling the error handler if
--   appropiate
processFile
  :: forall m a. (MonadConf m, MonadIO m)
  => FilePath
  -- ^ Path to the file
  -> (forall t. (IsTerm t) => Signature t -> Maybe PP.Error -> m a)
  -- ^ Error handler
  -> m a
processFile file ret = do
  mbErr <- liftIO $ runExceptT $ do
    s   <- lift $ readFile file
    raw <- exceptShowErr ppParseError "Parse" $ parseModule s
    exceptShowErr ppScopeError "Scope" $ scopeCheckModule raw
  case mbErr of
    Left err  -> (sigEmpty :: m (Signature Simple)) >>= flip ret (Just err)
    Right int -> checkFile int $ \sig mbErr' ->
                 ret sig (fmap (showError "Type") <$> mbErr')
  where
    showError errType err =
      PP.text errType <+> "error: " $$ PP.nest 2 err

    exceptShowErr wrapper errType =
      ExceptT . return . either (Left . wrapper . showError errType) Right

main :: IO ()
main = do
  maybeShowVersionAndExit
  join $ execParser $ info (helper <*> parseMain) fullDesc

maybeShowVersionAndExit :: IO ()
maybeShowVersionAndExit = do
  args <- getArgs
  if "--version" `elem` args then do
    putStrLn gitRevMsg
    exitWith ExitSuccess
  else
    return ()

gitRevMsg :: String
gitRevMsg = concat [ $(gitBranch), "@", $(gitHash), dirty ]
  where
        dirty | $(gitDirtyTracked) = "-dirty"
              | otherwise   = ""
