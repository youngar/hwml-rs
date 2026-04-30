{-# LANGUAGE NoImplicitPrelude #-}
module Tog.Instrumentation.Debug
  ( -- * Init
    debugInit
    -- * API
  , DebugLabel
  , debugBracket
  , debugBracket_
  , debugBracket0
  , debug
  , debug_
  , debugWhenLabel
  , whenDebug
  , fatalError
  , stackTrace
  , printStackTrace
  , printRaw
  , matchLabel
  ) where

import           Data.IORef                       (IORef, newIORef, readIORef, writeIORef)
import           System.IO.Unsafe                 (unsafePerformIO)

import           Tog.Instrumentation.Debug.Label (DebugLabel)
import           Tog.Instrumentation.Conf
import           Tog.Instrumentation.Timing
import           Tog.Prelude
import           Tog.PrettyPrint                  as PP

data DebugFrame = DebugFrame
  { dfDoc   :: !PP.Doc
  , dfLabel :: !DebugLabel
  }

_dummy :: a
_dummy = error "UNUSED" dfDoc

instance PP.Pretty DebugFrame where
  pretty (DebugFrame doc label) = "***" <+> PP.pretty label $$ doc

type DebugStack = [DebugFrame]

{-# NOINLINE stackRef #-}
stackRef :: IORef (Maybe DebugStack)
stackRef = unsafePerformIO $ newIORef Nothing

_ERROR_INDENT :: Natural
_ERROR_INDENT = 2

debugInit :: (MonadIO m, MonadConf m) => m ()
debugInit = do
  conf <- readConf
  writeStackRef $ if confDebug conf then Just [] else Nothing

rawDebug :: (MonadIO m) => DebugStack -> PP.Doc -> PP.Doc -> m String
rawDebug stack label doc = do
  let s  = PP.renderPretty 100 $ label $$ doc
  let pad = replicate (length stack * _ERROR_INDENT) ' '
  return $ unlines $ map (pad ++) $ lines s

printRawDebug :: (MonadIO m) => DebugStack -> PP.Doc -> PP.Doc -> m ()
printRawDebug stack label doc =
  liftIO . hPutStr stderr =<< rawDebug stack label doc

printRaw :: (MonadIO m) => String -> m ()
printRaw = liftIO . hPutStrLn stderr

matchLabel :: (MonadIO m, MonadConf m) => DebugLabel -> m () -> m () 
matchLabel label m = ifLabel label m $ return ()

ifLabel :: (MonadIO m, MonadConf m) => DebugLabel -> m a -> m a -> m a
ifLabel label mYes mNo = do
  debugLabels <- confDebugLabels `liftM` readConf
  case debugLabels of
    DLAll                       -> mYes
    DLSome ls | label `elem` ls -> mYes
    _                           -> mNo

debugWhenLabel :: (MonadIO m, MonadConf m) => DebugLabel -> m PP.Doc -> m ()
debugWhenLabel label m = matchLabel label $ do
  mbStack <- readStackRef
  forM_ mbStack $ \stack ->
    m >>= printRawDebug stack ("**" <+> pretty label)

readStackRef :: (MonadIO m) => m (Maybe DebugStack)
readStackRef = liftIO $ readIORef stackRef

writeStackRef :: (MonadIO m) => Maybe DebugStack -> m ()
writeStackRef mbStack = liftIO $ writeIORef stackRef mbStack

debugBracket :: (MonadIO m, MonadConf m) => DebugLabel -> m PP.Doc -> m a -> m a
debugBracket label docM m = do
  mbStack <- readStackRef
  forM_ mbStack $ \stack -> do
    alwaysRender <- not . confFastDebug <$> readConf
    doc <- if alwaysRender then
             docM
           else
             ifLabel label docM (return mempty)
    matchLabel label $ printRawDebug stack ("<<<" <+> PP.pretty label) doc
    let frame = DebugFrame doc label
    writeStackRef $ Just $ frame : stack

  timing <- confTimeLabel label `liftM` readConf
  x <- if timing then timingBracket label m else m
  mbStack' <- readStackRef
  forM_ mbStack' $ \(_:stack) -> do
    matchLabel label $ printRawDebug stack (">>>" <+> PP.pretty label) mempty
    writeStackRef $ Just stack
  return x

debugBracket_ :: (MonadIO m, MonadConf m) => DebugLabel -> PP.Doc -> m a -> m a
debugBracket_ label doc = debugBracket label (return doc)

debug :: (MonadIO m, MonadConf m) => PP.Doc -> m PP.Doc -> m ()
debug label docM = do
  mbStack <- readStackRef
  forM_ mbStack $ \stack -> case stack of
    frame : _ -> do
      matchLabel (dfLabel frame) $ do
        doc <- docM
        printRawDebug stack ("**" <+> label) doc
    [] -> do
      return ()

debug_ :: (MonadIO m, MonadConf m) => PP.Doc -> PP.Doc -> m ()
debug_ label doc = debug label (return doc)

debugBracket0 :: (MonadIO m, MonadConf m) => DebugLabel -> m a -> m a
debugBracket0 lbl = debugBracket_ lbl mempty

whenDebug :: (MonadIO m) => m () -> m ()
whenDebug m = do
  mbStack <- readStackRef
  forM_ mbStack $ \_ -> m

renderStackTrace :: PP.Doc -> DebugStack -> PP.Doc
renderStackTrace err stack =
  "error:" //> err $$
  "stack trace:" //> PP.indent _ERROR_INDENT (PP.vcat (map PP.pretty stack))

stackTrace :: (MonadIO m) => PP.Doc -> PP.Doc -> m (Maybe String)
stackTrace heading err = do
  mbStack <- readStackRef
  forM mbStack $ \stack ->
    rawDebug [] ("***" <+> heading) (renderStackTrace err stack)

printStackTrace :: (MonadIO m) => PP.Doc -> PP.Error -> m ()
printStackTrace heading PP.Error{errDoc} = do
  mbS <- stackTrace heading errDoc
  liftIO $ forM_ mbS $ hPutStrLn stderr

{-# NOINLINE fatalError #-}
fatalError :: String -> a
fatalError s =
  let mbS = unsafePerformIO $ stackTrace "fatalError" $ PP.string s
  in case mbS of
       Nothing -> error $ "\nfatalError\n" ++ s
       Just s' -> error $ "\n" ++ s'

