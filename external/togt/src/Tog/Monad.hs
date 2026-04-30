{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoImplicitPrelude #-}
-- | The monad that we use in elaboration, unification, and
-- type-checking in general.
module Tog.Monad
  ( -- * Monad definition
    TC
  , TC_
  , runTC
  , get
  , put
  , ask
  , asks
  , zoomTC
  , magnifyTC
  , magnifyStateTC
  , magnifyStateReaderTC
    -- * Operations
    -- ** Errors
  , catchTC
  , typeError
  , checkError
  , assert
  , assert_
    -- ** Source location
  , atSrcLoc
  , askSrcLoc
    -- ** Queries
  , getDefinition
  , getMetaType
  , metaIsInstantiated
    -- ** Signature update
  , addPostulate
  , addData
  , addRecordCon
  , addRecordConSignature
  , addTypeSig
  , addClauses
  , addProjection
  , addDataCon
  , addModule
  , addMeta
  , addMetaInCtx
  , uncheckedInstantiateMeta
    -- * Miscellanea
  , extendContext
  , unrollPi
  , unrollPiWithNames
    -- * Mixin
  , modifySignatureMixin
  ) where

import qualified Control.Lens                     as L
import           Control.Monad.State.Strict       (StateT(StateT), runStateT, MonadState(..))
import           Control.Monad.Reader             (MonadReader(..), asks)
import           Control.Monad.Trans.Except       (catchE)
import           Control.Monad.Error.Class        (MonadError)

import           Tog.Prelude
import           Tog.Instrumentation
import qualified Tog.Instrumentation.Debug.Label as DL
import           Tog.PrettyPrint                  ((<+>), ($$), (//>))
import qualified Tog.PrettyPrint                  as PP
import           Tog.Names
import           Tog.Names.Sorts
import           Tog.Term.Types
import           Tog.Error

-- Monad definition
------------------------------------------------------------------------

-- | The "type checking" monad.
--
-- It carries around a signature that we can modify, and also lets you
-- track of the current location in the source code.
--
-- Moreover, it's also a reader and state over some @r@ and @s@.
newtype TC t r s a = TC
  {unTC :: ExceptT TCErr (StateT (TCState t r s) (ConfT IO)) a}
  deriving (Functor, Applicative, Monad, MonadIO, MonadError TCErr, MonadConf)

type TC_ t a = forall r s. TC t r s a

data DocErr' d
    = DocErr SrcLoc d
    deriving (Typeable)

type DocErr = DocErr' PP.Doc
type TCErr = PP.Error' DocErr

data TCState t r s = TCState
    { _tsSignature        :: !(Signature t)
    , _tsSrcLoc           :: !SrcLoc
    , _tsEnv              :: !r
    , _tsState            :: !s
    } deriving (Functor)

makeLenses ''TCState

instance Bifunctor (TCState t) where
  bimap f g = over tsEnv f . over tsState g
  first = over tsEnv
  second = over tsState

instance PP.Pretty DocErr where
  pretty (DocErr p s) =
    "Error at" <+> PP.pretty p <+> ":" $$
    PP.nest 2 s

instance Show DocErr where
  show = PP.render

instance MonadReader r (TC t r s) where
  ask = TC $ do
    !r <- use tsEnv
    return r

  local f m = TC $ do
    oldEnv <- use tsEnv
    tsEnv %= f
    x <- unTC m
    tsEnv .= oldEnv
    return x

instance MonadState s (TC t r s) where
  get = TC $ do
    !s <- use tsState
    return s

  put x = TC $ tsState .= x

instance (IsTerm t) => MonadTerm t (TC t r s) where
  askSignature = TC $ use tsSignature
  modifySignatureMixin f = TC $ tsSignature L.%= withSignatureMixin f

runTC :: (IsTerm t, MonadConf m, MonadIO m)
      => Signature t -> r -> s -> TC t r s a
      -> m (Either PP.Error a, Signature t, s)
runTC sig env st m = do
  let ts = TCState sig noSrcLoc env st
  conf <- readConf
  mbErr <- liftIO$ flip runConfT conf$ runStateT (runExceptT (unTC m)) ts
  case mbErr of
    (Left e, ts')  -> return$ (Left (fmap PP.pretty e), ts'^.tsSignature, ts'^.tsState)
    (Right x, ts') -> return$ (Right x, ts'^.tsSignature, ts'^.tsState)

zoomTC :: Lens' s a -> TC t r a c -> TC t r s c
zoomTC l m = TC $ ExceptT $ StateT $ \ts0 -> do
  !s0 <- pure$ second (L.view l) ts0
  !s1 <- pure$ ts0^.tsState
  (!mbErr, !ts1) <- runStateT (runExceptT (unTC m)) s0
  !ts2 <- pure$ second (\x -> L.set l x s1) ts1
  return (mbErr, ts2)

magnifyTC :: (r -> a) -> TC t a s c -> TC t r s c
magnifyTC l m = TC $ ExceptT $ StateT $ \ts0 -> do
  (!mbErr, !ts1) <- runStateT (runExceptT (unTC m)) (first l ts0)
  !ts2 <- pure$ first (const (ts0^.tsEnv)) ts1
  return (mbErr, ts2)

magnifyStateTC :: (s -> a) -> TC t r a c -> TC t r s c
magnifyStateTC l m = TC $ ExceptT $ StateT $ \ts0 -> do
  (!mbErr, !ts1) <- runStateT (runExceptT (unTC m)) (second l ts0)
  !ts2 <- pure$ second (const (ts0^.tsState)) ts1
  return (mbErr, ts2)

-- Helps storing some read-only information in the state.
-- (it can be modified, but the changes will be thrown out)
-- The state is otherwise preserved
magnifyStateReaderTC :: s -> TC t r (a,s) c -> TC t r a c
magnifyStateReaderTC s m = TC $ ExceptT $ StateT $ \ts0 -> do
  (!mbErr, !ts1) <- runStateT (runExceptT (unTC m)) (fmap (,s)$ ts0)
  !ts2 <- pure$ fmap fst$ ts1
  return (mbErr, ts2)

-- Errors
------------------------------------------------------------------------

catchTC :: TC t r s a -> TC t r s (Either PP.Error a)
catchTC m = TC $ catchE (Right <$> unTC m) $ return . Left . fmap PP.pretty

-- | Fail with an error message.
typeError :: PP.Error -> TC t r s b
typeError err = TC $ do
  printStackTrace "typeError" err
  !loc <- use tsSrcLoc
  throwE $ DocErr loc <$> err

-- | Fail with an error token
checkError :: (IsTerm t) => CheckError t -> TC_ t a
checkError err = typeError =<< ppCheckError err

assert :: (PP.Doc -> TC t r s PP.Doc) -> TC t r s a -> TC t r s a
assert msg m = do
  mbErr <- catchTC m
  case mbErr of
    Left err -> fatalError . PP.render =<< traverse msg err
    Right x  -> return x

assert_ :: (PP.Doc -> PP.Doc) -> TC t r s a -> TC t r s a
assert_ msg = assert (return . msg)

-- SrcLoc
------------------------------------------------------------------------

-- | Run some action with the given 'SrcLoc'.
atSrcLoc :: HasSrcLoc a => a -> TC t r s b -> TC t r s b
atSrcLoc l !m = TC $ do
  !oldLoc <- use tsSrcLoc
  !newLoc <- pure$ srcLoc l
  tsSrcLoc .= newLoc
  x <- unTC m
  tsSrcLoc .= oldLoc
  return x

askSrcLoc :: TC_ t SrcLoc
askSrcLoc = TC$ do
  !loc <- use tsSrcLoc
  return loc

-- Signature
------------------------------------------------------------------------

addPostulate :: PDefName -> Tel t -> Type t -> TC t r s ()
addPostulate f tel type_ = do
  modifySignature $ \sig -> sigAddPostulate sig f tel type_

addData :: TyConName -> Tel t -> Type t -> TC t r s ()
addData f tel type_ = do
  modifySignature $ \sig -> sigAddData sig f tel type_

addRecordCon :: Opened TyConName t -> RConName -> TC t r s ()
addRecordCon tyCon dataCon = do
  modifySignature $ \sig -> sigAddRecordCon sig tyCon dataCon

addTypeSig :: IsDefName defName => defName -> Tel t -> Type t -> TC t r s ()
addTypeSig f tel type_ = do
  modifySignature $ \sig -> sigAddTypeSig sig f tel type_

addClauses :: Opened FDefName t -> Invertible t -> TC t r s ()
addClauses f cs = modifySignature $ \sig -> sigAddClauses sig f cs

addProjection
  :: Projection -> Opened TyConName t -> Contextual t (Type t) -> TC t r s ()
addProjection proj tyCon ctxtType =
  modifySignature $ \sig -> sigAddProjection sig (pName proj) (pField proj) tyCon ctxtType

addDataCon
  :: DConName -> Opened TyConName t -> Natural -> Contextual t (Type t) -> TC t r s ()
addDataCon dataCon tyCon numArgs ctxtType =
  modifySignature $ \sig -> sigAddDataCon sig dataCon tyCon numArgs ctxtType

addRecordConSignature
  :: RConName -> Opened TyConName t -> Natural -> Contextual t (Type t) -> TC t r s ()
addRecordConSignature dataCon tyCon numArgs ctxtType =
  modifySignature $ \sig -> sigAddRecordConSignature sig dataCon tyCon numArgs ctxtType

addModule :: (IsTerm t) => QName -> Tel t -> Module t -> TC t r s ()
addModule moduleName tel names = do
  debugBracket_ DL.AddModule (PP.pretty moduleName) $
    modifySignature $ \sig -> sigAddModule sig moduleName tel names

addMeta :: forall t r s. (IsTerm t) => Type t -> TC t r s Meta
addMeta type_ = do
  loc <- askSrcLoc
  ts <- TC get
  let (mv, sig') = sigAddMeta (ts^.tsSignature) loc type_
  TC $ tsSignature .= sig'
  let msg = do
        typeDoc <- prettyM_ type_
        return $
          "mv:" //> PP.pretty mv $$
          "type:" //> typeDoc
  debugBracket DL.AddMeta msg $ return mv

addMetaInCtx
  :: (IsTerm t)
  => Ctx t -> Type t -> TC_ t (Meta, Term t)
addMetaInCtx ctx type_ = do
  type' <- ctxPi ctx type_
  mv <- addMeta type'
  (mv,) <$> ctxApp (meta mv []) ctx

uncheckedInstantiateMeta :: Meta -> MetaBody t -> TC t r s ()
uncheckedInstantiateMeta mv mvb =
  modifySignature $ \sig -> sigInstantiateMeta sig mv mvb

metaIsInstantiated :: MonadTerm t m => Meta -> m Bool
metaIsInstantiated mv = askSignature <&> flip sigMetaIsInstantiated mv

-- Utils
------------------------------------------------------------------------

modifySignature :: (Signature t -> Signature t) -> TC t r s ()
modifySignature f = do
  !ts <- TC get
  let !sig' = f $ ts ^. tsSignature
  TC $ tsSignature .= sig'

-- Miscellanea
------------------------------------------------------------------------

-- Miscellanea
------------------------------------------------------------------------

-- Telescope & context utils
----------------------------

-- | Useful just for debugging.
extendContext :: (MonadTerm t m, PrettyM t a) => Ctx a -> (Name, a) -> m (Ctx a)
extendContext ctx type_ = do
  let ctx' = ctx :< type_
  debug "extendContext" $ prettyM_ ctx'
  return ctx'

-- Unrolling Pis
----------------




unrollPi
  :: (IsTerm t, MonadTerm t m)
  => Type t
  -- ^ Type to unroll
  -> m (Tel (Type t), Type t)
unrollPi type_ =
  debugBracket DL.UnrollPi (pure "") $ debugResult "unrolled:" $ unrollPiCached type_

unrollPiCached
  :: (IsTerm t, MonadTerm t m)
  => Type t
  -- ^ Type to unroll
  -> m (Tel (Type t), Type t)
unrollPiCached = memoize UnrollPiCache $ \type_ -> inspect$ do
    typeView <- whnfView type_
    case typeView of
      Pi domain codomain -> do
        name <- getAbsName_ codomain
        (ctx, endType) <- unrollPi (unAbs codomain)
        return ((name, domain) :> ctx, endType)
      _ ->
        return (T0, type_)

unrollPiWithNames
  :: (IsTerm t)
  => Type t
  -- ^ Type to unroll
  -> [Name]
  -- ^ Names to give to each parameter
  -> TC_ t (Tel (Type t), Type t)
  -- ^ A telescope with accumulated domains of the pis and the final
  -- codomain.
unrollPiWithNames type_ [] =
  return (T0, type_)
unrollPiWithNames type_ (name : names) = do
  typeView <- whnfView type_
  case typeView of
    Pi domain (Abs_ codomain) -> do
      (ctx, endType) <- unrollPiWithNames codomain names
      return ((name, domain) :> ctx, endType)
    _ -> do
      checkError $ ExpectingPi type_
