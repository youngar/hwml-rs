{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Tog.Term.MetaVars (
    runVisitMetasT
   ,runFoldMetas
   ,MonadVisit(..)
  {-
  occursDeep,
  metasDeep,
  occursShallow,
  metasShallow
  -}
  ) where

import           Tog.Prelude
import           Tog.Instrumentation
-- import qualified Tog.Instrumentation.Debug.Label as DL
import           Tog.Names
import           Tog.Names.Sorts
-- import           Tog.PrettyPrint                  ((//>), ($$))
import           Tog.Term.Core
import qualified Data.HashSet                     as HS
import           Data.HashSet (HashSet)
import           Control.Monad.State.Strict
import           Control.Monad.Reader
import           Data.FreeLattice
-- import           Data.FreeLattice

runFoldMetas :: (Metas t a, Monad m, MonoidM u) => (t -> m u) -> a -> m u
runFoldMetas f a = runReaderT (foldMetas a) f

-- Instances

instance Metas t (Term₀ t) where
  foldMetas (Term t) = ask >>= \f -> lift (f t)

instance Metas t (Elim t) where
  foldMetas (Apply t) = foldMetas (Term t)
  foldMetas (Proj _)  = memptyM

instance Metas t (Abs t) where
  foldMetas (Abs _ t) = foldMetas (Term t)

instance Metas t a => Metas t [a] where
  foldMetas xs = mconcatM $ map foldMetas xs

instance Metas t (Clause t) where
  foldMetas (Clause _ t) = foldMetas t

instance Metas t (ClauseBody t) where
  foldMetas cb = case cb of
    ClauseNoBody -> memptyM
    ClauseBody t -> foldMetas (Term t)

instance Metas t (Invertible t) where
  foldMetas (NotInvertible clauses) = foldMetas clauses
  foldMetas (Invertible injClauses) = foldMetas $ map snd injClauses

instance (Metas t a, Metas t b) => Metas t (a, b) where
  foldMetas (x, y) = foldMetas x `mappendM` foldMetas y

instance (Metas t a, Metas t b, Metas t c) => Metas t (a, b, c) where
  foldMetas (x, y, z) = foldMetas x `mappendM` foldMetas y `mappendM` foldMetas z

instance (ForAllQName (Metas t) f t, Metas t (f Projection t)) => Metas t (Definition f t) where
  foldMetas (Constant t c)             = foldMetas (Term t, c)
  foldMetas (DataCon dataCon _ type_)  = foldMetas (dataCon, coerce @_ @(Contextual t (Term₀ t)) type_)
  foldMetas (Projection _ tyCon type_) = foldMetas (tyCon, coerce @_ @(Contextual t (Term₀ t)) type_)
  foldMetas (Module _)                 = memptyM

instance (ForAllQName (Metas t) f t, Metas t (f Projection t)) => Metas t (Constant f t) where
  foldMetas Postulate               = memptyM
  foldMetas (Data dataCon)          = foldMetas dataCon
  foldMetas (Record dataCon fields) = foldMetas (dataCon, fields)
  foldMetas (Function inst)         = foldMetas inst

instance Metas t (FunInst t) where
  foldMetas Open     = memptyM
  foldMetas (Inst t) = foldMetas t

instance Metas t a => Metas t (Maybe a) where
  foldMetas Nothing  = memptyM
  foldMetas (Just x) = foldMetas x

instance Metas t (Signature t) where
  foldMetas sig =
    mconcatM
            [ foldMetas$ sigGetDefinition sig name
            | name <- sigDefinedNames sig ]

instance Metas t (Tel t) where
  foldMetas T0                  = memptyM
  foldMetas ((_, type_) :> tel) = foldMetas (Term type_, tel)

instance (Metas t a) => Metas t (Contextual t a) where
  
  foldMetas (Contextual x y) = foldMetas (x, y)

instance Metas t Name where
  foldMetas _ = memptyM

instance Metas t QName where
  foldMetas _ = memptyM

instance Metas t DefName where
  foldMetas _ = memptyM

instance Metas t ConName where
  foldMetas _ = memptyM

instance Metas t Projection where
  foldMetas _ = memptyM

instance (Metas t a) => Metas t (Const a b) where
  foldMetas (Const x) = foldMetas x

instance Metas t (MetaBody t) where
  foldMetas = foldMetas . Term . mbBody

instance IsQName qname => Metas t (Opened qname t) where
  foldMetas = foldMetas . coerce @_ @[Term₀ t] . opndArgs

instance Metas t (BlockedHead t) where
  foldMetas = \case
    BlockedOnFunction t -> foldMetas t
    BlockedOnJ -> memptyM

data MetasState = MetasState {
   _visitedQNames :: HashSet QName
 , _visitedMetas  :: HashSet Meta
 }
makeLenses ''MetasState

genericOnceFor :: (MonadState MetasState m, Eq a, Hashable a, Monoid u)
            => Lens' MetasState (HashSet a)
            -> a -> m u -> m u
genericOnceFor lens q m = do
  defs <- use lens
  if q `HS.member` defs then
    memptyM
  else do
    lens %= HS.insert q
    m

-- | Monad to explore definitions and metavariables recursively
newtype VisitDeepT m a = VisitDeepT {
  unVisitDeepT :: StateT MetasState -- Definitions and metas already explored
               m a
  } deriving (Functor, Applicative, Monad, MonadConf)

newtype VisitShallowT m a = VisitShallowT {
  unVisitShallowT :: m a
  } deriving (Functor, Applicative, Monad, MonadConf)

deriving instance MonadIO m => MonadIO (VisitDeepT m)
deriving instance MonadIO m => MonadIO (VisitShallowT m)

deriving instance MonadTerm t m => MonadTerm t (VisitShallowT m)
deriving instance MonadTerm t m => MonadTerm t (VisitDeepT m)

instance (Monad m) => MonadVisit (VisitDeepT m) where
  visitQName q = VisitDeepT . genericOnceFor visitedQNames q . unVisitDeepT
  visitMeta  v = VisitDeepT . genericOnceFor visitedMetas  v . unVisitDeepT

instance (Monad m) => MonadVisit (VisitShallowT m) where
  visitQName _ _ = memptyM
  visitMeta  _ _ = memptyM

instance Metas t t => Metas t (CtxType t) where
  foldMetas (Type t) = foldMetas t
  foldMetas (Dagger a b) = foldMetas (a, b)

runMetasStateT :: (Monad m) => StateT MetasState m a -> m a
runMetasStateT = flip evalStateT (MetasState HS.empty HS.empty)

{-
-- Meta set
metasShallow, metasDeep :: (MonadTerm t m, Metas t a, PrettyM t a) => a -> m (ISet Meta)
metasShallow t =
 let msg = do
             tDoc <- prettyM_ t
             return$ "t:" //> tDoc
 in
 debugBracket DL.Metas_shallow msg $ unVisitShallowT $ flip runReaderT MetaSetShallow $ foldMetas t

metasDeep t =
 let msg = do
             tDoc <- prettyM_ t
             return$ "t:" //> tDoc
 in
 debugBracket DL.Metas msg $ runMetasStateT $ unVisitDeepT $ flip runReaderT MetaSetDeep $ foldMetas t

-- Occurs check

occursShallow, occursDeep :: (MonadTerm t m, Metas t a, PrettyM t a) => Meta -> a -> m Bool
occursShallow mv t =
  let msg = do
          tDoc <- prettyM_ t
          mvDoc <- prettyM_ mv
          return$ 
            "mv:" //> mvDoc $$
            "t:" //> tDoc
  in
  debugBracket DL.Occurs_shallow msg $ fmap getAny $ unVisitShallowT $ flip runReaderT (OccursShallow mv) $ foldMetas t

occursDeep mv t =
  let msg = do
          tDoc <- prettyM_ t
          mvDoc <- prettyM_ mv
          return$ 
            "mv:" //> mvDoc $$
            "t:" //> tDoc
  in
  debugBracket DL.Occurs msg $ fmap getAny $ runMetasStateT $ unVisitDeepT $ flip runReaderT (OccursDeep mv) $ foldMetas t
-}

-- * Visiting
runVisitMetasT :: Monad m => VisitDeepT m t -> m t
runVisitMetasT = runMetasStateT . unVisitDeepT

-- This is a small DSL to define deep traversals of terms including metas and definitions,
-- where each definition is visited only once.
class Monad m => MonadVisit m where
  -- | Runs the given action once for each QName (i.e. if it has not
  --   been run for that QName before)
  visitQName :: Monoid a => QName -> m a -> m a

  -- | Runs the given action once for each Meta (i.e. if it has not
  --   been run for that Meta before)
  visitMeta  :: Monoid a => Meta  -> m a -> m a
