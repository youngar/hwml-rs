{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE IncoherentInstances #-}
-- | Top-level module with type-theory functionality
module Tog.Term.Types
  ( module Tog.Term.Core
  , module Tog.Term.Guard
  , module Tog.Term.Synonyms
  , module Tog.Term.FreeVars
  , whnfBlocked  
  , maybeNf
  , maybeNfElseWhnf
  , maybeNfElseExpandMetas
  , instantiateMaybeNf
  , instantiateMaybeNf_
  ) where
  
import Tog.Term.Core
import Tog.Term.Synonyms
import Tog.Term.Guard
import Tog.Term.FreeVars
import Tog.Names.Sorts
import Tog.Prelude
import Tog.Instrumentation
import qualified Tog.Instrumentation.Debug.Label as DL

import           Tog.PrettyPrint                  ((//>))

whnfBlocked :: (MonadTerm t m) => t -> m (Either (Guard, t) (t, TermView t))
whnfBlocked t = do
  t' <- whnf t
  case t' of
    NotBlocked t''       -> (Right . (t'',)) <$> view t''
    BlockingHeadMeta mv es -> (Left . (metaGuard mv,)) <$> meta mv es
    BlockingHeadDef  key@(Opened name _) es -> (Left . (qNameGuard $ getQName name,)) <$> def key es
    BlockedOn mvs bh es -> (Left . (mvs,)) <$> ignoreBlockedOn bh es

maybeNfElseExpandMetas :: (IsTerm t, ExpandMetas t a, Nf t a, PrettyM t a, MonadTerm t m) => a -> m a
maybeNfElseExpandMetas t = 
  let msg = do
        tDoc <- prettyM_ t
        return$ "t:" //> tDoc
  in
  debugBracket DL.MaybeNf msg $ do
    doNf <- confNfInUnifier <$> readConf
    if doNf then nf t else evalExpandMetas t


maybeNf :: (IsTerm t, Nf t a, PrettyM t a, MonadTerm t m) => a -> m a
maybeNf t = 
  let msg = do
        tDoc <- prettyM_ t
        return$ "t:" //> tDoc
  in
  debugBracket DL.MaybeNf msg $ do
    doNf <- confNfInUnifier <$> readConf
    if doNf then nf t else return t

maybeNfElseWhnf :: (HasSubterms t a, Nf t t, IsTerm t, PrettyM t a, MonadTerm t m) => a -> m a 
maybeNfElseWhnf t =
  let msg = do
        tDoc <- prettyM_ t
        return$ "t:" //> tDoc
  in
  debugBracket DL.MaybeNf msg $ do
    doNf <- confNfInUnifier <$> readConf
    traverseSubterms t (if doNf then nf else whnf >=> ignoreBlocking)

instantiateMaybeNf :: (IsTerm t, Nf t a, ApplySubst t a, PrettyM t a, MonadTerm t m) => a -> [Term t] -> m a
instantiateMaybeNf t as = join$ instantiate <$> maybeNf t <*> maybeNf as

instantiateMaybeNf_ :: (IsTerm t, Nf t a, PrettyM t a, ApplySubst t a, MonadTerm t m) => Abs a -> Term t -> m a
instantiateMaybeNf_ t a = join$ instantiate_ <$> maybeNf t <*> maybeNf a


