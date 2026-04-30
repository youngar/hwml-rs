{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS -fno-warn-orphans #-}
module Tog.Term.FreeVars
  ( FreeVars(..)
  , fvAll
  , genericFreeVars, fastFreeVars
  , IsVarNotFree(..)
  , isVarNotFree
  , flexibilize
  , addVar
  ) where

import qualified Data.BitSet                      as B

import           Tog.Prelude
import           Tog.Names (Name)
import           Tog.Term.Core
import           Development.Placeholders
import           Control.Monad.Reader (ReaderT, runReaderT, ask, local)
import           Data.FreeLattice
import           Tog.Instrumentation.Debug
import qualified Tog.Instrumentation.Debug.Label as DL
import           Tog.PrettyPrint
--import           Tog.PrettyPrint                  ((//>))
--import qualified Tog.Instrumentation.Debug.Label as DL

#include "impossible.h"

-- Free variables
------------------------------------------------------------------------

fvAll :: FreeVarSet -> VarSet
fvAll fvs = fvRigid fvs <> fvFlexible fvs

fvIsFree :: Var -> FreeVarSet -> Bool
fvIsFree var fvs = B.member var (fvAll fvs)

st1 :: FreeVarSet -> FreeVarSet
st1 (FreeVarSet{fvRigid,fvFlexible}) =
  FreeVarSet{fvRigid    = strengthenVars_ 1 fvRigid
            ,fvFlexible = strengthenVars_ 1 fvFlexible
            }

-- | Returns a the variable of a variable/twin variable head
isVar :: Head t -> Maybe Var
isVar (Var v) = Just v
isVar (Twin _ v) = Just v
isVar _ = Nothing

instance FreeVars t a => FreeVars t (Elim a) where  
  freeVars (Apply t) = freeVars @t t
  freeVars (Proj{})  = return mempty

instance FreeVars t a => FreeVars t (Abs a) where
  freeVars (Abs_ a) = st1 <$> freeVars a

instance FreeVars t a => FreeVars t (Tel a) where
  freeVars = go
    where
      go T0 = pure mempty 
      go ((_, t) :> tel) = (<>) <$> freeVars t <*> (st1 <$> freeVars tel)

instance FreeVars t a => FreeVars t [a] where
  freeVars = fmap mconcat . mapM freeVars 

instance FreeVars t a => FreeVars t (Maybe a) where
  freeVars = fmap fold . mapM freeVars 

instance (FreeVars t a, FreeVars t b) => FreeVars t (a,b) where
  freeVars (a,b) = (<>) <$> freeVars a <*> freeVars b

instance (FreeVars t a, FreeVars t b) => FreeVars t (a :∈ b) where
  freeVars (a :∈ b) = (<>) <$> freeVars a <*> freeVars b

instance (FreeVars t a, FreeVars t b, FreeVars t c) => FreeVars t (a,b,c) where
  freeVars (a,b,c) = (<>) <$> freeVars a <*> ((<>) <$> freeVars b <*> freeVars c)

addVar :: Name -> VarSet -> VarSet
addVar name vs = B.insert (boundVar name) (weakenVars_ 1 vs)

flexibilize :: FreeVarSet -> FreeVarSet
flexibilize fvs = FreeVarSet{fvRigid = B.empty, fvFlexible = fvAll fvs}

-- | Rigid variables are those that are in the arguments of a metavariable
genericFreeVars
  :: forall t m. (MonadFreeVars t m)
  => t -> m FreeVarSet
genericFreeVars t = do
  {- let msg = do
        tDoc <- prettyM_ t
        return $
          "term:" //> tDoc
  t' <- maybeNf t
  debugBracket DL.FreeVars msg $ -} go t
  where
    go :: t -> m FreeVarSet
    go t0 = do
      tView <- view t0
      case tView of
        Lam body -> fv body
        Pi domain codomain ->
          (<>) <$> fv domain <*> fv codomain
        Equal type_ x y ->
          fv (type_, x, y)
        App (isVar -> Just v) elims -> do
          let fvs = FreeVarSet{fvRigid = B.singleton v, fvFlexible = B.empty}
          (fvs <>) <$> fv elims
        App h@(Def (Opened _ args)) elims -> do
          fvs1 <- fv args
          fvs2 <- fv elims
          neutral <- headIsNeutral h
          return $ (if neutral then id else flexibilize) $ fvs1 <> fvs2
        App (Meta _) elims -> do
          flexibilize <$> fv elims
        App J elims -> flexibilize <$> fv elims
        Set -> 
          return mempty
        Refl ->
          return mempty
        Con _ args ->
          fv args
        where
          fv :: forall a. FreeVars t a => a -> m FreeVarSet
          fv a = freeVars a >>= \(!fvs) -> return fvs

-- | This version is faster, but harder to memoize
fastFreeVars 
  :: forall t m. (MonadFreeVars t m)
  => t -> m FreeVarSet
fastFreeVars t = do
  {- let msg = do
        tDoc <- prettyM_ t
        return $
          "term:" //> tDoc
  t' <- maybeNf t
  debugBracket DL.FreeVars msg $ -} go Just t
  where
    lift' :: (Var -> Maybe Var) -> (Var -> Maybe Var)
    lift' f v =
      let _ = $(placeholderNoWarning "This lifting pattern is a bit inefficient, as it is applying the strenghtening n times") in
      if varIndex v > 0
      then f $ mkVar "varName v" (varIndex v - 1)
      else Nothing

    go :: (Var -> Maybe Var) -> t -> m FreeVarSet
    go strengthen' t0 = do
      tView <- view t0
      case tView of
        Lam (Abs_ body) ->
          go (lift' strengthen') body
        Pi domain (Abs_ codomain) ->
          (<>) <$> go strengthen' domain <*> go (lift' strengthen') codomain
        Equal type_ x y ->
          mconcat <$> mapM (go strengthen') [type_, x, y]
        App (isVar -> Just v) elims -> do
          let fvs = FreeVarSet (maybe B.empty B.singleton (strengthen' v)) B.empty
          (fvs <>) <$> (mconcat <$> mapM (go strengthen') [t | Apply t <- elims])
        App h@(Def (Opened _ args)) elims -> do
          fvs1 <- mconcat <$> mapM (go strengthen') args
          let elims' = [t | Apply t <- elims]
          fvs2 <- mconcat <$> mapM (go strengthen') elims'
          neutral <- headIsNeutral h
          return $ (if neutral then id else flexibilize) $ fvs1 <> fvs2
        App (Meta _) elims -> do
          flexibilize . mconcat <$> mapM (go strengthen') [t | Apply t <- elims]
        App J elims ->
          flexibilize . mconcat <$> mapM (go strengthen') [t | Apply t <- elims]
        Set ->
          return mempty
        Refl ->
          return mempty
        Con _ args ->
          mconcat <$> mapM (go strengthen') args

class IsVarNotFree t a where
  isVarNotFree_ :: MonadTerm t m => a -> ReaderT Var (WriterT (Meet DoesNotOccur) m) a
  default isVarNotFree_ :: (MonadTerm t m, a ~ t) => a -> ReaderT Var (WriterT (Meet DoesNotOccur) m) a
  isVarNotFree_ t = genericIsVarNotFree whnf t

-- class IsMetaNotFree t a where
--   isMetaNotFree_ :: MonadTerm t m => a -> ReaderT Meta m DoesNotOccur
--   isMetaNotFree_ = genericIsMetaNotFree whnf t 

isVarNotFree :: forall m t a. (IsVarNotFree t a, FreeVars t a, MonadTerm t m, PrettyM t a)
  => Var -> a -> m (a, DoesNotOccur)
isVarNotFree v a = do
  let msg = do
              vDoc <- prettyM_ v
              tDoc <- prettyM_ a
              return $
                  "v:" //> vDoc $$
                  "t:" //> tDoc
  debugBracket DL.IsVarNotFree msg $ do
    res <- do
    -- Try a simple check first
      fvs <- freeVars a
      if v `B.member` fvRigid fvs then 
        pure (a, Rigidly)
      else if v `B.member` fvFlexible fvs then
        -- Perform accurate check
        fmap (second getMeet) $ runWriterT $ flip runReaderT v $ isVarNotFree_ a
      else pure (a, DoesNotOccur)
    debug "result:" $ prettyM_ res
    return res

-- isMetaNotFree :: forall m t a. (IsVarNotFree t a, FreeVars t a, MonadTerm t m, PrettyM t a) => Meta -> a -> m DoesNotOccur
-- isMetaNotFree v a = do
--   let msg = do
--               vDoc <- prettyM_ v
--               tDoc <- prettyM_ a
--               return $
--                   "v:" //> vDoc $$
--                   "t:" //> tDoc
--   debugBracket DL.IsVarNotFree msg $ do
--     res <- do
--     -- Try a simple check first
--       fvs <- freeVars a
--       if v `B.member` fvRigid fvs then 
--         return Rigidly
--       else if v `B.member` fvFlexible fvs then
--         -- Perform accurate check
--         flip runReaderT v $ isVarNotFree_ a
--       else return DoesNotOccur
--     debug "result:" $ prettyM_ res
--     return res
-- 
-- Rigid variables are those that are in the arguments of a metavariable
genericIsVarNotFree :: forall a t m. (IsVarNotFree t t, MonadTerm t m, BlockedTerm t a)
    => (t -> m a) -> t -> ReaderT Var (WriterT (Meet DoesNotOccur) m) t
genericIsVarNotFree weakNf = go
    where
      go :: t -> ReaderT Var (WriterT (Meet DoesNotOccur) m) t
      go t0 = do
        wf <- lift$ lift$ weakNf t0
        censorJoin (Flexibly (maybe Bottom inj $ isBlocked wf)) $
          lift (lift (ignoreBlocking_ wf)) >>= \case
            Lam body -> join$ lam <$> isVarNotFree_ body
            Pi domain codomain ->
              join$ pi <$> isVarNotFree_ domain
                       <*> isVarNotFree_ codomain
            Equal type_ x y ->
              join$ equal <$> isVarNotFree_ type_
                          <*> isVarNotFree_ x
                          <*> isVarNotFree_ y
            App h elims -> join$ app <$> isVarNotFree_ h
                                     <*> mapM isVarNotFree_  elims
            Set  -> tell (pure DoesNotOccur) >> pure set
            Refl -> tell (pure DoesNotOccur) >> pure refl
            Con c args -> join$ con c <$> mapM isVarNotFree_ args

instance IsVarNotFree t a => IsVarNotFree t (Abs a) where
  isVarNotFree_ (Abs name t) = Abs name <$> (local (weakenVar_ 1) $ isVarNotFree_ t)

instance IsVarNotFree t a => IsVarNotFree t (Elim a) where
  isVarNotFree_ (Apply t)  = Apply <$> isVarNotFree_ t 
  isVarNotFree_ p@(Proj _) = tell (pure DoesNotOccur) >> pure p

instance IsVarNotFree t a => IsVarNotFree t (Head a) where
  isVarNotFree_ h@(Var v') = ask >>= \v ->
    tell (pure (if v == v' then Rigidly
                           else  DoesNotOccur)) >> pure h
  isVarNotFree_ Twin{} = __IMPOSSIBLE__
  isVarNotFree_ h@Meta{} = tell (pure DoesNotOccur) >> pure h
  isVarNotFree_ (Def op) = Def <$> isVarNotFree_ op
  isVarNotFree_ h@J      = tell (pure DoesNotOccur) >> pure h

instance IsVarNotFree t a => IsVarNotFree t (Opened k a) where
  isVarNotFree_ (Opened key args) = Opened key <$> mapM isVarNotFree_ args

instance IsVarNotFree t a => IsVarNotFree t (Tel a) where
  isVarNotFree_ T0 = tell (pure DoesNotOccur) >> pure T0
  isVarNotFree_ ((name, ty) :> tel) =
    (:>) <$> ((name,) <$> isVarNotFree_ ty) <*>
             (local (weakenVar_ 1) $ isVarNotFree_ tel)

instance IsVarNotFree t a => IsVarNotFree t (Maybe a) where
  isVarNotFree_ Nothing  = tell (pure DoesNotOccur) >> pure Nothing
  isVarNotFree_ (Just x) = Just <$> isVarNotFree_ x

instance (IsVarNotFree t a, IsVarNotFree t b) => IsVarNotFree t (a :∈ b) where
  isVarNotFree_ (a :∈ b) = (:∈) <$> isVarNotFree_ a <*> isVarNotFree_ b
