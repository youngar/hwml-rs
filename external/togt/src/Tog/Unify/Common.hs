{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS -fno-warn-partial-type-signatures #-}
module Tog.Unify.Common
{-       (
    -- * Twins 
  , KillTwins(..)
  , TwinVarSet(..)
  , tvSingleton, tvInsert, tvMember
  , twinSet               
  , strengthenTwinVars_
  , fastKillTwinsE ) -}
  {-
  , genericNfEq
  , etaContractMaybe
  , applyProjectionType
-}

  where


import qualified Prelude
import qualified Data.ISet                        as I
import qualified Data.BitSet                      as B
import qualified Data.Set                         as Set
import           Data.Tree                        (Tree(Node), subForest, rootLabel, Forest)
import           Data.Collect
import           Data.FreeLattice (inj,DecBottom,DecTop
                                  ,pattern Top
                                  ,pattern Bottom)

import           Control.Monad.Writer.Strict      (WriterT, runWriterT, tell, Endo(..), censor, writer)
import           Control.Monad.Reader             (ReaderT, runReaderT, local, ask)
import           Control.Monad.Except
import           Control.Lens                      ((%~), (.~), (&), (^.))

import           Tog.Instrumentation
import qualified Tog.Instrumentation.Debug.Label as DL
import           Tog.Names
import           Tog.Names.Sorts
import           Tog.Prelude
import           Tog.PrettyPrint                  (($$), (<+>), (//>))
import qualified Tog.PrettyPrint                  as PP
import           Tog.Term
import           Tog.Term.FreeVars                (addVar)
import           Tog.Monad
import           Tog.TypeCheck                    (instantiateMeta)
import           Tog.Error

import           Development.Placeholders
#include "impossible.h"

type Unify t = (IsTerm t, Prune t t, KillTwins t t, IsVarNotFree t t)

-- Pruning
------------------------------------------------------------------------

{-# WARNING curryMeta "Remove this, do the unrolling on-demand in prune." #-}
-- | @curryMeta t@ checks if @t = α ts@ and for every argument
-- of the metavar which is a record type it splits it up in separate
-- arguments, one for each field.
curryMeta
  :: forall t r s. (IsTerm t) => Term t -> TC t r s (Term t)
curryMeta t = do
  let msg = do
        tDoc <- prettyM_ t
        return $
          "term:" //> tDoc
  debugBracket DL.CurryMeta msg $ fmap (fromMaybe t) $ runMaybeT $ do
    App (Meta mv) _ <- lift $ viewW t
    (tel, mvType) <- lift $ unrollPi =<< getMetaType mv
    (True, args0, newMvType) <- lift $ go tel mvType
    lift $ do
      let abstractions = length args0
      args <- toArgs args0
      newMv <- addMeta newMvType
      mvT <- meta newMv $ map Apply args
      let mi = MetaBody abstractions mvT
      debug "unrolled" $ runNamesT C0$ do
        mvTypeDoc <- prettyM =<< telPi tel mvType
        newMvTypeDoc <- prettyM newMvType
        mvTDoc <- prettyM mi
        return $
          "old type:" //> mvTypeDoc $$
          "new type:" //> newMvTypeDoc $$
          "term:" //> mvTDoc
      instantiateMeta mv mi
      -- Now we return the old type, which normalized will give the new
      -- mv.
      return t
  where
    treePaths :: Tree a -> [[a]]
    treePaths tr | null (subForest tr) = [[rootLabel tr]]
    treePaths tr = concatMap (map (rootLabel tr :) . treePaths)  (subForest tr)

    toArgs :: MetaArgs t -> TC t r s [Term t]
    toArgs args = fmap concat $ forM args $ \mbArg -> do
      case mbArg of
        Nothing -> do
          return []
        Just (v, projs) -> do
          let projsPaths = concatMap treePaths projs
          if null projsPaths
            then do
              t' <- app (Var v) []
              return [t']
            else do
              mapM (app (Var v) . map Proj) projsPaths

    go :: Tel t -> Type t -> TC t r s (Bool, MetaArgs t, Type t)
    go T0 type_ = do
      return (False, [], type_)
    go ((n, dom) :> tel) type0 = do
      let fallback = do
            (changed, args, type1) <- go tel type0
            let argVar = weakenVar_ (length args) $ boundVar n
            type2 <- pi dom (Abs n type1)
            return (changed, Just (argVar, []) : args, type2)
      domView <- whnfView dom
      case domView of
        App (Def tyCon) elims -> do
          tyConDef <- getDefinition tyCon
          case tyConDef of
            -- Only curry meta for records of more than one field
            -- This avoids problems with variables of unit type `disappearing`
            -- from the metavariable telescope.
            Constant _ (Record dataCon openedProjs@(_:_)) -> do
              let projs = map opndKey openedProjs
              let Just tyConPars = mapM isApply elims
              DataCon _ _ dataConType <- getDefinition dataCon
              appliedDataConType <- openContextual dataConType tyConPars
              debug_ "tyConPars" $ PP.text $ show $ show tyConPars
              (dataConPars0, _) <-
                assert_ ("curryMeta, unrollPiWithNames:" <+>) $
                unrollPiWithNames appliedDataConType (map (qNameName . getQName . pName . opndKey) openedProjs)
              let dataConPars = telToCtx dataConPars0
              let numDataConPars = ctxLength dataConPars
              recordTerm <- con dataCon =<< mapM var (ctxVars dataConPars)
              let telLen = telLength tel
              let weakenBy = numDataConPars
              if weakenBy <= 0
                -- This means that the type was unit.
                then do
                  tel' <- instantiate (coerce tel :: Tel (OpenTerm t)) [recordTerm]
                  type1 <- applySubst type0 . subLift telLen =<< subSingleton recordTerm
                  (_, args, type2) <- go (dataConPars `telAppend` coerce tel') type1
                  return (True, Nothing : args, type2)
                else do
                  sub <- subInstantiate recordTerm $ subWeaken numDataConPars subId
                  tel' <- applySubst (coerce tel :: Tel (OpenTerm t)) sub
                  type1 <- applySubst type0 $ subLift telLen sub
                  (_, args, type2) <- go (dataConPars `telAppend` coerce tel') type1
                  let (argsL, argsR) = strictSplitAt (length projs) args
                  let argVar = weakenVar_ (length argsR) $ boundVar n
                  let argL = ( argVar
                             , [ Node proj projs'
                               | (proj, Just (_, projs')) <- zip projs argsL
                               ]
                             )
                  return (True, Just argL : argsR, type2)
            _ -> do
              fallback
        _ -> do
          fallback

-- Prune
----------

class IsTerm t => Prune t a where
  -- | @pruneTerm vs t@ tries to remove all the variables that are not
  --   in @vs@ by instantiating metavariables that can make such
  --   variables disappear.  Always succeeds, but might not eliminate
  --   all the variables.
  prune :: 
       VarSet                -- ^ allowed vars
    -> a
    -> TC t r s a
  default prune :: (t ~ a) => VarSet -> a -> TC t r s a
  prune = genericPruneTerm

{-# INLINE debugPruneTerm #-}
debugPruneTerm :: MonadTerm t m => (VarSet -> t -> m a) -> VarSet -> t -> m a
debugPruneTerm f vs t =    
  let msg = do
        tDoc <- prettyM_ t
        return $
          "allowed vars:" <+> PP.pretty (runNoNames$ B.toList vs) $$
          "term:" //> tDoc
  in 
  debugBracket DL.PruneTerm msg $ f vs t

instance Prune t a => Prune t (Elim a) where
  {-# INLINE prune #-}
  prune vs (Apply t') = Apply <$> prune vs t'
  prune _  (Proj p)   = return $ Proj p

instance Prune t a => Prune t (Abs a) where 
  {-# INLINE prune #-}
  prune vs (Abs name body) = Abs name <$> prune (addVar name vs) body

instance Prune m a => Prune m [a] where
  {-# INLINE prune #-}
  prune vs = mapM (prune vs)

genericPruneTerm
    :: (IsTerm t, Prune t t)
    => VarSet                -- ^ allowed vars
    -> Term t
    -> TC t r s (Term t)
genericPruneTerm vs t = do
  tView <- viewW t
  case tView of
    Lam body ->
      lam =<< prune vs body
    Pi domain codomain ->
      join $ pi <$> prune vs domain <*> prune vs codomain
    Equal type_ x y -> do
      join $ equal <$> prune vs type_ <*> prune vs x <*> prune vs y
    App (Meta mv) elims -> do
      -- First try to curry and expand
      mvT <- meta mv elims
      mvTView <- viewW =<< etaExpandMeta =<< curryMeta mvT
      case mvTView of
        App (Meta mv') elims' -> do
          mbMvT' <- pruneMeta vs mv' elims'
          case mbMvT' of
            Nothing   -> return mvT
            Just mvT' -> eliminate mvT' elims'
        _ -> do
          prune vs mvT
    App h elims -> return t
      -- headIsNeutral h >>= \case
      -- True  -> app h =<< prune vs elims
      -- False -> return t
    Set ->
      return set
    Refl ->
      return refl
    Con dataCon args ->
      con dataCon =<< prune vs args

type MetaArgs t = [Maybe (Var, Forest Projection)]

-- | @prune vs α es@ tries to prune all the variables in @es@ that are
--   not in @vs@, by instantiating @α@.  If we managed to prune
--   anything returns 'Just', 'Nothing' if we can't prune or no prune
--   is needed.
pruneMeta
    :: forall t r s.
       (IsTerm t)
    => VarSet           -- ^ allowed vars
    -> Meta
    -> [Elim (Term t)]       -- ^ Arguments to the metavariable
    -> TC t r s (Maybe (Closed (Term t)))
pruneMeta allowedVs oldMv elims = do
  
    let msg = runNamesT C0$ do
          mvTypeDoc <- prettyM =<< getMetaType oldMv
          elimsDoc <- prettyM elims
          return $
            "metavar type:" //> mvTypeDoc $$
            "metavar:" <+> PP.pretty oldMv $$
            "elims:" //> elimsDoc $$
            "allowed vars:" //> PP.pretty (runNoNames$ B.toList allowedVs)
    debugBracket DL.PruneMeta msg $ runMaybeT $ do
      args <- MaybeT $ return $ mapM isApply elims
      kills0 <- MaybeT $ sequence <$> mapM (shouldKill allowedVs) args
      lift $ debug_ "to kill" $ PP.pretty kills0
      guard (or kills0)
      oldMvType <- lift $ getMetaType oldMv
      (newMvType, kills1) <- lift $ createNewMetaFromKills oldMvType kills0
      lift $ debug_ "new kills" $ PP.pretty (map unNamed kills1)
      guard (any unNamed kills1)
      newMv <- lift $ addMeta newMvType
      mi <- lift $ killArgs newMv kills1
      lift $ instantiateMeta oldMv mi
      lift $ metaBodyToTerm mi

-- | We build a pi-type with the non-killed types in.  This way, we
--   can analyze the dependency between arguments and avoid killing
--   things that later arguments depend on.
--
--   At the end of the type we put both the new metavariable and the
--   remaining type, so that this dependency check will be performed
--  on it as well.
createNewMetaFromKills
  :: IsTerm t => Type t -> [Bool] -> TC t r s (Type t, [Named Bool])
createNewMetaFromKills type_ [] =
  return (type_, [])
createNewMetaFromKills type_ (kill : kills) = do
  typeView <- whnfView type_
  case typeView of
    Pi domain (Abs name codomain) -> do
      (type', kills') <- createNewMetaFromKills codomain kills
      debug "createNewMetaFromKills" $ do
        domDoc <- prettyM_ domain
        typeDoc <- prettyM_ type'
        return $
          "kill:" <+> PP.pretty kill $$
          "type:" //> domDoc $$
          "strengthening:" //> typeDoc
      let notKilled = do
            type'' <- pi domain (Abs name type')
            return (type'', named name False : kills')
      if not kill
        then notKilled
        else do
          -- By using `maybeNfElseWhnfNf` we cover the case where the
          -- metavariable reduces to a simple lambda, even if full
          -- normalization is disabled.
          mbType <- flip safeStrengthen (boundVar name) =<< maybeNfElseExpandMetas type'
          case mbType of
            Just type'' -> do return (type'', named name True : kills')
            Nothing     -> do debug_ "couldn't strengthen" ""
                              notKilled
    _ ->
      fatalError "impossible.createNewMeta: metavar type too short"


-- | Returns whether the term should be killed, given a set of allowed
--   variables.

--     killed means removed from the argument telescope of a metavariable
--   Returning `Nothing` means that this argument blocks the pruning altogether
--   See p. 58
shouldKill
  :: forall t r s. (IsTerm t)
  => VarSet -> Term t -> TC t r s (Maybe Bool)
shouldKill vs t = runMaybeT $ do
  whnfMeta t >>= \case
    MetaBlockingHead _mv _ ->
      
      mzero

    MetaNotBlocked t' -> do
      let {- checkSpine ts = lift $ do
            
            
            fvs <- runFreeVars t
            return $ not (fvRigid fvs `B.isSubsetOf` vs) -}

          -- Variables of unit type are problematic
          giveUpForNow = return False
          
          -- that the variable is not of Unit type.

          stopAllPruning = mzero
          don'tPruneThisArg = return False


      view t' >>= \case
        Lam _ -> stopAllPruning  -- See https://github.com/agda/agda/issues/1153
        Con dataCon args -> do
          guard =<< lift (isRecordConstr dataCon)
          -- See https://github.com/agda/agda/issues/458
          and <$> mapM (MaybeT . shouldKill vs) args
        -- See agda issue
        App (Var v) _    -> return$ not$ v `B.member` vs
        App (Twin _ v) _ -> return$ not$ v `B.member` vs
        App (Def f) _es -> do -- Either Def, J or 
          getDefinition f >>= \case
            Constant _ Function{}  -> stopAllPruning {- might reduce -}
              
            Constant _ Data{}      -> giveUpForNow
            Constant _ Record{}    -> giveUpForNow
            Constant _ Postulate{} -> don'tPruneThisArg {- same as variables -}
            _                      -> __IMPOSSIBLE__
        App J _ -> stopAllPruning {- see constant function -} 
        App Meta{} _ -> __IMPOSSIBLE__ -- Already checked by whnfMeta
        Pi{}    -> giveUpForNow
        Equal{} -> giveUpForNow
        Refl -> don'tPruneThisArg
        Set  -> don'tPruneThisArg 

-- Tools useful for expanding of contexts.
------------------------------------------------------------------------

{-
-- | Checks whether an eliminator is a a projected variables (because
--   we can expand those).
--
--   Returns the variable and the projection name.
isProjectedVar :: (IsTerm t) => Elim t -> MaybeT (TC t r s) (Var, Opened QName t)
isProjectedVar elim = do
  Apply t <- return elim
  App (Var v) vElims <- lift $ whnfView t
  Proj p : _ <- lift $ return vElims
  return (v, first pName p)
-}

-- | @etaExpandContextVar v Γ@.  Pre:
--
-- * @v@ is in scope in @Γ@
--
-- * If @Γ₁; v : A; Γ₂@, either @A = D t1 ⋯ tn@, where @D@ is a record
--   constructor, or @A@ is blocked.
--
-- Returns the context with @v@ η-expanded if @A@ isn't blocked, the
-- blocking metas if it is.
etaExpandContextVar
  :: (IsTerm t)
  => Ctx t -> Var
  -> TC t r s (Either Guard (Tel t, Subst t))
etaExpandContextVar ctx v = do
  let msg = do
        ctxDoc <- prettyM_ ctx
        return $
          "ctx:" //> ctxDoc $$
          "var:" //> PP.pretty v
  debugBracket DL.EtaExpandContextVar msg $ do
    let (ctx1, vType, tel2) = splitContext ctx v
    blocked <- isBlocked <$> whnf vType
    case blocked of
      Just mvs -> do
        return $ Left mvs
      Nothing -> do
        (tel2', acts) <- etaExpandVar vType tel2
        return $ Right (ctx1 `telAppend` tel2', acts)

-- | Expands a record-typed variable ranging over the given 'Tel',
-- returning a new telescope ranging over all the fields of the record
-- type and the old telescope with the variable substituted with a
-- constructed record, and a substitution for the old variable.
etaExpandVar
  :: forall t r s. (IsTerm t)
  => Type t
  -- ^ The type of the variable we're expanding.
  -> Tel t
  -> TC t r s (Tel t, Subst t)
etaExpandVar type_ tel = do
  App (Def tyCon) tyConPars0 <- whnfView type_
  Constant _ (Record dataCon projs) <- getDefinition tyCon
  DataCon _ _ dataConType <- getDefinition dataCon
  let Just tyConPars = mapM isApply tyConPars0
  appliedDataConType <- openContextual dataConType tyConPars
  (dataConPars0, _) <- assert_ ("etaExpandVar, unrollPiWithNames:" <+>) $
    unrollPiWithNames appliedDataConType (map (qNameName . getQName . pName . opndKey) projs)
  let dataConPars = telToCtx dataConPars0
  dataConT <- con dataCon =<< mapM var (ctxVars dataConPars)
  
  -- specially like in metavar expansion?
  sub <- subInstantiate dataConT $ subWeaken (ctxLength dataConPars) subId
  tel' <- applySubst (coerce tel :: Tel (OpenTerm t)) sub
  let telLen = telLength tel'
  return (dataConPars `telAppend` coerce tel', subLift telLen sub)

-- | Divides a context at the given variable.
splitContext
  :: Ctx a -> Var -> (Ctx a, Type a, Tel a)
splitContext ctx00 v0 =
  go ctx00 (varIndex v0) T0
  where
    go ctx0 ix0 tel = case (ctx0, ix0) of
      (C0, _) ->
        __IMPOSSIBLE__
      (ctx :< (n', type_), ix) ->
        if ix > 0
        then go ctx (ix - 1) ((n', type_) :> tel)
        else (ctx, type_, tel)

type ProjectedVar t = (Var, [Projection])

-- | Codifies what is acceptable as an argument of a metavariable, if we
-- want to invert such metavariable.
data MetaArg t v
  = MVAVar v               -- This vars might be projected before
                           -- expanding the context.
  | MVARecord              --
      (Opened TyConName t) -- Type constructor name
      [MetaArg t v]        -- Arguments to the datacon
  deriving (Functor, Foldable, Traversable)

type MetaArg' t = MetaArg t (ProjectedVar t)

instance PrettyM t a => PrettyM t (MetaArg t a) where
  prettyM (MVAVar v) = do
    vDoc <- prettyM v
    return $ "MVAVar" <+> vDoc
  prettyM (MVARecord tyCon mvArgs) = do
    mvArgsDoc <- prettyM mvArgs
    tyConDoc <- prettyM tyCon
    return $ "MVARecord" <+> tyConDoc //> mvArgsDoc

-- | if @checkMetaElims els ==> args@, @length els == length args@.
checkMetaElims
  :: (IsTerm t) => [Elim (Term t)]
  -> TC t r s (Validation (Collect_ Guard) [MetaArg' t])
checkMetaElims elims = do
  case mapM isApply elims of
    Nothing   -> return $ Failure $ CFail ()
    Just args -> sequenceA <$> mapM checkMetaArg args

checkMetaArg
  :: (IsTerm t) => Term t -> TC t r s (Validation (Collect_ Guard) (MetaArg' t))
checkMetaArg arg = do
  blockedArg <- whnf arg
  let fallback = return $ Failure $ CFail ()
  case blockedArg of
    NotBlocked t -> do
      tView <- whnfView =<< etaContract t
      case tView of
        App (Var v) vArgs -> do
          case mapM isProj vArgs of
            Just ps -> return $ pure $ MVAVar (v, ps)
            Nothing -> fallback
        Con dataCon recArgs -> do
          DataCon tyCon _ _ <- getDefinition dataCon
          tyConDef <- getDefinition tyCon
          case tyConDef of
            Constant _ (Record _ _) -> do
              recArgs'  <- sequenceA <$> mapM checkMetaArg recArgs
              return $ MVARecord tyCon <$> recArgs'
            _ -> do
              fallback
        _ -> do
          fallback
    BlockingHeadMeta mv _ -> do
      return $ Failure $ CCollect $ metaGuard mv
    BlockingHeadDef (Opened key _) _ -> do
      return $ Failure $ CCollect $ qNameGuard key
    BlockedOn mvs _ _ -> do
      return $ Failure $ CCollect mvs

etaContract :: MonadTerm t m => Term t -> m (Term t)
etaContract t0 = fmap (fromMaybe t0) $ etaContractMaybe t0

-- Metavar inversion
------------------------------------------------------------------------

-- | Wraps the given term 'n' times.
lambdaAbstract :: (IsTerm t) => Natural -> Term t -> TC t r s (Term t)
lambdaAbstract 0 t = return t
lambdaAbstract n t = (lam_ <=< lambdaAbstract (n - 1)) t

data InvertMeta t = InvertMeta
  { imvSubst :: [(Var, Term t)]
    -- ^ A substitution from variables in equated term to variables by
    -- the metavariable to terms in the context abstracted by the
    -- metavariable.
  , imvAbstractions :: Natural
    -- ^ How many variables the metas abstracts.
  }

instance PrettyM  t (InvertMeta t) where
  prettyM (InvertMeta ts vs) = do
    ts' <- forM ts $ \(v, t) -> do
      tDoc <- prettyM t
      return $ PP.pretty (v, tDoc)
    return $ PP.list ts' $$ PP.pretty vs

invertMetaVars :: InvertMeta t -> [Var]
invertMetaVars (InvertMeta sub _) = map fst sub

invertMeta
  :: (IsTerm t)
  => Ctx t -> [Elim (Term t)]
  -> TC t r s (Either (Collect_ Guard) (Ctx t, Subst t, InvertMeta t))
invertMeta ctx elims = do
  let msg = runNamesT ctx$ do
        ctxDoc <- prettyM ctx
        elimsDoc <- prettyM =<< traverse (traverse whnfTerm) elims
        return $
          "ctx:" //> ctxDoc $$
          "elims:" //> elimsDoc
  debugBracket DL.InvertMeta msg $ runExceptT $ do
    mvArgs <- ExceptT $ fmap validationToEither $ checkMetaElims elims
    (ctx', mvArgs', acts) <- lift $ removeProjections ctx mvArgs
    lift $ whenDebug $ unless (subNull acts) $ do
      debug "removeProjections" $ runNamesT ctx'$ do
        ctx'Doc <- prettyM ctx'
        mvArgs'Doc <- prettyM mvArgs'
        return $
          "new ctx:" //> ctx'Doc $$
          "args:" //> mvArgs'Doc
    mbInv <- lift $ checkPatternCondition mvArgs'
    case mbInv of
      Nothing  -> do
        throwE $ CFail ()
      Just inv -> do
        lift $ debug "inverted" $ runNamesT ctx'$ do
          ctx'Doc <- prettyM ctx'
          actsDoc <- prettyM acts
          invDoc <- prettyM inv
          return $
            "ctx:" //> ctx'Doc $$
            "acts:" //> actsDoc $$
            "inversion:" //> invDoc
        return (ctx', acts, inv)

mvaApplyActions
  :: (MonadTerm t m) => Subst t -> MetaArg' t -> m (MetaArg' t)
mvaApplyActions acts (MVAVar (v, ps)) = do
  vt <- var v
  vt' <- applySubst vt acts
  vt'' <- eliminate vt' (map Proj ps)
  makeMetaArg vt''

mvaApplyActions acts (MVARecord n args) = do
  MVARecord n <$> mapM (mvaApplyActions acts) args

makeMetaArg :: (MonadTerm t m) => Term t -> m (MetaArg' t)
makeMetaArg vt = do
  vtt <- whnfView vt
  let crash = fatalError <$> do
          vttDoc <- prettyM_ vtt
          fatalError$ PP.render$
                  "Cannot make" //> vttDoc $$
              "into a meta argument"
  case vtt of
    App (Var v') elims -> do
      let Just ps' = mapM isProj elims
      pure$ MVAVar (v', ps')
    Con c xs -> do
      tyCon <- tyConFromCon c
      isRecordType tyCon >>= \case
        True  -> MVARecord tyCon <$> mapM makeMetaArg xs
        False -> crash
    _ -> crash

metaArgToTerm :: MonadTerm t m => (MetaArg t Var) -> m (Term t)
metaArgToTerm (MVAVar v) = var v 
metaArgToTerm (MVARecord tyCon as) = do
  Just c <- recordConFromTyCon tyCon
  con c =<< mapM metaArgToTerm as 

varApplyActions
  :: (IsTerm t) => Subst t -> Var -> TC t r s (MetaArg t Var)
varApplyActions acts v = do
  tView <- whnfView =<< ((`applySubst` acts) =<< var v)
  case tView of
    App (Var v') [] -> do
      return $ MVAVar v'
    Con c args -> do
      Success mvArgs <- sequenceA <$> mapM checkMetaArg args
      let mvArgs' = map (fmap (\(x, []) -> x)) mvArgs
      tyCon <- tyConFromCon c
      return $ MVARecord tyCon mvArgs'
    _ -> do
      fatalError "impossible.varApplyActions"

removeProjections
  :: forall t r s.
     (IsTerm t)
  => Ctx t -> [MetaArg' t]
  -> TC t r s (Ctx t, [MetaArg t Var], Subst t)
removeProjections ctx0 mvArgs0 = do
    let msg = runNamesT ctx0$ do
          ctxDoc <- prettyM ctx0
          mvArgsDoc <- prettyM mvArgs0
          return $
            "ctx:" //> ctxDoc $$
            "args:" //> mvArgsDoc
    debugBracket DL.RemoveProjections msg $ go ctx0 mvArgs0
  where
    go :: Ctx t -> [MetaArg' t]
       -> TC t r s (Ctx t, [MetaArg t Var], Subst t)
    go ctx [] = do
      return (ctx, [], subId)
    go ctx (MVAVar (v, []) : mvArgs) = do
      (ctx', mvArgs', tActs) <- go ctx mvArgs
      mvArg <- varApplyActions tActs v
      return (ctx', mvArg : mvArgs', tActs)
    go ctx1 (MVAVar (v, (p : ps)) : mvArgs) = do
      Right (ctx2, tActs) <- etaExpandContextVar ctx1 v
      t <- (`eliminate` [Proj p]) =<< var v
      App (Var v') [] <- whnfView =<< applySubst t tActs
      mvArgs' <- mapM (mvaApplyActions tActs) mvArgs
      (ctx3, mvArgs'', tActs') <- go (telToCtx ctx2) (MVAVar (v', ps) : mvArgs')
      tActs'' <- subCompose tActs' tActs
      return (ctx3, mvArgs'', tActs'')
    go ctx1 (MVARecord tyCon mvArgs1 : mvArgs2) = do
      (ctx2, mvArgs1', tActs1) <- go ctx1 mvArgs1
      (ctx3, mvArgs2', tActs2) <- go ctx2 mvArgs2
      tActs3 <- subCompose tActs2 tActs1
      return (ctx3, MVARecord tyCon mvArgs1' : mvArgs2', tActs3)

-- | Returns an inversion if the pattern condition is respected for the
-- given 'MetaArg's.
checkPatternCondition
  :: forall t r s. (IsTerm t)
  => [MetaArg t Var] -> TC t r s (Maybe (InvertMeta t))
checkPatternCondition mvArgs = do
  let allVs = concatMap toList mvArgs
  let linear = length allVs == fromIntegral (Set.size (Set.fromList allVs))
  if linear
    then do
      vs <- mapM var $ reverse [mkVar "_" ix | (ix, _) <- zip [0..] mvArgs]
      subs <- projectRecords $ zip mvArgs vs
      return $ Just $ InvertMeta subs (length vs)
    else do
      return $ Nothing
  where
    projectRecords xs = concat <$> mapM (uncurry projectRecord) xs

    projectRecord :: MetaArg t Var -> Term t -> TC t r s [(Var, Term t)]
    projectRecord (MVAVar v) t = do
      return [(v, t)]
    projectRecord (MVARecord tyCon mvArgs') t = do
      Constant _ (Record _ fields) <- getDefinition tyCon
      mvArgs'' <- forM (zip mvArgs' fields) $ \(mvArg, Opened proj _) ->
        (mvArg, ) <$> eliminate t [Proj proj]
      projectRecords mvArgs''

-- | Takes a meta inversion and applies it to a term.  Fails returning
--   a 'Var' if that 'Var' couldn't be substituted in the term -- in
--   other word if the term contains variables not present in the
--   substitution.
applyInvertMeta
  :: forall α t r s.
     (IsTerm t)
  => Ctx α -> InvertMeta t -> Term t
  -> TC t r s (Validation (Collect Var MetaSet) (MetaBody t))
applyInvertMeta ctx (InvertMeta sub vsNum) t = do
  let fallback = fmap (MetaBody vsNum) <$> applyInvertMetaSubst sub t
  let dontTouch = return $ Success $ MetaBody vsNum t
  -- Optimization: if the substitution is the identity, and if the free
  -- variables in the term are a subset of the variables that the
  -- substitution covers, don't touch the term.
  isId <- isIdentity sub
  if isId
    then do
      let vs = B.fromList (map fst sub)
      if B.size vs == Prelude.length (ctxVars ctx)
        then dontTouch
        else do
          fvs <- freeVars t
          if fvAll fvs `B.isSubsetOf` vs
            then dontTouch
            else fallback
    else fallback
  where
    isIdentity :: [(Var, Term t)] -> TC t r s Bool
    isIdentity [] = do
      return True
    isIdentity ((v, u) : sub') = do
      tView <- whnfView u
      case tView of
        App (Var v') [] | v == v' -> isIdentity sub'
        _                         -> return False

applyInvertMetaSubst
  :: forall t r s.
     (IsTerm t)
  => [(Var, Term t)]
  -- ^ Inversion from variables outside to terms inside
  -> Term t
  -- ^ Term outside
  -> TC t r s (Validation (Collect Var MetaSet) (Term t))
  -- ^ Either we fail with a variable that isn't present in the
  -- substitution, or we return a new term.
applyInvertMetaSubst sub t0 =
  let msg = do
        subDoc <- prettyM_ sub
        t0Doc   <- prettyM_ t0
        return $
          "sub:" //> subDoc $$
          "t:"   //> t0Doc
  in
  debugBracket DL.ApplyInvertMetaSubst msg $ flip go t0 $ \v -> return $ maybe (Left v) Right (lookup v sub)
  where
    lift' :: (Var -> TC t r s (Either Var (Term t)))
          -> (Var -> TC t r s (Either Var (Term t)))
    lift' f v0 = case strengthenVar_ 1 v0 of
      Nothing ->
        Right <$> var v0
      Just v -> do
        e <- f v
        case e of
          Left v' -> return $ Left v'
          Right t -> Right <$> weaken_ 1 t

    goAbs invert (Abs name body) = fmap (Abs name) <$> go (lift' invert) body

    go :: (Var -> TC t r s (Either Var (Term t))) -> Term t
       -> TC t r s (Validation (Collect Var MetaSet) t)
    go invert t = do
      viewW t >>= \case
        Lam body -> do
          traverse lam =<< goAbs invert body
        Pi dom cod -> do
          dom' <- go invert dom
          cod' <- goAbs invert cod
          sequenceA $ pi <$> dom' <*> cod'
        Equal type_ x y -> do
          type' <- go invert type_
          x' <- go invert x
          y' <- go invert y
          sequenceA $ equal <$> type' <*> x' <*> y'
        Refl ->
          return $ pure refl
        Con dataCon args -> do
          args' <- mapM (go invert) args
          sequenceA $ con dataCon <$> sequenceA args'
        Set ->
          return $ pure set
        App h elims -> do
          let goElim (Apply t') = fmap Apply <$> go invert t'
              goElim (Proj p)   = return $ pure $ Proj p
          resElims <- sequenceA <$> mapM goElim elims
          let fallback = sequenceA $ app h <$> resElims
          let checkBlocking bl = case resElims of
                Failure (CCollect mvs) ->
                  return $ Failure $ CCollect $ I.insert bl mvs
                Failure (CFail _) ->
                  return $ Failure $ CCollect $ I.singleton bl
                _ ->
                  fallback
          case h of
            Meta mv -> do
              checkBlocking mv
            Var v -> do
              inv <- invert v
              sequenceA $ eliminate <$> either (Failure . CFail) pure inv <*> resElims
            Twin{} -> $(placeholderNoWarning "Unexpected twin variable when inverting meta")
            Def _ -> do
              fallback
            J -> do
              fallback

-- Various
------------------------------------------------------------------------

-- | @killArgs α kills@ instantiates @α@ so that it discards the
--   arguments indicated by @kills@.
killArgs :: (IsTerm t) => Meta -> [Named Bool] -> TC t r s (MetaBody t)
killArgs newMv kills = do
  let vs = reverse [ mkVar n ix
                   | (ix, Named n kill) <- zip [0..] (reverse kills), not kill
                   ]
  body <- meta newMv . map Apply =<< mapM var vs
  return $ MetaBody (length kills) body

-- | If @t = α ts@ and @α : Δ -> D us@ where @D@ is some record type, it
-- will instantiate @α@ accordingly.
etaExpandMeta :: forall t r s. (IsTerm t) => Term t -> TC t r s (Term t)
etaExpandMeta t = do
  debugBracket DL.EtaExpandMeta (prettyM_ t) $ debugResult "etaExpandMeta:" $ etaExpandMetaCached t

{-# NOINLINE etaExpandMetaCached #-}
etaExpandMetaCached :: (IsTerm t) => Term t -> TC t r s (Term t)
etaExpandMetaCached t =
  let fallback = do
        debug_ "didn't expand meta" ""
        return t
  in
  do
    r <- runMaybeT$ do
        App (Meta mv) elims <- lift $ viewW t
        mvType <- lift $ getMetaType mv
        Just (mvb', mvT') <- lift$ (memoize EtaExpandMetaCache $ \mvType ->
          do
            inspect$ runMaybeT $ do
              (telMvArgs, endType) <- lift $ unrollPi mvType
              App (Def tyCon) tyConArgs0 <- lift $ whnfView endType
              lift$ taintDefinition $ getQName $ opndKey tyCon
              Constant _ (Record dataCon _) <- lift $ getDefinition tyCon
              lift $ do
                DataCon _ _ dataConType <- getDefinition dataCon
                let Just tyConArgs = mapM isApply tyConArgs0
                appliedDataConType <- openContextual dataConType tyConArgs
                (dataConArgsTel, _) <- unrollPi appliedDataConType
                dataConArgs <- createMvsPars (telToCtx telMvArgs) dataConArgsTel
                mvT <- con dataCon dataConArgs
                let mvb = MetaBody (telLength telMvArgs) mvT
                (mvb,) <$> metaBodyToTerm mvb) =<< maybeNf mvType

        lift$ instantiateMeta mv mvb'
        lift$ eliminate mvT' elims
    case r of
      Just t' -> return t'
      Nothing -> fallback

-- | Invariant: etaExpansion preserves normal forms
etaExpand :: forall t r s. (IsTerm t) => Type t -> Term t -> TC t r s (Term t)
etaExpand type_ t = do
  
  -- t <- etaExpandMeta t0
  let msg = do
        typeDoc <- prettyM_ type_
        tDoc <- prettyM_ t
        return $
          "type:" //> typeDoc $$
          "term:" //> tDoc
  debugBracket DL.EtaExpand msg $ debugResult "expanded" $ etaExpandCached (t :∈ type_)

-- | @etaExpand A t@ η-expands term @t@.
etaExpandCached :: forall t r s. (IsTerm t) => (Type t :∋ Term t) -> TC t r s (Term t)
etaExpandCached = (memoize EtaExpandCache $ \(type_ :∋ t) -> inspect$ do
    let fallback = do
          debug_ "didn't expand" ""
          return t
    typeView <- whnfView type_
    scrub$ case typeView of
      App (Def tyCon) _ -> do
        tyConDef <- getDefinition tyCon
        case tyConDef of
          Constant _ (Record dataCon projs) -> do
            tView <- viewW t
            case tView of
              -- Optimization: if it's already of the right shape, do nothing
              Con _ _ -> do
                fallback
              _ -> do
                ts <- sequence [eliminate t [Proj p] | Opened p _ <- projs]
                con dataCon ts
          _ -> do
            fallback
      Pi _ cod -> do
        name <- getAbsName_ cod
        v <- var $ boundVar name
        tView <- viewW t
        -- Expand only if it's not a λ-function
        case tView of
          Lam _ -> do
            fallback
          _ -> do
            t' <- weaken_ 1 t
            lam . Abs name =<< eliminate t' [Apply v]
      _ -> do
        fallback)

-- | @intersectVars us vs@ checks whether all relevant elements in @us@
--   and @vs@ are variables, and if yes, returns a prune list which says
--   @True@ for arguments which are different and can be pruned.
intersectVars :: (IsTerm t) => [Elim t] -> [Elim t] -> TC t r s (Maybe [Bool])
intersectVars els1 els2 = runMaybeT $ mapM (uncurry areVars) $ zip els1 els2
  where
    areVars (Apply t1) (Apply t2) = do
      t1View <- lift $ whnfView t1
      t2View <- lift $ whnfView t2
      case (t1View, t2View) of
        (App (isHeadVar -> Just v1) [], App (isHeadVar -> Just v2) []) ->
          return $ (v1 /= v2) -- prune different vars
        (_,               _)               ->
          -- If any of the arguments are not variables, abort!
          -- Consider the case      ?A true x y ~ ?A false y x
          -- None of  the constructors agree, but   ?A  admits the solution
          --   ?A := \b x y = if b then x else y
          mzero
    areVars _ _ =
      mzero

intersectMetaSpine :: (IsTerm t) => Ctx α -> Meta -> [Elim t] -> [Elim t] -> TC t r s (Maybe Guard)
intersectMetaSpine ctx mv els1 els2 = do
  let msg = runNamesT ctx$ do
        els1Doc <- prettyM els1
        els2Doc <- prettyM els2
        return $
          "metavar:" <+> PP.pretty mv $$
          "elims 1:" //> els1Doc $$
          "elims 2:" //> els2Doc
  debugBracket DL.IntersectMetaSpine msg $ do
      mbKills <- intersectVars els1 els2
      debug_ "kills:" $ PP.pretty mbKills
      case mbKills of
        Nothing ->
          
          pure$ Just$ metaGuard mv
        Just kills -> do
          mvType <- getMetaType mv
          (mvType', kills') <- createNewMetaFromKills mvType kills
          if any unNamed kills' then do
            debug_ "new kills:" $ PP.pretty kills'
            newMv <- addMeta mvType'
            instantiateMeta mv =<< killArgs newMv kills'
            return Nothing
          else
            pure$ Just$ metaGuard mv

{-
-- | @instantiateDataCon α c@ makes it so that @α := c β₁ ⋯ βₙ@, where
--   @c@ is a data constructor.
--
--   Pre: @α : Δ → D t₁ ⋯ tₙ@, where @D@ is the fully applied type
--   constructor for @c@.
instantiateDataCon
  :: (IsTerm t)
  => Meta
  -> Opened Name t
  -- ^ Name of the datacon
  -> TC t r s (Closed (Term t))
instantiateDataCon mv dataCon = do
  mvType <- getMetaType mv
  (telMvArgs, endType') <- unrollPi mvType
  DataCon tyCon _ dataConType <- getDefinition dataCon
  -- We know that the metavariable must have the right type (we have
  -- typechecked the arguments already).
  App (Def tyCon') tyConArgs0 <- whnfView endType'
  Just tyConArgs <- return $ mapM isApply tyConArgs0
  True <- synEq tyCon tyCon'
  appliedDataConType <- openContextual dataConType tyConArgs
  (dataConArgsTel, _) <- unrollPi appliedDataConType
  dataConArgs <- createMvsPars (telToCtx telMvArgs) dataConArgsTel
  mvT <- con dataCon dataConArgs
  let mi = MetaBody (telLength telMvArgs) mvT
  -- given the usage, here we know that the body is going to be well typed.
  
  instantiateMeta mv mi
  metaBodyToTerm mi
-}

-- | @createMvsPars Γ Δ@ unrolls @Δ@ and creates a metavariable for
--   each of the elements.
createMvsPars
  :: forall t r s. (IsTerm t) => Ctx t -> Tel (Type t) -> TC t r s [Term t]
createMvsPars ctx0 tel0 = go ctx0 tel0
  where
    go _ T0 =
      return []
    go ctx ((_, type') :> tel) = do
      mv  <- snd <$> addMetaInCtx ctx type'
      mvs <- go ctx . coerce =<< instantiate (coerce tel :: Tel (OpenTerm t)) [mv]
      return (mv : mvs)

-- | Applies a projection to a term, and returns the new term and the
--   new type.
applyProjection
  :: (IsTerm t)
  => Projection
  -> Term t
  -- ^ Head
  -> Opened TyConName t
  -- ^ Type constructor
  -> [Elim (Term t)]
  -- ^ Arguments of the type constructor
  -> TC t r s (Term t, Type t)
applyProjection proj h tyCon' tyConArgs0 = (,)
                  <$> eliminate h [Proj proj]
                  <*> applyProjectionType proj h tyCon' tyConArgs0

headType
  :: (IsTerm t)
  => Ctx t -> Head t -> TC t r s (Type t)
headType = inferHeadType {- ctx h = case h of
  Var v   -> ctxGetVar v ctx
  Def f   -> definitionType =<< getDefinition f
  Meta mv -> getMetaType mv
  J       -> return typeOfJ-}
{-
headType_ :: (IsTerm t) => Ctx_ t -> Head t -> TC t r s (Type t)
headType_ = inferHead_
-}

isRecordConstr :: (IsTerm t) => Opened ConName t -> TC t r s Bool
isRecordConstr dataCon = do
  def' <- getDefinition dataCon
  case def' of
    DataCon tyCon _ _ -> isRecordType tyCon
    _                 -> return False

{-# SPECIALIZE tyConFromCon :: (IsTerm t) => Opened ConName t -> TC t r s (Opened TyConName t) #-}
tyConFromCon :: (IsTerm t, MonadTerm t m) => Opened ConName t -> m (Opened TyConName t)
tyConFromCon dataCon = do
  DataCon tyCon _ _ <- getDefinition dataCon
  return tyCon

recordConFromTyCon :: (IsTerm t, MonadTerm t m) => Opened TyConName t -> m (Maybe (Opened RConName t))
recordConFromTyCon = getDefinition >&> \case
  Constant _ (Record con _) -> Just con
  _ -> Nothing

isRecordType :: (IsTerm t, MonadTerm t m) => Opened TyConName t -> m Bool
isRecordType = recordConFromTyCon >&> \case
  Just{} -> True
  Nothing -> False

occursCheckFailed :: IsTerm t => Meta -> MetaBody t -> TC t r s α
occursCheckFailed mv mvb = checkError$ OccursCheckFailed mv mvb


-- Also, if the resulting Guard is Bottom, we should just say 'occursCheckFailed'.
safeInstantiateMeta_ :: (IsTerm t) => Meta -> MetaBody t -> TC t r s (Either (GuardLattice, MetaBody t) ())
safeInstantiateMeta_ mv mvb = 
  checkMetaOccurs mv mvb >>= \case
    (DoesNotOccur, mvb') -> Right <$> instantiateMeta mv mvb'
    (Rigidly, mvb')      ->
      -- We do not want to fail, in case that the occurrence
      -- turns out to be bogus
      pure$ Left (inj$ metaGuard mv, mvb')
      --occursCheckFailed mv mvb'
    (Flexibly bs, mvb')  -> pure$ Left (bs, mvb')

safeInstantiateMeta :: (IsTerm t) => Meta -> MetaBody t -> TC t r s ()
safeInstantiateMeta mv mvb = safeInstantiateMeta_ mv mvb >>= \case
  Left (_, mvb') -> occursCheckFailed mv mvb' 
  Right ()  -> return ()

--------------------
-- Twin Variables --
--------------------

class KillTwins t a where
  {-# MINIMAL killTwins | killTwinsE #-}
  killTwins :: a -> WriterT TwinVarSet (TC t r s) a
  killTwins a = lift (killTwinsE mempty a) >>= writer 

  killTwinsE :: (KillTwins t a) => TwinVarSet -> a -> TC t r s (a, TwinVarSet) 
  killTwinsE tvm a = second (tvm <>) <$> runWriterT (killTwins a)

data TwinVarSet = TwinVarSet {
   _twinSetFst :: !VarSet 
 , _twinSetSnd :: !VarSet
}

instance Monoid TwinVarSet where                  
  mempty = TwinVarSet mempty mempty

instance Semigroup TwinVarSet where
  (TwinVarSet a b) <> (TwinVarSet a' b') =
    TwinVarSet (a <> a') (b <> b')

twinSet :: Dir -> Lens' TwinVarSet VarSet
twinSet Fst f x = fmap (\_twinSetFst -> x{_twinSetFst}) (f $ _twinSetFst x)
twinSet Snd f x = fmap (\_twinSetSnd -> x{_twinSetSnd}) (f $ _twinSetSnd x)

tvInsert :: Var -> Dir -> TwinVarSet -> TwinVarSet                  
tvInsert v dir = twinSet dir %~ B.insert v

tvSingleton :: Var -> Dir -> TwinVarSet
tvSingleton v dir = mempty & twinSet dir .~ B.singleton v

tvMember :: (Var, Dir) -> TwinVarSet -> Bool
tvMember (v,dir) = B.member v . (^. twinSet dir)  

strengthenTwinVars_ :: Natural -> TwinVarSet -> TwinVarSet 
strengthenTwinVars_ n = (twinSet Fst %~ strengthenVars_ n) . (twinSet Snd %~ strengthenVars_ n)

-- | Removes twin variables from a term, replacing them with their non-twin counterparts.
--   Also records which twin variables appeared in the term so that their
--   types in the context can be unified.
genericKillTwinsTerm :: forall t m r s. (m ~ TC t r s, IsTerm t, KillTwins t t) => t -> WriterT TwinVarSet m t
genericKillTwinsTerm = go
  where
  go :: t -> WriterT TwinVarSet m t
  go t =
    view t >>= (\case
        App (Twin dir v) es -> do
            tell$ tvSingleton v dir
            app (Var v) <$> killTwins es
        Pi t a -> pi <$> killTwins t <*> killTwins a
        Lam t -> lam <$> killTwins t
        -- Passthrough
        App h es -> app <$> killTwins h <*> killTwins es
        Equal t t1 t2 -> equal <$> killTwins t <*> killTwins t1 <*> killTwins t2
        Refl -> pure (pure refl)
        Set -> pure (pure set)
        Con o ts -> con o <$> killTwins ts) >>= id


instance KillTwins t a => KillTwins t (Abs a) where  
  killTwins = traverse (st1 . killTwins)
    where st1 = censor (strengthenTwinVars_ 1)

instance (KillTwins t a, KillTwins t b) => KillTwins t (a,b) where
  killTwins (a,b) = (,) <$> killTwins a <*> killTwins b

instance (KillTwins t a, KillTwins t b, KillTwins t c) => KillTwins t (a,b,c) where
  killTwins (a,b,c) = (,,) <$> killTwins a <*> killTwins b <*> killTwins c

instance (KillTwins t a, KillTwins t b) => KillTwins t (a :∈ b) where
  killTwins (a :∈ b) = (:∈) <$> killTwins a <*> killTwins b

instance KillTwins t Meta where
  killTwins mv = pure mv


-- These are all specializations of `Traversable f => KillTwins f a`
-- We choose not to make a general version so that we have control over where
-- the instance gets applied.
instance (KillTwins t a) => KillTwins t [a] where killTwins x = traverse killTwins x
instance (KillTwins t a) => KillTwins t (Elim a) where killTwins x = traverse killTwins x
instance (KillTwins t a) => KillTwins t (Head a) where killTwins x = traverse killTwins x

fastKillTwinsE :: (HasSubterms t a, PrettyM t a, IsTerm t) =>
             TwinVarSet -> a -> TC t r s (a, TwinVarSet)
fastKillTwinsE tvm a = do
  a' <- maybeNfElseWhnf a
  res <- runExceptT (runWriterT (runReaderT (go a') 0))
  case res of
    Right (x, Endo vars) -> return (x, vars tvm)
    Left v -> checkError$ BoundTwinVariable v a
  where
  go :: forall t m a. (HasSubterms t a, MonadTerm t m) => a -> ReaderT Natural (WriterT (Endo TwinVarSet) (ExceptT Var m)) a
  go a = traverseSubterms a $ \t ->
    view t >>= (\case
        App (Twin dir v) es -> do
            n <- ask
            v' <- strengthenOrFail n v
            tell$ Endo$ tvInsert v' dir
            app (Var v) <$> go es

        App h es -> app <$> go h <*> go es
        -- Passthrough
        Pi t a -> pi <$> go t <*> local (+1) (go a)
        Lam t -> lam <$> local (+1) (go t)
        Equal t t1 t2 -> equal <$> go t <*> go t1 <*> go t2
        Refl -> pure (pure refl)
        Set -> pure (pure set)
        Con o ts -> con o <$> go ts) >>= id

  strengthenOrFail :: (MonadError Var m) => Natural -> Var -> m Var
  strengthenOrFail n v =
     case strengthenVar_ n v of
       Just v  -> return v
       Nothing -> throwError v

{-
safeStrengthen :: (IsTerm t, MonadTerm t m, ApplySubst t a) => Abs a -> m (Maybe a)
safeStrengthen (Abs_ t) = do
  nameOrT <- runSafeApplySubst $ genericSafeApplySubst t $ subStrengthen 1 subId
  case nameOrT of
    Left _   -> return Nothing
    Right t' -> return $ Just t'
-}


-- | @instantiateDataCon α c@ makes it so that @α := c β₁ ⋯ βₙ@, where
--   @c@ is a data constructor.
--
--   Pre: @α : Δ → D t₁ ⋯ tₙ@, where @D@ is the fully applied type
--   constructor for @c@.
--
instantiateDataCon
  :: (IsTerm t)
  => Meta
  -> ConName
  -- ^ Name of the datacon
  -> TC t r s (Closed (Term t))
instantiateDataCon mv dataCon = do
  let openedDataCon = Opened dataCon []
  mvType <- getMetaType mv
  (telMvArgs, endType') <- unrollPi mvType
  DataCon tyCon _ dataConType <- getDefinition openedDataCon
  -- We know that the metavariable must have the right type (we have
  -- typechecked the arguments already).
  App (Def (OTyCon tyCon')) tyConArgs0 <- whnfView endType'
  Just tyConArgs <- return $ mapM isApply tyConArgs0
  True <- synEq tyCon tyCon'
  appliedDataConType <- openContextual dataConType tyConArgs
  (dataConArgsTel, _) <- unrollPi appliedDataConType
  dataConArgs <- createMvsPars (telToCtx telMvArgs) dataConArgsTel
  mvT <- con openedDataCon dataConArgs
  let mi = MetaBody (telLength telMvArgs) mvT
  -- given the usage, here we know that the body is going to be well typed.
  
  instantiateMeta mv mi
  metaBodyToTerm mi

-- | η-contracts a term (both records and lambdas).
etaContractMaybe :: forall m t. MonadTerm t m => Term t -> m (Maybe (Term t))
etaContractMaybe t0 =
  debugBracket DL.EtaContract (pure mempty) $ runMaybeT $ go t0
  where
    go :: Term t -> MaybeT m t
    go t0 = do
      t0View <- viewW t0
      case t0View of
        Lam (Abs_ body) -> do
          App h elims@(_:_) <- viewW =<< etaContract body
          Apply t <- return $ last elims
          -- We might have something like (λ x. f (pair (fst x) (snd x)))
          App (Var v) [] <- lift $ viewW =<< etaContract t
          guard $ varIndex v == 0
          Just t' <- lift $ flip safeStrengthen (boundVar "_") =<< app h (init elims)
          return t'
        Con dataCon args -> do
          DataCon tyCon _ _ <- lift $ getDefinition dataCon
          Constant _ (Record _ fields) <- lift $ getDefinition tyCon
          guard $ length args == length fields
          (t : ts) <- sequence (zipWith isRightProjection (map opndKey fields) args)
          guard =<< (and <$> lift (mapM (synEq t) ts))
          return t
        _ ->
          mzero
      where
        isRightProjection p t = do
          App h elims@(_ : _) <- viewW =<< etaContract t
          Proj p' <- return $ last elims
          guard $ p == p'
          app h (init elims)

applyProjectionType
  :: (MonadTerm t m)
  => Projection
  -> Term t
  -- ^ Head
  -> Opened TyConName t
  -- ^ Type constructor
  -> [Elim (Term t)]
  -- ^ Arguments of the type constructor
  -> m (Type t)
applyProjectionType proj h tyCon' tyConArgs0 = do
  let openedProjName = first (const (pName proj)) tyCon'
  Projection _ tyCon projType <- getDefinition openedProjName
--  h' <- eliminate h [Proj proj]
--  App (Def tyCon') tyConArgs0 <- whnfView type_
  True <- synEq tyCon tyCon'
  let Just tyConArgs = mapM isApply tyConArgs0
  appliedProjType <- openContextual projType tyConArgs
  Pi _ endType <- whnfView appliedProjType
  endType' <- instantiate_ endType h
  return endType'


-- | Checks whether two terms convert in a given context
--   A simple converter, even with η for the unit type.
genericNfEq :: forall t m. MonadTerm t m => Ctx t -> ((Term t, Term t) :∈ Type t) -> m (Either (PP.Doc, Ctx t, (Term t, Term t) :∈ Type t) ())
genericNfEq ctx ((t1,t2) :∈ ty) = do
  -- We need to fully normalize so that η-contraction will work properly at all levels
  ctx' <- nf ctx; t1' <- nf t1; t2' <- nf t2; ty' <- nf ty
  synEq t1' t2' >>= \case
    True  -> return$ Right ()
    False -> runExceptT$ go ctx' ((t1',t2') :∈ ty')
  where
  go :: Ctx t -> ((Term t, Term t) :∈ Type t) -> ExceptT (PP.Doc, Ctx t, (Term t, Term t) :∈ Type t) m ()
  go ctx ((t1,t2) :∈ ty) = do
    -- note that, once normalized, getting the WHNF is constant time
    -- also, types do not need to get eta contracted on the head,
    -- because elements of `Set` can neither be `Lam` headed nor `Con` headed.
    tView1 <- etaExpandDefHeaded =<< whnfView t1
    tView2 <- etaExpandDefHeaded =<< whnfView t2
    tyView <- whnfView ty

    -- Fallbacks in case of failed η-contraction
    let errorFallback msg = throwE (msg, ctx, (t1,t2) :∈ ty)

    let goHead (Def o1) (Def o2) = goOpened o1 o2
        goHead h1       h2       = synEq h1 h2

        
        goOpened :: forall t m qname. MonadTerm t m => IsQName qname => Opened qname t -> Opened qname t -> m _
        goOpened (Opened k1 args1) (Opened k2 args2) =
          and <$> sequence
              [pure $ k1 == k2
              ,pure $ length args1 == length args2
              ,and <$> sequence [do
                  a1' <- etaContract a1                                    
                  a2' <- etaContract a2
                  synEq a1' a2' | (a1,a2) <- zip args1 args2 ]
              ]

    let etaFallback1 = etaExpandMaybe (t2 :∈ ty) >>= \case
          Just t2' -> go ctx ((t1,t2') :∈ ty) 
          Nothing  -> errorFallback "can't contract lhs"

    let etaFallback2 = etaExpandMaybe (t1 :∈ ty) >>= \case
          Just t1' -> go ctx ((t1',t2) :∈ ty) 
          Nothing  -> errorFallback "can't contract rhs"

    let goSpine (_   :∈ _) [] [] = return ()
        goSpine (mbH :∈ ty) (e@(Apply x):es1) (Apply y:es2) = do
          whnfView ty >>= \case
            Pi dom cod -> do
              go ctx $ (x,y) :∈ dom
              cod'  <- instantiate_ cod x
              mbH'  <- forM mbH (flip eliminate [e])
              goSpine (mbH' :∈ cod') es1 es2 
            _ -> errorFallback "head of wrong type"
        goSpine _ (Apply{}:_) _ = __IMPOSSIBLE__

        goSpine (mbH :∈ ty) (e@(Proj  p):es1) (Proj  q:es2) = do
          let Just h = mbH
          whnfView ty >>= \case
            (App (Def (OTyCon tyCon)) args) -> do
              flip unless (errorFallback "mismatching projections") =<< synEq p q
              ty' <- applyProjectionType p h tyCon args
              h'  <- eliminate h [e]
              goSpine (Just h' :∈ ty') es1 es2
            _ -> errorFallback "head of wrong type"
        goSpine _ (Proj{}:_) _ = __IMPOSSIBLE__

    let isUnitRecord (App (Def tyCon) _) =
          getDefinition tyCon >>= \case
            Constant _ (Record _ []) -> return True
            _ -> return False
        isUnitRecord _ = return False

    isUnitRecord tyView >>= \case
    -- η-equality for the unit type
      True -> return ()
      False ->
        case (tView1, tView2, tyView) of
          (Lam (Abs name1 body1), Lam (Abs name2 body2), Pi dom (Abs_ cod)) ->
            go (ctx :< (name1 <> name2, dom)) ((body1, body2) :∈ cod) 

          (Pi domain1 (Abs name1 codomain1), Pi domain2 (Abs name2 codomain2), Set) -> do
            go ctx ((domain1, domain2) :∈ set)
            go (ctx :< (name1 <> name2, domain1)) ((codomain1, codomain2) :∈ set)

          (Equal type1 x1 y1, Equal type2 x2 y2, Set) -> do
            go ctx ((type1, type2) :∈ set)
            go ctx ((x1, x2) :∈ type1)
            go ctx ((y1, y2) :∈ type1)

          (Set, Set, Set) ->
            return ()

          (Con dataCon1 args1, Con dataCon2 args2, App _ tyConPars) -> do
            goOpened dataCon1 dataCon2 >>= flip unless (errorFallback "mismatched constructor")

            -- Copied verbatim from the unifier
            let Just tyConPars' = mapM isApply tyConPars
            DataCon _ _ dataConType <- getDefinition dataCon1
            appliedDataConType <- openContextual dataConType tyConPars'
            goSpine (Nothing :∈ appliedDataConType) (map Apply args1) (map Apply args2)
 
          (Refl, Refl, Equal ty x y) -> do
            go ctx ((x,y) :∈ ty)
            return ()

          -- Spines are tricky, as they may be of type unit in the end
          -- so, we need to capture the exception, and then see if
          -- the spine becomes of type unit at any point during the
          -- unification.
          --
          -- A theory of partial η-equality would be nice (e.g. have it only
          -- for instantiating metas, but not for terms in general…
          -- But that is essentially impossible, as it breaks transitivity
          -- of equality.
          (App h1 els1, App h2 els2, _) -> do
            goHead h1 h2 >>= flip unless (errorFallback "mismatched heads")
            ty <- inferHeadType ctx h1
            h1' <- app h1 []
            goSpine (Just h1' :∈ ty) els1 els2

          -- Cases that we might be able to solve with η.
          -- We want to η-contract the proper side
          -- Note that records with no fields cannot be η-contracted.

          -- Note that the result of η-contraction can never be Lam or a Con;
          -- it will always be an App
          (Lam{}, _, Pi{}) -> etaFallback1
          (_, Lam{}, Pi{}) -> etaFallback2
          (Con{}, _, App{}) -> etaFallback1
          (_, Con{}, App{}) -> etaFallback2

          -- Also, try η expansion for unit!
          -- Insight: A value of unit cannot be eliminated, so we do not need
          -- to check each of the intermediate values of an application
          -- it is enough to check the type of the whole β-normal term.
          (_, _, _) -> errorFallback "terms not equal" 


-- | n f ↦ λ x₁ x₂ … xₙ . f x₁ x₂ … xₙ
etaExpandLambdaN :: forall t m. MonadTerm t m => Nat -> TermView t -> m (TermView t)
etaExpandLambdaN n _ | n < 0 = __IMPOSSIBLE__
etaExpandLambdaN 0 t         = return t
etaExpandLambdaN (natToInt -> n) tView = do
  -- We need n to be an integer for
  wt  <- weaken_ (fromIntegral n) =<< unview tView
  -- Downwards enumeration for Natural does not work properly
  es' <- sequence [Apply <$> var (mkVar "_" (fromIntegral i)) | i <- reverse [0..n-1]] 
  go n =<< eliminate wt es'
  where
    go :: Int -> Term t -> m (TermView t)
    go 1 t' = pure$ Lam (Abs_ t')
    go n t' = go (n-1) =<< lam_ t' 

-- | @etaExpandDefHeaded A t@ makes sure that a term is not headed by a definition
--   that could reduce through η-expansion.
etaExpandDefHeaded :: forall t m. MonadTerm t m => TermView t -> m (TermView t)
etaExpandDefHeaded tView = do
  let fallback = return tView
  case tView of
    (App (Def (OFDef f)) es) -> do
      getMaxClauseArity f >>= \case
        Just maxArity -> do
          let esLen = length es
          if maxArity > esLen then
            etaExpandLambdaN (maxArity - esLen) tView
          else
            fallback
        _ -> fallback
    _ -> fallback


-- | @etaExpand A t@ η-expands term @t@.
etaExpandMaybe :: (MonadTerm t m) => (Term t :∋ Term t) -> m (Maybe (Term t))
etaExpandMaybe (ty :∋ t) = do
    let fallback = return Nothing
    whnfView ty >>= \case
      App (Def tyCon) _ -> do
        tyConDef <- getDefinition tyCon
        case tyConDef of
          Constant _ (Record dataCon projs) -> do
            viewW t >>= \case
              -- Optimization: if it's already of the right shape, do nothing
              Con _ _ -> return Nothing
              tView -> do
                t  <- unview tView
                ts <- sequence [eliminate t [Proj p] | Opened p _ <- projs]
                Just <$> con dataCon ts
          _ -> do
            fallback
      Pi _ cod -> do
        name <- getAbsName_ cod
        v <- var $ boundVar name
        -- Expand only if it's not a λ-function
        viewW t >>= \case
          Lam _ -> return Nothing
          tView -> do
            t' <- weaken_ 1 =<< unview tView
            Just <$> (lam . Abs name =<< eliminate t' [Apply v])
      _ -> return Nothing

-- | Meta instantiation without occurs check
--   Only appropiate when the MetaBody has been newly constructed,
--   involving only freshly-created metas.
unsafeInstantiateMeta :: IsTerm t => Meta -> MetaBody t -> _ ()
unsafeInstantiateMeta = instantiateMeta


