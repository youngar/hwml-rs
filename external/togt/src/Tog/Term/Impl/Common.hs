{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoImplicitPrelude #-}
-- | This module exports both building blocks for building custom
--   term implementations, and ready-made default implementations
--   based on these blocks.
module Tog.Term.Impl.Common
  ( genericSafeApplySubst
  , genericApplySubst
  , genericSafeStrengthen
  , genericSafeApplySubstIdOpt
  , genericSafeApplySubstReduce
  , genericWhnf
  , genericWhnfMeta
  , genericWhnfView
  , genericTypeOfJ
  , genericNf
  , genericExpandMetas
  , genericSynEq
  , genericSynEqWhnf
  , genericSynEqView
  , genericPrettyPrecM
  , genericFreeVars, fastFreeVars
  , genericMetaOccurs
  , genericMetaOccursWhnf
  , view
  , unview
  , eliminateMetaBody
  , IsTermE(..)
  , ViewFun(..)
  ) where

import           Data.Traversable                 (mapM, sequence)
import           Data.Collect

import           Tog.Instrumentation
import           Tog.Prelude                      hiding (foldr, mapM, sequence)
import           Tog.Names
import           Tog.Names.Sorts
import           Tog.Monad (TC)
import qualified Tog.Abstract                     as SA
import qualified Tog.PrettyPrint                  as PP
import           Tog.Term.Synonyms
import           Tog.Term.Types
import qualified Tog.Term.Subst                   as Sub
import           Tog.Term.FreeVars (genericFreeVars, fastFreeVars)
import           Tog.Term.MetaVars


-- For debugging  
import qualified Tog.Instrumentation.Debug.Label as DL
import           Tog.PrettyPrint                  ((//>), ($$))

#include "impossible.h"

genericSafeApplySubst
  :: (MonadTerm t m) => t -> Subst t -> ApplySubstM m t
genericSafeApplySubst =
  genericSafeApplySubstIdOpt $
  genericSafeApplySubstReduce $
  genericSafeApplySubstCore

genericSafeApplySubstIdOpt, genericSafeApplySubstReduce
  :: (MonadTerm t m) => (t -> Subst t -> ApplySubstM m t) ->
                        (t -> Subst t -> ApplySubstM m t) 

-- | Avoid applying identity substitutions
genericSafeApplySubstIdOpt _  t Sub.Id = return t
genericSafeApplySubstIdOpt go t rho    = go t rho

-- | Retries failed strenghtenings on the WHNF of the term.
--   We do not want normalization to affect the success of
--   type-checking.
--
--   Failures are very expensive; successes are cheap.
--   Ofc, memoization will make failures cheap also, as the
--   WHNF will not change.
genericSafeApplySubstReduce go t rho = do
  reduce <- confWhnfApplySubst <$> readConf
  if reduce then
    whnfTerm t >>= flip go rho
  else
    -- If the substitution fails (because of an strengthening),
    -- we are compelled to try again on the weak-head normal form of the term
    catchE (go t rho) (\_ -> whnfTerm t >>= flip go rho)

  -- - With `view', GR is as fast as S with `whnfView', but S is impossibly slow;
  -- - With `whnfView', GR is almost twice as slow as S.

genericSafeApplySubstCore
  :: forall t m. (MonadTerm t m) => t -> Subst t -> ApplySubstM m t
genericSafeApplySubstCore t rho = do
  view t >>= go
  where
    go tView =
      case tView of
        Lam body ->
          lift . lam =<< traverse (flip safeApplySubst $ subLift 1 rho) body
        Pi dom cod -> do
          dom' <- safeApplySubst dom rho
          cod' <- traverse (flip safeApplySubst $ subLift 1 rho) cod
          lift $ pi dom' cod'
        Equal type_ x y  -> do
          type' <- safeApplySubst type_ rho
          x' <- safeApplySubst x rho
          y' <- safeApplySubst y rho
          lift $ equal type' x' y'
        Refl ->
          return refl
        Con dataCon args -> do
          args' <- safeApplySubst (coerce args :: [OpenTerm t]) rho
          lift $ con dataCon (coerce args')
        Set ->
          return set
        App h els  -> do
          els' <- safeApplySubst els rho
          case h of
            Var v -> do u <- subLookup v rho
                        lift $ eliminate u els'
            Twin dir v  -> do u <- subLookupTwin dir v rho
                              lift$ eliminate u els'
            Def n   -> do n' <- safeApplySubst (coerce n :: Opened DefName (OpenTerm t)) rho
                          lift $ def (coerce n' :: Opened DefName t) els'
            Meta mv -> lift $ meta mv els'
            J       -> lift $ app J els'

genericWhnf
  :: (MonadTerm t m) => t -> m (Blocked t)
genericWhnf t = do
  tView <- view t
  let fallback = return $ NotBlocked t
  case tView of
    App (Def opnd@(Opened dkey _)) es -> do
      sig <- askSignature
      -- Note that here we don't want to crash if the definition is not
      -- set, since I want to be able to test non-typechecked terms.
      case sigLookupDefinition sig dkey of
        Just (Contextual tel (Constant _ (Function inst))) -> do
          eliminateInst (telLength tel) (first Right opnd) inst es
        _ -> do
          fallback
    App (Meta mv) es -> do
      sig <- askSignature
      case sigLookupMetaBody sig mv of
       Nothing -> do
         return $ BlockingHeadMeta mv es
       Just mvb -> whnf =<< eliminateMetaBody mv mvb es
    App J es0@(_ : x : _ : _ : Apply p : Apply refl' : es) -> do
      refl'' <- whnf refl'
      case refl'' of
        BlockingHeadMeta bl _ ->
          -- return $ BlockedOn (HS.singleton bl) BlockedOnJ es0
          return $ BlockedOn (metaGuard bl) BlockedOnJ es0
        BlockingHeadDef (Opened key _) _ ->
          return $ BlockedOn (qNameGuard key) BlockedOnJ es0
        BlockedOn mvs _ _ ->
          return $ BlockedOn mvs BlockedOnJ es0
        NotBlocked refl''' -> do
          reflView <- view refl'''
          case reflView of
            Refl -> whnf =<< eliminate p (x : es)
            _    -> fallback
    _ ->
      fallback

genericWhnfMeta
  :: (MonadTerm t m) => t -> m (MetaBlocked t)
genericWhnfMeta t = do
  tView <- view t
  let fallback = return $ MetaNotBlocked t
  case tView of
    App (Meta mv) es -> do
      sig <- askSignature
      case sigLookupMetaBody sig mv of
       Nothing -> do
         return $ MetaBlockingHead mv es
       Just mvb -> whnfMeta =<< eliminateMetaBody mv mvb es
    {-
    -- We also normalize J, because it is a) relatively frequent, and b) involves no computation.
    App J (_ : x : _ : _ : Apply p : Apply refl' : es) -> do
      viewW refl' >>= \case
        Refl -> whnfMeta =<< eliminate p (x : es)
        _ -> fallback
    -}
    _ ->
      fallback


-- | For convenience, here we have turned already meta-variables bodies
-- into dummy contextual clauses.
eliminateInst
  :: (MonadTerm t m)
  => Natural
  -- ^ Length of the context the 'FunInst' resides in.
  -> Opened (Either Meta DefName) t -> FunInst t -> [Elim t]
  -> m (Blocked t)
eliminateInst _ (Opened (Left mv) args) Open es = do
  return $ BlockingHeadMeta mv (map Apply args ++ es)
eliminateInst _ (Opened (Right f) args) Open es = do
  return $ BlockingHeadDef (Opened f args) es
eliminateInst argsNum opnd@(Opened _ args) (Inst inv) es | clauses <- ignoreInvertible inv = do
  -- Optimization: if the arguments are all lined up, don't touch
  -- the body.
  --
  -- This is a special case, we know that all meta-variable bodies and
  -- where clauses will be stored in this form, and we want to
  -- optimize for that.  If some functions fall under this pattern
  -- too, it doesn't matter.

  -- The number of arguments must be the same as the length of the
  -- context telescope.
  _assert@True <- return $ length args == argsNum
  simple <- isSimple (argsNum - 1) args
  clauses' <- if simple
    then return clauses
    else instantiate clauses args
  eliminateClauses opnd clauses' es
  where
    isSimple _ [] = do
      return True
    isSimple n' (arg : args') = do
      argView <- view arg
      case argView of
        App (Var v) [] | varIndex v == n' -> isSimple (n'-1) args'
        _                                 -> return False

eliminateMetaBody :: MonadTerm t m => Meta -> MetaBody t -> Elims t -> m (Term t)
eliminateMetaBody mv mvb@(MetaBody argsNum mvT) es = do
  -- Try to treat the meta var body as a clause
  if length es >= argsNum
    then do
      -- Note that we know that the first 'argsNum' elims, if
      -- present, must be applications, since we know that the
      -- body has at least 'argsNum' arguments.
      let (l, es')  = strictSplitAt argsNum es
      let Just args = mapM isApply l
      ignoreBlocking =<< eliminateInst argsNum (Opened (Left mv) args)
        (Inst (NotInvertible [Clause [] (ClauseBody mvT)])) es'
    else do
      mvT' <- metaBodyToTerm mvb
      eliminate mvT' es


eliminateClauses
  :: (MonadTerm t m)
  => Opened (Either Meta DefName) t -> [Clause t] -> [Elim t] -> m (Blocked t)
-- Again, metas only ever have one clause.  Note that all these are just
-- assertions, things would work just fine without them, but let's
-- program defensively.
eliminateClauses (Opened (Left _) _) [Clause [] (ClauseBody t)] es = do
  whnf =<< eliminate t es
eliminateClauses (Opened (Left _) _) _ _  = do
  __IMPOSSIBLE__
eliminateClauses (Opened (Right f) args) clauses es = do
  let opnd = Opened f args
  mbT <- whnfFun opnd es clauses
  case mbT of
    Nothing -> NotBlocked <$> def opnd es
    Just t  -> return t

whnfFun
  :: (MonadTerm t m)
  => Opened DefName t -> [Elim t] -> [Clause t]
  -> m (Maybe (Blocked t))
whnfFun _ _ [] = do
  return Nothing
whnfFun fun es (Clause _ ClauseNoBody : clauses) =
  whnfFun fun es clauses
whnfFun fun es (Clause patterns (ClauseBody body) : clauses) = runMaybeT $ do
  matched <- lift $ matchClause es patterns
  case matched of
    Failure (CCollect mvs) ->
      return $ BlockedOn mvs (BlockedOnFunction fun) es
    Failure (CFail ()) ->
      MaybeT $ whnfFun fun es clauses
    Success (args, leftoverEs) -> lift $ do
      body' <- instantiateClauseBody body args
      whnf =<< eliminate body' leftoverEs

matchClause
  :: (MonadTerm t m)
  => [Elim t] -> [Pattern t]
  -> m (Validation (Collect_ Guard) ([t], [Elim t]))
matchClause es [] =
  return $ pure ([], es)
matchClause (Apply arg : es) (VarP : patterns) = do
  matched <- matchClause es patterns
  return $ (\(args, leftoverEs) -> (arg : args, leftoverEs)) <$> matched
matchClause (Apply arg : es) (ConP dataCon dataConPatterns : patterns) = do
  blockedArg <- whnf arg
  case blockedArg of
    BlockingHeadMeta bl _ -> do
      matched <- matchClause es patterns
      return $ Failure (CCollect (metaGuard bl)) <*> matched
    BlockingHeadDef (Opened bl _) _ -> do
      matched <- matchClause es patterns
      return $ Failure (CCollect (qNameGuard bl)) <*> matched
    BlockedOn mvs _ _ -> do
      matched <- matchClause es patterns
      return $ Failure (CCollect mvs) <*> matched
    NotBlocked t -> do
      tView <- view t
      let fallback = return $ Failure $ CFail ()
      case tView of
        -- Here we can compare just the key, since the assumption is
        -- that we only reduce well-typed terms.
        Con (ODCon dataCon') dataConArgs | opndKey dataCon == opndKey dataCon' ->
          matchClause (map Apply dataConArgs ++ es) (dataConPatterns ++ patterns)
                                         | otherwise -> fallback
        -- It cannot be a record type, because that would never
        -- match against a data constructor pattern.
        Con ORCon{} _ -> __IMPOSSIBLE__
        _ -> fallback
matchClause _ _ =
  return $ Failure $ CFail ()

genericWhnfView :: (MonadTerm t m) => t -> m (TermView t)
genericWhnfView = genericWhnf >=> ignoreBlocking >=> view

genericNf :: forall t m. (MonadTerm t m) => t -> m t
genericNf t = do
  tView <- whnfView t
  case tView of
    Lam body ->
      lam =<< nf body
    Pi domain codomain ->
      join $ pi <$> nf domain <*> nf codomain
    Equal type_ x y ->
      join $ equal <$> nf type_ <*> nf x <*> nf y
    Refl ->
      return refl
    Con dataCon args ->
      join $ con dataCon <$> mapM nf args
    Set ->
      return set
    App h elims ->
      join $ app h <$> mapM nf elims

genericExpandMetas :: forall t m. (MonadTerm t m) => t -> WriterT Guard m t
genericExpandMetas = viewW >=> \case
    Lam body ->
      lam =<< go body
    Pi domain codomain ->
      join $ pi <$> go domain <*> go codomain
    Equal type_ x y ->
      join $ equal <$> go type_ <*> go x <*> go y
    Refl ->
      return refl
    Con dataCon args ->
      join $ con dataCon <$> go args
    Set -> return set
    App h es -> do
      let fallback guard = do
            tell guard
            app h =<< go es
      case h of
        Def{}   -> fallback mempty
        Var{}   -> fallback mempty
        Meta mv -> fallback (metaGuard mv)
        J       -> fallback mempty
  where
    go :: forall a. ExpandMetas t a => a -> WriterT Guard m a
    go = expandMetas
  

-- (A : Set) ->
-- (x : A) ->
-- (y : A) ->
-- (P : (x : A) -> (y : A) -> (eq : _==_ A x y) -> Set) ->
-- (p : (x : A) -> P x x refl) ->
-- (eq : _==_ A x y) ->
-- P x y eq
genericTypeOfJ :: forall t m. (MonadUnview t m) => m (Closed (Type t))
genericTypeOfJ =
    ("A", r set) -->
    ("x", v "A" 0) -->
    ("y", v "A" 1) -->
    ("P", ("x", v "A" 2) --> ("y", v "A" 3) -->
          ("eq", join (equal <$> v "A" 4 <*> v "x" 1 <*> v "y" 0)) -->
          r set
    ) -->
    ("p", ("x", v "A" 3) --> (app (Var (mkVar "P" 1)) . map Apply =<< sequence [v "x" 0, v "x" 0, r refl])) -->
    ("eq", join (equal <$> v "A" 4 <*> v "x" 3 <*> v "y" 2)) -->
    (app (Var (mkVar "P" 2)) . map Apply =<< sequence [v "x" 4, v "y" 3, v "eq" 0])
  where
    v n ix = var $ mkVar n ix
    r = return

    infixr 9 -->
    (-->) :: (Name, m t) -> m t -> m t
    (name, type_) --> t = join $ pi <$> type_ <*> (Abs name <$> t)

genericSynEqWhnf, genericSynEq, genericSynEqLazy
  :: (MonadTerm t m)
  => t -> t -> m Bool
genericSynEqWhnf t1 t2 = do
  join $ genericSynEqView <$> whnfView t1 <*> whnfView t2

genericSynEq t1 t2 = do
  join $ genericSynEqView <$> viewW t1 <*> viewW t2

genericSynEqLazy t1 t2 = do
  join $ genericSynEqView <$> view t1 <*> view t2

genericSynEqView
  :: (MonadTerm t m)
  => TermView t -> TermView t -> m Bool
genericSynEqView tView1 tView2 = do
  case (tView1, tView2) of
    (Lam body1, Lam body2) ->
      synEq body1 body2
    (Pi domain1 codomain1, Pi domain2 codomain2) ->
      (&&) <$> synEq domain1 domain2 <*> synEq codomain1 codomain2
    (Equal type1 x1 y1, Equal type2 x2 y2) ->
      (&&) <$> ((&&) <$> synEq type1 type2 <*> synEq x1 x2)
           <*> synEq y1 y2
    (App h1 els1, App h2 els2) ->
      synEq (h1, els1) (h2, els2)
    (Set, Set) ->
      return True
    (Con dataCon1 args1, Con dataCon2 args2) ->
      synEq (dataCon1, args1) (dataCon2, args2)
    (Refl, Refl) ->
      return True
    (_, _) -> do
      return False


instantiateClauseBody
  :: (MonadTerm t m) => Term t -> [Term t] -> m (Term t)
instantiateClauseBody = instantiate

genericPrettyPrecM
  :: (MonadTerm t m, MonadNames m) => Int -> t -> m PP.Doc
genericPrettyPrecM p t = do
    synT <- internalToTerm t
    return $ PP.prettyPrec p synT

internalToTerm
  :: (MonadTerm t m, MonadNames m) => t -> m SA.Expr
internalToTerm t0 = do
  dontNormalize <- confDontNormalizePP <$> readConf
  tView <- view =<< if dontNormalize then evalExpandMetas t0 else nf t0
  case tView of
    Lam (Abs name body) -> do
      SA.Lam (pure name) <$> localAddName name (internalToTerm body)
    Pi dom (Abs name cod) -> do
      mbN <- runSafeApplySubst $ safeApplySubst cod $ subStrengthen 1 subId
      case mbN of
        Left _v -> do
          SA.Pi (pure name) <$> internalToTerm dom <*> localAddName name (internalToTerm cod)
        Right cod' -> do
          SA.Fun <$> internalToTerm dom <*> internalToTerm cod'
    Equal type_ x y ->
      SA.Equal <$> internalToTerm type_ <*> internalToTerm x <*> internalToTerm y
    Refl ->
      return $ SA.Refl noSrcLoc
    Con dataCon args ->
      SA.Con (fmap SA.internalToQName $ opndKey dataCon) <$> mapM internalToTerm (opndArgs dataCon ++ args)
    Set ->
      return $ SA.Set noSrcLoc
    App h args -> do
      hDoc <- prettyM h
      (h', args1) <- case h of
        Var{} ->
          return (SA.Var$ pure$ mkName (PP.render hDoc), [])
        Twin{} ->
          return (SA.Var$ pure$ mkName (PP.render hDoc), [])
        Def (Opened f args') ->
          (SA.Def$ fmap SA.internalToQName f,) <$> mapM (fmap SA.Apply . internalToTerm) args'
        Meta mv ->
          return $ (SA.Var (mkName (PP.render hDoc) :@ (srcLoc mv)), [])
        J ->
          return (SA.J noSrcLoc, [])
      args2 <- forM args $ \arg -> case arg of
        Apply t -> SA.Apply <$> internalToTerm t
        Proj p  -> return $ SA.Proj $ fmap SA.internalToQName$ pName p
      return $ SA.App h' (args1 ++ args2)

{-
genericFoldMetas :: (MonadTerm t m, MonadVisit m, MonoidM u) => Term t -> ReaderT (MetasProgram u) m u
genericFoldMetas t = do

    -- Using `view` here instead of `whnfView` is kosher because we are looking up
    -- the definition in the signature in `foldMetasHead`.
    tView <- viewW t
    case tView of
      Lam body           -> foldMetas body
      Pi domain codomain -> foldMetas (domain, codomain)
      Equal type_ x y    -> foldMetas (type_, x, y)
      App h elims        -> foldMetasHead h `mappendM` foldMetas elims
      Set                -> memptyM
      Refl               -> memptyM
      Con _ elims        -> foldMetas elims

  where

    foldMetasHead (Def (Opened name args)) = do
      (<>) <$>
       (flip sigLookupDefinition name <$> askSignature >>= \case
          -- Perhaps the symbol has not been defined yet
          Nothing   -> memptyM
          Just body -> visitQName name $ foldMetas body)
       <*> foldMetas args

    foldMetasHead (Meta mv)             = yieldMeta mv
      lookupMetaBody mv >>= \case
        Nothing -> yieldMeta mv
        Just body -> visitMeta mv $ foldMetas body

    foldMetasHead (Var _)               = memptyM
    foldMetasHead (Twin _ _)            = memptyM
    foldMetasHead (J)                   = memptyM
-}

data ViewFun = FunView
             | FunViewW
genericMetaOccurs :: forall t m. (MonadTerm t m, MonadVisit m)
  => ViewFun
  -- ^ Normalization function
  -> (forall a. Metas t a => a -> m Any)
  -- ^ Recursive case
  -> Meta
  -- ^ Metavariable
  -> Term t
  -- ^ Term
  -> m Any
genericMetaOccurs funView go mv t = do
    -- Using `view` here instead of `whnfView` is kosher because we are looking up
    -- the definition in the signature in `foldMetasHead`.
    tView <- (case funView of
                FunView  -> view 
                FunViewW -> viewW
                ) t
    case tView of
      Lam body           -> go body
      Pi domain codomain -> go (Term domain, codomain)
      Equal type_ x y    -> go (Term type_, Term x, Term y)
      App h elims        -> goHead h `mappendM` go elims
      Set                -> memptyM
      Refl               -> memptyM
      Con con elims      -> go (con, coerce @_ @[Term₀ t] elims)  {- constructor arguments don't really occur -}
  where
    goHead :: Head t -> m Any
    goHead (Def (Opened name args)) = do
      mappendM
        (flip sigLookupDefinition name <$> askSignature >>= \case
           
           Nothing   -> memptyM
           Just body -> visitQName (getQName name)$  go body)
        (go$ coerce @_ @[Term₀ t] args)

    goHead (Meta mv') | mv == mv' = return$ Any True
                      | otherwise =
                        case funView of
                          FunViewW -> memptyM
                          FunView  -> lookupMetaBody mv >>= \case
                            Nothing    -> memptyM
                            Just body  -> visitMeta mv' $ go body

    goHead (Var _)               = memptyM
    goHead (Twin _ _)            = memptyM
    goHead (J)                   = memptyM

genericMetaOccursWhnf :: forall t m. (MonadTerm t m)
  => (forall a. Metas t a => a -> m (Meet DoesNotOccur))
  -- ^ Recursive case
  -> Meta
  -- ^ Metavariable
  -> Term t
  -- ^ Term
  -> m (Meet DoesNotOccur)
genericMetaOccursWhnf go mv t = do
    -- Using `view` here instead of `whnfView` is kosher because we are looking up
    -- the definition in the signature in `foldMetasHead`.
    t & whnf >>= \case
      NotBlocked t    -> goWhnf =<< view t 
      BlockedOn mvs def es -> fmap (flexibleUnder mvs) <$> go (def, es)
      BlockingHeadDef (Opened name _) es -> fmap (flexibleUnder (qNameGuard name)) <$> go es
      BlockingHeadMeta mv' es | mv == mv' -> pure (pure Rigidly)
                              | otherwise -> fmap (flexibleUnder (metaGuard mv')) <$> go es 
  where
    goWhnf = \case
      Lam body           -> go body
      Pi domain codomain -> go (Term domain, codomain)
      Equal type_ x y    -> go (Term type_, Term x, Term y)
      App h elims        -> goHead h$ go elims
      Set                -> memptyM
      Refl               -> memptyM
      Con con elims      -> go (con, coerce @_ @[Term₀ t] elims)  {- constructor arguments don't really occur -}

    goHead :: Head t -> m (Meet DoesNotOccur) -> m (Meet DoesNotOccur)
    goHead (Def def)                es = go def `mappendM` es
    goHead (Meta _)                 es = es
    goHead (Var _)                  es = es
    goHead (Twin _ _)               es = es
    goHead (J)                      es = es

genericSafeStrengthen :: (IsTerm t, MonadTerm t m, ApplySubst t a) => a -> Var -> m (Maybe a)
genericSafeStrengthen t (unVar -> n) = do
  nameOrT <- runSafeApplySubst $ safeApplySubst t $ subLift n $ subStrengthen 1 subId
  case nameOrT of
    Left _   -> return Nothing
    Right t' -> return $ Just t'

genericApplySubst :: (MonadTerm t m, ApplySubst t a) => a -> Subst t -> m a
genericApplySubst x rho = do
  nameOrRes <- runExceptT $ safeApplySubst x rho
  case nameOrRes of
    Left name -> error $ "applySubst: couldn't strengthen because of " ++ show name
    Right res -> return res


 
-- | Common functionality for terms
class IsTerm t => IsTermE t where
    -- | Whether the meta occurs in the term. This will not normalize the term.
    metaOccurs :: (MonadTerm t m) => Meta -> t -> m Bool
    metaOccurs mv a = fmap getAny$ runVisitMetasT$ let r = genericMetaOccurs FunViewW (runFoldMetas r) mv in r a 

    metaOccursWhnf :: (MonadTerm t m) => Meta -> t -> m DoesNotOccur
    metaOccursWhnf mv a = fmap getMeet$ let r = genericMetaOccursWhnf (runFoldMetas r) mv in r a



