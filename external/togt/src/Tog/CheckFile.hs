{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
-- | Processes a @tog@ file.  This provides the function that will be
-- used by the main program.
--
-- The input is abstract syntax, and the output is the result of elaborating
-- the abstract syntax into internal syntax.
--
-- The solving of the constraints is done concurrently with the generation
-- of the constraints.
module Tog.CheckFile
  ( -- * Program checking
    checkFile
  , checkers
  ) where

import qualified Control.Lens                     as L
import qualified Data.HashSet                     as HS
import           Data.List                        (find)
import           Tog.Instrumentation
import qualified Tog.Instrumentation.Debug.Label as DL
import           Tog.Prelude
import           Tog.Names
import           Tog.Names.Sorts
import qualified Tog.Abstract                     as SA
import           Tog.Abstract                     (pattern (:@@), pattern (:@@@))
import           Tog.Term
import           Tog.Term.Impl
import           Tog.PrettyPrint                  ((<+>), render, (//>), ($$))
import qualified Tog.PrettyPrint                  as PP
import           Tog.Monad
import           Tog.TypeCheck
import           Tog.Elaborate
import           Tog.Unify
import           Tog.Error
import           Tog.Unify.Class (auditState)

import           Control.Monad.Error.Class        (throwError, catchError)                 

#include "impossible.h"
import Development.Placeholders

-- Type checking
------------------------------------------------------------------------

data CheckState t = CheckState
  { _csSolveState     :: !(SolveState t)
  }

L.makeLenses ''CheckState

initCheckState :: (Unify t, MonadConf m, MonadIO m) => m (CheckState t)
initCheckState = CheckState <$> initSolveState

type CheckM t = TC t (Env t) (CheckState t)
type CCheckM t = forall b. CheckM t b -> CheckM t b

-- Decls
------------------------------------------------------------------------

-- | Checks a single declaration in a module file.
-- | Here we don't use continuations because we don't want the debugging
-- output to be nested across declarations.
checkDecl
  :: (Unify t)
  => Env t       -- ^ Definitions and variables in the scope of the definition
  -> SA.Decl
  -> TC t r (CheckState t) (Env t)
checkDecl env decl = do
  let cont = ask
  magnifyTC (const env) $ do
    debugBracket_ DL.CheckDecl (PP.pretty decl) $ atSrcLoc decl $ do
      case decl of
        SA.TypeSig sig      -> checkTypeSig sig cont
        SA.Postulate sig    -> checkPostulate sig cont
        SA.Data sig         -> checkData sig cont
        SA.Record sig       -> checkRecord sig cont
        SA.DataDef (d :@@@ _) xs cs  -> checkDataDef d [x | x :@ _ <- xs] cs cont
        SA.RecDef (d :@@@ _) xs (c :@@@ _) fs -> checkRecDef d [x | x :@ _ <- xs] c fs cont
        SA.FunDef (f :@@@ _) clauses -> checkFunDef f clauses cont
        SA.Module_ module_  -> checkModule module_ cont
        SA.Import (modu :@@ _) args -> checkImport modu args cont
        SA.Open (modu :@@ _)       -> checkOpen modu cont

-- | Checks a sequence of declarations, adding each of them
--   to the environment.
--
--   Note that `checkDecl` can call `checkModule`, which in turn calls `checkDecls`.
checkDecls :: (Unify t) => Env t -> [SA.Decl] -> TC t r (CheckState t) (Env t)
checkDecls env [] = do
  return env
checkDecls env (decl : decls) = do
  !env' <- checkDecl env decl
  checkDecls env' decls

-- | Adds a constant (a module, a type declaration, a postulate …), and adds it
--   to the current enviroment
addConstantAndOpen
  :: (Unify t, IsQName name)
  => (name -> Tel t -> Type t -> CheckM t ()) -- ^ Function that adds the constant
  -> name
  -> Type t
  -> CCheckM t
addConstantAndOpen f name type_ cont = do
  tel <- asks envTel
  f name tel type_
  openDefinitionInEnv_ name $ \_ -> cont

-- | Returns a term u of type A, such that, when the constraints
--   are solved, it will be equal to [e].
checkExpr
  :: (Unify t)
  => SA.Expr
     -- ^ e
  -> Type t
     -- ^ A
  -> CheckM t (Term t)
checkExpr synT type_ = do
  let msg = do
        typeDoc <- prettyMEnv type_
        return $
          "type:" //> typeDoc $$
          "term:" //> PP.pretty synT
  debugBracket DL.CheckExpr msg $ do
    t <- zoomTC csSolveState $ elaborate type_ synT

    -- This checks that the elaborated term has the required type
    -- However, this is unnecessary, as the `elaborate`
    -- algorithm guarantees this.
    nce <- confNoCheckElaborated <$> readConf
    if nce then do
      return t
    else do
      ctx <- asks envCtx
      check ctx t type_
      return t

-- | Checks that the type in a type signature is in set,
--   and adds the type signature to the environment.
checkTypeSig :: (Unify t) => SA.TypeSig 'FDefS -> CCheckM t
checkTypeSig (SA.Sig (name :@@@ _) absType) cont = do
    type_ <- checkExpr absType set
    addConstantAndOpen addTypeSig name type_ cont

-- | Checks that the type in a type postulate is in set,
--   and adds the postulate to the environment.
checkPostulate :: (Unify t) => SA.TypeSig 'PDefS -> CCheckM t
checkPostulate (SA.Sig (name :@@@ _) absType) cont = do
    type_ <- checkExpr absType set
    addConstantAndOpen addPostulate name type_ cont

-- | Checks that the type in a data-type signature is a
--   Pi type with (eventually) set codomain, and adds the data-type
--   signature to the -- environment.
checkData :: (Unify t) => SA.TypeSig 'TyConS -> CCheckM t
checkData (SA.Sig (name :@@@ _) absType) cont = do
    type_ <- checkExpr absType set
    -- Check that at the end of the type there is a 'Set'
    (tel, endType) <- unrollPi type_
    extendEnv (telToCtx tel) $ do
      ctx <- asks envCtx
      definitionallyEqual ctx set endType set
    addConstantAndOpen addData name type_ cont

-- | Checks that the type in a data-type signature is a
--   Pi type with (eventually) set codomain, and adds the data-type
--   signature to the -- environment.
checkRecord :: (Unify t) => SA.TypeSig 'TyConS -> CCheckM t
checkRecord (SA.Sig (name :@@@ _) absType) cont = do
    type_ <- checkExpr absType set
    -- Check that at the end of the type there is a 'Set'
    (tel, endType) <- unrollPi type_
    extendEnv (telToCtx tel) $ do
      ctx <- asks envCtx
      definitionallyEqual ctx set endType set
    -- We add it as a postulate first, because we don't know what the
    -- datacon is yet.
    addConstantAndOpen addTypeSig name type_ cont

checkDataDef
    :: forall t. (Unify t)
    => TyConName
    -- ^ Name of the tycon.
    -> [Name]
    -- ^ Names of parameters to the tycon.
    -> [SA.TypeSig 'DConS]
    -- ^ Types for the data constructors.
    -> CCheckM t
checkDataDef tyCon0 tyConParsNames dataCons cont = do
  -- The type constructor must already be defined, and opened
  (tyCon, _) <- getOpenedDefinition tyCon0
  tyConType <- definitionType =<< getDefinition tyCon
  (tyConPars, _) <- unrollPiWithNames tyConType tyConParsNames
  -- We check the data constructor types under the type parameters of
  -- the type constructor
  dataConsTypes <- extendEnv (telToCtx tyConPars) $ do
    -- We need to weaken the opened tyCon name
    tyCon' <- applySubst (coerce tyCon :: Opened TyConName (OpenTerm t)) $ subWeaken (telLength tyConPars) subId
    appliedTyConType <- telApp (def (coerce tyCon' :: Opened TyConName t) []) tyConPars
    mapM (checkDataCon appliedTyConType) dataCons
  -- Now we repeatedly add the data constructors.
  let go [] cont' = do
        cont'
      go ((dataCon, dataConArgs, dataConType) : dataConsTypes') cont' = do
        addDataCon dataCon tyCon dataConArgs $ Contextual tyConPars dataConType
        openDefinitionInEnv_ dataCon $ \_ -> go dataConsTypes' cont'
  go dataConsTypes cont

checkDataCon
    :: (Unify t)
    => Type t
    -- ^ Tycon applied to the parameters.
    -> SA.TypeSig 'DConS
    -- ^ Data constructor type
    -> CheckM t (DConName, Natural, Type t)
    -- ^ Name of the datacon, number of arguments and type of the data
    -- constructor, scoped over the parameters of the data type.
checkDataCon appliedTyConType (SA.Sig (dataCon :@@@ loc) synDataConType) = do
  atSrcLoc loc $ do
    dataConType <- checkExpr synDataConType set
    (vsTel, endType) <- unrollPi dataConType
    -- Check that the data constructor produces an element of the type
    -- it belongs to.
    extendEnv (telToCtx vsTel) $ do
      appliedTyConType' <- weaken_ (telLength vsTel) appliedTyConType
      ctx <- asks envCtx
      definitionallyEqual ctx set appliedTyConType' endType
    return (dataCon, telLength vsTel, dataConType)

-- | Check a record definition

--   We disallow records with less than one field, because they mess up
--   strenghtening because of η-equality (e.g. bad interaction with
--   `curryMeta`.).
--   Otherwise we would need some fancy mechanism to detect whether a
--   variable is a singleton type.
checkRecDef
    :: forall t. (Unify t)
    => TyConName
    -- ^ Name of the tycon.
    -> [Name]
    -- ^ Name of the parameters to the tycon.
    -> RConName
    -- ^ Name of the data constructor.
    -> [SA.TypeSig 'ProjS]
    -- ^ Fields of the record.
    -> CCheckM t
checkRecDef tyCon0 tyConPars dataCon fields cont = do
  -- The tyCon must already be opened (and in the same module)
  (tyCon, _) <- getOpenedDefinition tyCon0
  tyConType <- definitionType =<< getDefinition tyCon
  -- Add the constructor name to the tyCon
  addRecordCon tyCon dataCon
  -- Enter a context with the arguments to the tyCon in scope
  (tyConParsTel, _) <- unrollPiWithNames tyConType tyConPars
  fieldsTel <- extendEnv (telToCtx tyConParsTel) $ checkFields fields
  fieldsTel' <- weaken_ 1 (coerce fieldsTel :: Tel (OpenTerm t))
  tyCon' <- weaken_ (telLength tyConParsTel) (coerce tyCon :: Opened TyConName (OpenTerm t))
  appliedTyConType <- telApp (def (coerce tyCon' :: Opened TyConName t) []) tyConParsTel
  addProjections tyCon tyConParsTel (boundVar "_") [name | (SA.typeSigName -> name :@@@ _) <- fields] (coerce fieldsTel') $ do
    dataConType <- telPi fieldsTel =<< weaken_ (telLength fieldsTel) appliedTyConType
    addRecordConSignature dataCon tyCon (length fields) $ Contextual tyConParsTel dataConType
    openDefinitionInEnv_ dataCon $ \_ -> do
      -- Recheck definitions (the new constructor may have rendered things solvable)
      recheckDefinitions
      cont

-- | Run this when the definitions are changed (e.g. added constructor or record)
recheckDefinitions :: Unify t => CheckM t ()
recheckDefinitions = zoomTC csSolveState $ solveAll []

checkFields
    :: forall t. (Unify t)
    => [SA.TypeSig 'ProjS] -> CheckM t (Tel (Type t))
checkFields = go C0
  where
    go :: Ctx (Type t) -> [SA.TypeSig 'ProjS] -> CheckM t (Tel (Type t))
    go ctx [] =
        return $ ctxToTel ctx
    go ctx (SA.Sig (field :@@@ _) synFieldType : fields) = do
        fieldType <- extendEnv ctx $ checkExpr synFieldType set
        go (ctx :< (qNameName$ getQName field, fieldType)) fields

addProjections
    :: forall t.
       (Unify t)
    => Opened TyConName t
    -- ^ Type constructor.
    -> Tel (Type t)
    -- ^ Arguments to the type constructors
    -> Var
    -- ^ Variable referring to the value of type record type itself,
    -- which is the last argument of each projection ("self").  Note
    -- that this variable will have all the context above in scope.
    -> [ProjName]
    -- ^ Names of the remaining fields.
    -> Tel (Type t)
    -- ^ Telescope holding the types of the next fields, scoped
    -- over the types of the previous fields and the self variable.
    -> CCheckM t
addProjections tyCon tyConPars self fields0 fieldTypes0 cont = do
    appliedTyCon <- telApp (def tyCon []) tyConPars

    let go [] T0 = do
          cont
        go (proj : fields') ((name, fieldType) :> fieldTypes') = do
          endType <- pi appliedTyCon (Abs name fieldType)
          addProjection proj tyCon $ Contextual tyConPars endType
          openDefinitionInEnv_ (pName proj) $ \openedProj -> do
            projected <- app (Var self) [Proj (opndKey$ (first (const proj) openedProj))]
            go fields' . coerce =<< instantiate (coerce fieldTypes' :: Tel (OpenTerm t)) [projected]
        go _ _ = do
          __IMPOSSIBLE__

    go (zipWith Projection' fields0 $ map Field [0,1..]) fieldTypes0

checkFunDef
  :: (Unify t) => FDefName -> [SA.Clause] -> CCheckM t
checkFunDef fun0 synClauses cont = do
    (fun, funDef) <- getOpenedDefinition fun0
    case funDef of
      Constant funType (Function Open) -> do
        clauses <- mapM (checkClause funType) synClauses
        inv <- checkInvertibility clauses
        -- We don't need to extend the environment, because the function
        -- definition is already open
        addClauses fun inv
        -- Instantiating definitions may change solvability of clauses. Recheck.
        recheckDefinitions
        cont
      Constant _ Postulate -> do
        funDoc <- prettyM_ fun
        typeError . ppGenericError $ "Cannot give body to postulate" <+> funDoc
      _ -> do
        __IMPOSSIBLE__

checkClause
  :: (Unify t)
  => Closed (Type t)
  -> SA.Clause
  -> CheckM t (Closed (Clause t))
checkClause funType (SA.Clause synPats synClauseBody) = do
  -- We check the patterns, and start a new block with the context that
  -- the patterns have left us with.
  checkPatterns synPats funType $ \pats clauseType -> startBlock $ do
    let msg = do
          ctxDoc <- prettyM_ =<< asks envCtx
          return $
            "context:" //> ctxDoc $$
            "clause:" //> PP.pretty synClauseBody
    if any hasEmptyPat pats
      then case synClauseBody of
        SA.ClauseNoBody -> return $ Clause pats ClauseNoBody
        _               -> checkError EmptyPatternWithClauseBody
      else case synClauseBody of
        SA.ClauseNoBody ->
          checkError NoClauseBodyWithoutEmptyPattern
        SA.ClauseBody synClauseBody' wheres -> do
          env <- ask
          env' <- checkDecls env wheres
          magnifyTC (const env') $ do
            debugBracket DL.CheckClause msg $ do
              clauseBody <- checkExpr synClauseBody' clauseType
              return $ Clause pats $ ClauseBody clauseBody
  where
    hasEmptyPat EmptyP        = True
    hasEmptyPat (ConP _ pats) = any hasEmptyPat pats
    hasEmptyPat VarP          = False

checkPatterns
  :: (Unify t)
  => [SA.Pattern]
  -> Type t
  -- ^ Type of the clause that has the given 'SA.Pattern's in front.
  -> ([Pattern t] -> Type t -> CheckM t a)
  -- ^ Continuation taking the elaborated patterns, a list of terms
  -- corresponding to terms produced by the patterns, and the type of
  -- the body of the clause.
  -> CheckM t a
checkPatterns [] type_ cont = do
  cont [] type_
checkPatterns (synPat : synPats) type0 cont = do
  typeView <- whnfView type0
  case typeView of
    Pi dom (Abs_ cod0) ->
      checkPattern synPat dom cod0 $ \pat cod ->
      checkPatterns synPats cod $ \pats type_ ->
      cont (pat : pats) type_
    _ -> do
      checkError $ ExpectingPi type0

-- | Failure to prove distinct does not imply that they are equal
proveDistinct
  :: (Unify t)
  => Type t -> Term t -> Term t -> CheckM t Bool
proveDistinct ty tmA tmB = do
  tyView <- whnfView ty
  case tyView of
    App (Def _tyCon) _ -> do
      -- It's a data type! Now check if the head constructors are distinct
      aView <- whnfView tmA
      bView <- whnfView tmB
      case (aView, bView) of
        (Con aCon _argsA, Con bCon _argsB) -> do
          synEq aCon bCon >>= \case
            True -> do
              let _ = $(placeholderNoWarning "Compare arguments recursively")
              return False
            False -> return True
        _ -> return False

checkPattern
  :: (Unify t)
  => SA.Pattern
  -> Type t
  -- ^ Type of the matched thing.
  -> Type t
  -- ^ Type of what's past the matched thing.
  -> (Pattern t -> Term t -> CheckM t a)
  -- ^ The elaborated pattern, the term produced by the pattern.
  -> CheckM t a
checkPattern synPat patType type_ cont = atSrcLoc synPat $ case synPat of
  SA.EmptyP _ -> do
    -- Check that the data type has no constructors
    let fallback = checkError $ EmptyPatternOnBadType patType
    patTypeView <- whnfView patType
    case patTypeView of
      App (Def tyCon) _ -> do
        tyConDef <- getDefinition tyCon
        case tyConDef of
          Constant _ (Data []) -> cont EmptyP type_
          _                    -> fallback
      Equal ty tmA tmB -> do
        proveDistinct ty tmA tmB >>= \case
          True -> cont EmptyP type_
          False -> fallback
      _ -> do
        fallback
  SA.VarP (name :@ _) -> do
    -- The type is already scoped over a single variable, so we're fine.
    extendEnv_ (name, patType) $ cont VarP type_
  SA.WildP _ -> do
    -- Same as above
    extendEnv_ ("_", patType) $ cont VarP type_
  SA.ConP (RConName dataCon :@@@ _) _synPats -> do
    -- We do not allow pattern-matching on record constructors
    sig <- askSignature
    let dataConDef = sigGetDefinition sig dataCon
        DataCon (Const tyCon) _ _ = ignoreContextual dataConDef
    case ignoreContextual (sigGetDefinition sig tyCon) of
      Constant _ Record{} -> checkError $ PatternMatchOnRecord synPat tyCon
      _                   -> __IMPOSSIBLE__
  SA.ConP (DConName dataCon :@@@ _) synPats -> do
    -- Check that the 'dataCon' is a constructor for the 'patType' we
    -- have been given.
    sig <- askSignature
    let dataConDef = sigGetDefinition sig dataCon
        DataCon (Const tyCon) _ _ = ignoreContextual dataConDef
    patTypeView <- whnfView patType
    case patTypeView of
      -- Here we don't care about the argument in 'Opened', because the
      -- match refers to whatever arguments the tyCon has in the type
      -- signature.
      App (Def (OTyCon tyCon')) tyConArgs0 | tyCon == opndKey tyCon' -> do
        let Just tyConArgs = mapM isApply tyConArgs0
        -- Here we use the arguments of the 'tyCon' to open the
        -- definition of the 'dataCon'.
        let openDataCon = Opened dataCon $ opndArgs tyCon'
        DataCon _ _ dataConType <- openDefinition dataConDef (opndArgs tyCon')
        -- We unroll the type of the data constructor, and then we
        -- continue examining the patterns using the type of the data
        -- constructor chained to the rest of the type we were given.
        appliedDataConType <- openContextual dataConType tyConArgs
        (appliedDataConTypeTel, _) <- unrollPi appliedDataConType
        -- Here we form the term made up of the new variables we're
        -- bringing in scope by taking the type of the dataCon...
        t <- con openDataCon =<< mapM var (telVars appliedDataConTypeTel)
        -- ...which we then instantiate in the old type, taking care of
        -- weakening the rest.
        let numDataConArgs = telLength appliedDataConTypeTel
        rho <- subChain (subLift 1 (subWeaken numDataConArgs subId)) =<< subSingleton t
        type' <- telPi appliedDataConTypeTel =<< applySubst type_ rho
        debug "checkPattern" $ runNamesT C0 $ do
         typeDoc <- prettyM type_
         rhoDoc <- prettyM rho
         type'Doc <- prettyM type'
         return $
          "type:" //> typeDoc $$
          "rho:" //> rhoDoc $$
          "type':" //> type'Doc
        -- GO GO GO
        checkPatterns synPats type' $ \pats type'' -> do
          cont (ConP openDataCon pats) type''
      _ -> do
        checkError $ ExpectingTyCon (Just tyCon) patType

checkModule
  :: forall t. (Unify t) => SA.Module -> CCheckM t
checkModule (SA.Module (moduleName :@@ _) pars0 exports decls) cont = do
  let msg =
        "name:" //> PP.pretty moduleName $$
        "pars:" //> PP.pretty pars0 $$
        "exports:" //> PP.pretty exports
  debugBracket_ DL.CheckModule msg $ do
    module_ <- go pars0 C0
    tel <- asks envTel
    addModule moduleName tel module_
    openDefinitionInEnv_ moduleName $ \_ -> cont
  where
    go :: SA.Params -> Ctx t -> CheckM t (Module t)
    go [] ctx = do
      extendEnv ctx $ startBlock $ do
        env <- ask
        void $ checkDecls env decls
      return $ Contextual (ctxToTel ctx) $ HS.fromList [name | name :@@ _ <- exports]
    go ((n :@ _, synType) : pars) ctx = do
      type_ <- extendEnv ctx $ checkExpr synType set
      go pars $ ctx :< (n, type_)

checkImport
  :: forall t. (Unify t) => QName -> [SA.Expr] -> CCheckM t
checkImport moduleName0 synArgs0 cont = do
  (_, Module (Contextual tel0 names0)) <- getOpenedDefinition moduleName0

  let checkArgs T0 [] args = do
        openDefs (reverse args) (HS.toList names0)
      checkArgs ((_, type_) :> tel) (synArg : synArgs) args = do
        arg <- checkExpr synArg type_
        tel' <- instantiate (coerce tel :: Tel (OpenTerm t)) [arg]
        checkArgs (coerce tel') synArgs (arg : args)
      checkArgs _ _ _ = do
        checkError $ MismatchingArgumentsForModule moduleName0 tel0 synArgs0

      openDefs _    []             = cont
      openDefs args (name : names) = openDefinitionInEnv name args $ \_ -> openDefs args names

  checkArgs tel0 synArgs0 []

checkOpen
  :: (Unify t) => QName -> CCheckM t
checkOpen _ cont = cont

-- Bringing everything together
------------------------------------------------------------------------

-- Checking programs
--------------------

newtype Checker' = Checker' { unpack ::
                                forall m. (MonadConf m, MonadIO m) =>
                                (forall a. SA.Module -> (forall t. (Unify t) =>
                                          Signature t -> Maybe PP.Error -> m a) -> m a) }
type Checker = CmdModule Checker'

pattern Checker :: String
                     -> String
                     -> (forall m. (MonadConf m, MonadIO m) => forall a.
                         SA.Module
                         -> (forall t. Unify t => Signature t -> Maybe PP.Error -> m a)
                         -> m a)
                     -> CmdModule Checker'
pattern Checker a b c = CmdModule a b (Checker' c)

checkers :: [Checker]
checkers = [ mkChecker @Simple
           , mkChecker @Suspended
           , mkChecker @GraphReduce
           , mkChecker @GraphReduceUnpack
           , mkChecker @HashConsed2
           , mkChecker @HashConsed4
           ]

mkChecker :: forall a. Unify a => Checker
mkChecker = Checker (shortName @a) (longName @a)$ checkFile' @a 

  {-
  Checker "S" "Simple"$ checkFile' @Simple
 ,Checker "P" "Suspended"$ checkFile' @Suspended
 ,Checker "GR" "GraphReduce"$ checkFile' @GraphReduce
 ,Checker "GRU" "GraphReduceUnpack"$ checkFile' @GraphReduceUnpack
 --,Checker "H" "Hashed"$ checkFile' @Hashed
 --,Checker "HC2" "HashConsed2"$ checkFile' @HashConsed2
 --,Checker "HC3" "HashConsed3"$ checkFile' @HashConsed3
 ,Checker "HC4" "HashConsed4"$ checkFile' @HashConsed4
 --,Checker "HC4P" "HashConsed4P"$ checkFile' @HashConsed4P
 --,Checker "PH" "SuspendedHC"$ checkFile' @SuspendedHC
 --,Checker "PHI" "SuspendedHCI"$ checkFile' @SuspendedHCI
 ]
-}
checkFile
  :: forall m a. (MonadConf m, MonadIO m)
  => SA.Module
  -> (forall t. (Unify t) => Signature t -> Maybe PP.Error -> m a) -> m a
checkFile decls ret = do
  tt <- confTermType <$> readConf
  case find ((==) tt . opt) checkers of
    Just (cmd -> checker) -> unpack checker decls ret
    Nothing -> (sigEmpty :: m (Signature Simple)) >>= flip ret (Just (ppGenericError$ "Invalid term type" <+> PP.text tt))

checkFile'
    :: forall t a m. (Unify t, MonadConf m, MonadIO m)    
    => SA.Module -> (Signature t -> Maybe PP.Error -> m a) -> m a
checkFile' decls0 ret = do
    quiet <- confQuiet <$> readConf
    unless quiet $ do
      drawLine
      liftIO$ putStrLn "-- Checking declarations"
    s <- initCheckState
    -- For the time being we always start a dummy block here
    (mbErr, sig, _) <- (sigEmpty :: m (Signature t)) >>= \sig -> runTC sig () s $ termReprInitialize *> do
      err <- flip catchError (return . Just) $ do
        magnifyTC (const (initEnv C0)) $ do
          checkModule decls0 $ return ()
        return Nothing
      case err of
        Nothing -> checkSignature <* termReprFinalize
        Just typeError -> do
          catchError checkSignature (\_ -> return ())
          termReprFinalize
          throwError typeError
    ret sig $ either Just (\() -> Nothing) mbErr
  where
    checkSignature :: TC t r (CheckState t) ()
    checkSignature = do
      sig <- askSignature
      -- unsolvedMvs <- metas sig
      let unsolvedMvs = HS.fromList$ sigUninstantiatedMetas sig
      quiet <- confQuiet <$> readConf
      unless quiet $ do
        mvNoSummary <- confNoMetasSummary <$> readConf
        mvReport <- confMetasReport <$> readConf
        mvOnlyUnsolved <- confMetasOnlyUnsolved <$> readConf
        when (not mvNoSummary || mvReport) $ do
          let solvedMvs = catMaybes $ map (sigLookupMetaBody sig) $ sigDefinedMetas sig
          drawLine
          putStrLn' $ "-- Solved Metas: " ++ show (length solvedMvs)
          putStrLn' $ "-- Unsolved Metas: " ++ show (HS.size unsolvedMvs)
          when mvReport $ do
            drawLine
            let mvsTypes = map (\mv -> (mv, sigGetMetaType sig mv)) $ sigDefinedMetas sig
            forM_ (sortBy (comparing fst) $ mvsTypes) $ \(mv, mvType) -> do
              let mbMvb = sigLookupMetaBody sig mv
              when (not (isJust mbMvb) || not mvOnlyUnsolved) $ do
                mvTypeDoc <- prettyM_ mvType
                putStrLn' $ render $
                  PP.pretty mv <+> PP.parens (PP.pretty (srcLoc mv)) <+> ":" //> mvTypeDoc
                when (not mvOnlyUnsolved) $ do
                  mvBody <- case mbMvb of
                    Nothing -> return "?"
                    Just mi -> prettyM_ mi
                  putStrLn' $ render $ PP.pretty mv <+> "=" <+> PP.nest 2 mvBody
                putStrLn' ""
        noProblemsSummary <- confNoProblemsSummary <$> readConf
        problemsReport <- confProblemsReport <$> readConf
        when (not noProblemsSummary || problemsReport) $  do
          drawLine
          ss <- use csSolveState
          printSolveState ss
      doAudit <- confUnifyAudit <$> readConf
      when doAudit $ do
        unless quiet $ drawLine
        use csSolveState >>= \SolveState{sState} -> auditState sState >>= \case
          Left  (loc,error)-> atSrcLoc loc $ checkError error
          Right auditCount -> unless quiet$ putStrLn'$ "-- " <> show auditCount <> " problems audited successfully."
      unless (HS.null unsolvedMvs) $ checkError $ UnsolvedMetas (HS.toList unsolvedMvs) 

      mvCheckMetas <- confCheckMetaConsistency <$> readConf
      when mvCheckMetas $ mapM_ (uncurry checkMetaTypeConsistency) (sigInstantiatedMetas sig)
      unless quiet $ drawLine

    putStrLn' :: forall m. MonadIO m => String -> m ()
    putStrLn' = liftIO . putStrLn

    drawLine :: forall m. MonadIO m => m ()
    drawLine =
      putStrLn' "------------------------------------------------------------------------"
