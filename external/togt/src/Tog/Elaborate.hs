-- | Turns some abstract expression in a term.
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedLists #-}
module Tog.Elaborate
  ( -- * Elaboration
    module Tog.Elaborate.Constraint
  , elaborate

    -- * Elaboration environment
  , Block
  , Env
  , envPending
  , envBlocks
  , extendEnv
  , extendEnv_
  , initEnv
  , startBlock

    -- * Definitions
  , envCtx
  , envTel
  , getOpenedDefinition
  , openDefinitionInEnv
  , openDefinitionInEnv_

    -- * Pretty-printing
  , prettyMEnv 
  , prettyPrecMEnv
  ) where

import           Control.Lens                     ((&), at, (?~))
import           Control.Monad.State              (modify)
import           Control.Monad.Reader             (MonadReader, asks)
import qualified Data.HashMap.Strict              as HMS

import           Tog.Instrumentation
import qualified Tog.Instrumentation.Debug.Label as DL
import           Tog.Names
import           Tog.Names.Sorts
import           Tog.Prelude
import qualified Tog.Abstract                     as SA
import           Tog.Abstract                     (pattern (:@@), pattern (:@@@))
import           Tog.Term
import           Tog.Monad
import           Tog.PrettyPrint                  (($$), (//>))
import qualified Tog.PrettyPrint                  as PP
import           Tog.Elaborate.Constraint         

import           Tog.Unify (SolveState, solveAll, Unify)

#include "impossible.h"

-- We define these types first because of TH restrictions.

-- | A block is an environment where we can open modules.  In practice,
-- where clauses and modules.  They have a context (modules can be
-- parametrised and where clauses have the clause parameters in scope),
-- and a collection of opened names.
data Block t = Block
  { _blockCtx    :: !(Ctx t)
  , _blockOpened :: !(HMS.HashMap QName [Term t])
    -- ^ Stores arguments to opened things.
  }

makeLenses ''Block


instance PrettyM t (Block t) where
  prettyM (Block ctx opened) = do
    ctxDoc <- prettyM ctx
    openedDoc <- prettyM $ HMS.toList opened
    return $
      "Block" $$
      "ctx:" //> ctxDoc $$
      "opened:" //> openedDoc

-- | The environment we do the elaboration is a series of 'Block's plus
--   a dangling context at the end.  The dangling context is the usual
--   context that you would find when type checking---what we get when we
--   traverse abstractions.
--
--   One cannot open a definition if te dangling context is not empty.
data Env t = Env
  { _envBlocks  :: ![Block t]
  , _envPending :: !(Ctx t)
  }

makeLenses ''Env

instance PrettyM t (Env t) where
  prettyM (Env blocks ctx) = do
    blocksDoc <- prettyM blocks
    ctxDoc <- prettyM ctx
    return $
      "Env" $$
      "blocks:" //> blocksDoc $$
      "pending:" //> ctxDoc

-- Elaboration
------------------------------------------------------------------------

type ElabM t a = forall s. TC t (Env t) (s, Constraints t -> TC t (Env t) s ()) a

-- | Pre: In @elaborate Γ A t@, @Γ ⊢ A : Set@.
--
--   Post: If @(u, constrs) <- elaborate Γ A t@, then
--     - @Γ ⊢ u : A@,
--     - If all constraints in @constr@ are solved, @Γ ⊢ t ≡ u : A@.
elaborate
  :: (Unify t) => Type t -> SA.Expr -> TC t (Env t) (SolveState t) (Term t)
elaborate type_ absT = do
  env <- ask
  let msg = do
        locDoc <- PP.pretty <$> askSrcLoc
        envDoc <- prettyMEnv env
        return $
          "loc:" //> locDoc $$
          "env:" //> envDoc
  debugBracket DL.Elaborate msg $ do
    readConf <&> confDelayedDispatch >>= \case
      True -> do
        -- Elaboration with constraint accumulation
        let writer con' = modify (<> con')
        (t, (constrs, _)) <- magnifyStateTC (const ([], writer)) $
          (,) <$> elaborate' type_ absT <*> get
        debug "constraints" $ do
          tDoc <- prettyMEnv t
          constrsDoc <- PP.list . toList <$> mapM prettyMEnv constrs
          return $
            "term:" //> tDoc $$
            "constraints:" //> constrsDoc
        solveAll constrs
        return t
      False ->  do
        -- Elaboration with immediate dispatch
        let writer = solveAll
        magnifyStateReaderTC writer $ elaborate' type_ absT
        

-- | Monad with a RO (Env t) and a modifiable set of constraints
-- type ElabM t = TC t (Env t) (Constraints t)

writeConstraint :: IsTerm t => Constraint t -> ElabM t ()
writeConstraint con' = do
  debugWhenLabel DL.Elaborate$ (("write: " //>) <$> prettyM_ con')
  writer <- snd <$> get
  zoomTC _1 $ writer [con']

-- | Writes a constraint equating a fresh meta-variable of the given
-- type to the typed term it is given.
--
-- Pre: In @expect A B u@, @A : Set@, @B : Set@, and @u : B@.
--
-- Post: if @t <- expect A B u@, @t : A@.
--       envCtx ≡ Γ
--       t ≡ α Γ
--       A constraint   Γ ⊢ α Γ : A ~ u : B
--
--   t is a metavariable ossibly applied to the variables
--   in the context
expect
  :: IsTerm t =>
     Type t -- ^ A : Set
  -> (Term t :∈ Type t) -- ^ u : B : Set
  -> ElabM t (Term t) -- ^ t : A, t ~ u
expect tA (u :∈ tB) =
  ifFastElaborateAnd (synEq tA tB) >>= \case
    Just True  -> return u
    _ -> do
      t <- addMetaInEnv tA
      env <- ask
      loc <- askSrcLoc
      writeConstraint $ JmEq loc (envCtx env) (tA :∋ t) (u :∈ tB)
      return t

-- | Only runs the (potentially expensive) monadic action if fastElaborate is enabled
ifFastElaborateAnd :: MonadConf m => m a -> m (Maybe a)
ifFastElaborateAnd m = do
  ifFastElaborate >>= \case
    True  -> Just <$> m
    False -> return Nothing

-- | Only runs the (potentially expensive) monadic action if fastElaborate is enabled
ifFastElaborate :: MonadConf m => m Bool
ifFastElaborate = readConf <&> confFastElaborate

expectEqual ::
  IsTerm t =>
     Type t -- ^ A : Set
  -> Type t -- ^ B : Set
  -> ElabM t () -- ^ t
expectEqual tA tB = do
  env <- ask
  loc <- askSrcLoc
  writeConstraint $ JmEq loc (envCtx env) (tA :∈ set) (tB :∈ set)

-- | We annotate each case with the correspondent bidirectional
-- type-checking rule.  The elaboration should be fairly close, apart
-- from generating synthetic types when needed (e.g. see the case for
-- 'SA.PI').
--
-- Implementing elaboration rules from the paper. `expect` is used
-- to add the implicit  metavariable+equality_constraint .
elaborate'
  :: (IsTerm t)
  => Type t -- ^  A   : Set
  -> SA.Expr -- ^ e
  -> ElabM t (Term t) -- ^ u ≡ [e] ,  u : A
elaborate' type_ absT = atSrcLoc absT $ do
  let msg = do
        typeDoc <- prettyMEnv type_
        let absTDoc = PP.pretty absT
        return $
          "type:" //> typeDoc $$
          "t:" //> absTDoc
  debugBracket DL.Elaborate msg $ do
    let expect_ = expect type_
    case absT of
      --
      -- -----------------
      --   Γ ⊢ Set : Set
      SA.Set _ -> do
        expect_ (set :∋ set)
      --   Γ ⊢ A : Set    Γ, x : A ⊢ B : Set
      -- -------------------------------------
      --   Γ ⊢ (x : A) → B : Set
      SA.Pi (name :@ _) synDom synCod -> do
        dom <- elaborate' set synDom
        cod <- extendEnv_ (name, dom) $ elaborate' set synCod
        t <- pi dom (Abs name cod)
        expect_ (set :∋ t)
      SA.Fun synDom synCod -> do
        elaborate' type_ (SA.Pi (pure "_") synDom synCod)
      --   α : Γ → A ∈ Σ
      -- -----------------
      --   Γ ⊢ α Γ : A
      SA.Meta _ -> do
        mvT <- addMetaInEnv type_
        return mvT
      --   Γ ⊢ A : Set    Γ ⊢ t : A    Γ ⊢ u : A
      -- -----------------------------------------
      --   Γ ⊢ t ≡_A u : Set
      SA.Equal synType synT1 synT2 -> do
        type' <- elaborate' set synType
        t1 <- elaborate' type' synT1
        t2 <- elaborate' type' synT2
        t <- equal type' t1 t2
        expect_ (set :∋ t)
      --   Γ, x : A ⊢ t : B
      -- -----------------------------
      --   Γ ⊢ \x -> t : (x : A) → B
      SA.Lam (name :@ _) synBody ->
        ifFastElaborateAnd (viewW type_) >>= \case
          Just (Pi dom (Abs_ cod)) -> do
            (lam . Abs name) =<< extendEnv_ (name, dom) (elaborate' cod synBody)
          _ -> do 
            dom <- addMetaInEnv set
            (cod, body) <- extendEnv_ (name, dom) $ do
              cod <- addMetaInEnv set
              body <- elaborate' cod synBody
              return (cod, body)
            type' <- pi dom (Abs name cod)
            t <- lam (Abs name body)
            expect_ (type' :∋ t)
      --   Γ ⊢ A : Set    Γ ⊢ t : A    Γ ⊢ u : A
      -- -----------------------------------------
      --   Γ ⊢ refl : t ≡_A u
      --
      -- Note that we don't have the type or the term, so we put metas.
      SA.Refl _ -> do
        ifFastElaborateAnd (viewW type_) >>= \case
          Just (Equal tA t u) ->
            synEq t u >>= \case
              True  -> return refl
              False -> do
                type' <- equal tA t t
                expect_ (type' :∋ refl)
          _ -> do
            eqType <- addMetaInEnv set
            t1 <- addMetaInEnv eqType
            type' <- equal eqType t1 t1
            expect_ (type' :∋ refl)
      --   c : Δ → Ψ → D Δ ∈ Σ
      --   ∀ i. Γ ⊢ tᵢ : Δᵢ (every tycon arg is well-typed)
      --   ∀ j. Γ ⊢ uⱼ : Ψⱼ (every datacon arg is well-typed)
      -- -----------------------------------------------------
      --   Γ ⊢ c u₁ ⋯ tₘ : D Δ
      --
      -- Again, we don't have the tycon args, so we put meta-variables
      -- instead.
      SA.Con (dataCon0 :@@@ _) synArgs -> do
        elaborateCon' type_ dataCon0 synArgs

      SA.App h elims -> do
        elaborateApp' type_ h elims


-- | Yields the constraints necessary to typecheck an application, and
--   reports it.
elaborateCon'
  :: (IsTerm t)
  => Type t
  -- ^ Type of the result of applying the head to the elims (B)
  -> ConName
  -- ^ Constructor
  -> [SA.Expr]
  -- ^ Elims
  -> ElabM t (Term t)
  -- ^ Term equivalent to  h @ ē, but which is easily  checked to be
  --   of type B.
elaborateCon' type_ con args = do
  let msg = do
        typeDoc <- prettyMEnv type_
        return $
          "type:" //> typeDoc $$
          "con:" //> PP.pretty con $$
          "args:" //> PP.pretty args
  debugBracket DL.ElaborateCon msg $
    ifFastElaborate >>= \case
      True  -> elaborateConInfer type_ con (fromList args)
      False -> elaborateCon      type_ con (fromList args)

elaborateConInfer :: IsConName con => IsTerm t => Type t -> con -> [SA.Expr] -> ElabM t (Term t)
elaborateConInfer type_ dataCon0 synArgs = do
  let fallback = elaborateCon type_ dataCon0 synArgs
  viewW type_ >>= \case 
    App (Def (OTyCon tyCon')) tyConArgs -> do
      (dataCon, DataCon tyCon _ dataConType) <- getOpenedDefinition dataCon0
      synEq tyCon tyCon' >>= \case
        False -> fallback
        True  -> do
          Just tyConArgs' <- pure$ mapM isApply tyConArgs
          appliedDataConType <- openContextual dataConType tyConArgs'
          dataConArgs <- elaborateDataConArgs appliedDataConType synArgs
          t <- con dataCon dataConArgs
          return t
    _ -> fallback

elaborateCon :: IsConName con => IsTerm t => Type t -> con -> [SA.Expr] -> ElabM t (Term t)
elaborateCon type_ dataCon0 synArgs = do
  (dataCon, DataCon tyCon _ dataConType) <- getOpenedDefinition$ dataCon0
  tyConType <- definitionType =<< getDefinition tyCon
  tyConArgs <- fillArgsWithMetas tyConType
  appliedDataConType <- openContextual dataConType tyConArgs
  dataConArgs <- elaborateDataConArgs appliedDataConType synArgs
  type' <- def tyCon $ map Apply tyConArgs
  t <- con dataCon dataConArgs
  expect type_ (type' :∋ t)

-- | Takes a telescope in the form of a Pi-type and replaces all it's
-- ‘domains’ with metavariables of that type.
fillArgsWithMetas :: IsTerm t =>
                     Type t -- ∏Γ.Set
                  -> ElabM t [Term t] -- [ γ : Γ ]
fillArgsWithMetas type' = do
  typeView <- whnfView type'
  case typeView of
    Pi dom cod -> do
      arg <- addMetaInEnv dom
      cod' <- instantiate_ cod arg
      (arg :) <$> fillArgsWithMetas cod'
    Set -> do
      return []
    _ -> do
      -- The tycon must end with Set
      __IMPOSSIBLE__

-- | Elaborates each of the arguments of a data constructor, in sequence
elaborateDataConArgs
  :: (IsTerm t) => Type t -> [SA.Expr] -> ElabM t [Term t]
elaborateDataConArgs _ [] =
  return []
elaborateDataConArgs type_ (synArg : synArgs) = do
  Pi dom cod <- whnfView type_
  arg <- elaborate' dom synArg
  cod' <- instantiate_ cod arg
  args <- elaborateDataConArgs cod' synArgs
  return (arg : args)

-- | Infers the the type of the function in an application,
--   for applications in βη-normal form (note that it's not
--   βηδ-normal form.
inferHead
  :: (IsTerm t)
  => SA.Head
  -- ^ A function, a definition or the J axiom
  -> ElabM t (Term t :∈ Type t)
  -- ^ The function applied to an empty list of arguments, and the
  --   resulting type.
inferHead synH = atSrcLoc synH $ case synH of
  --   x : A ∈ Γ
  -- -------------
  --   Γ ⊢ x ⇒ A
  SA.Var (name :@ _) -> do
    mbV <- lookupName name
    case mbV of
      Nothing -> do
        -- We have already scope checked
        __IMPOSSIBLE__
      Just (v, type_) -> do
        h <- app (Var v) []
        return (h :∈ type_)
  --   f : A ∈ Σ
  -- -------------
  --   Γ ⊢ f ⇒ A
  SA.Def (name0 :@@@ _) -> do
    (name, def') <- getOpenedDefinition name0
    type_ <- definitionType def'
    h <- def name []
    return (h :∈ type_)
  --
  -- --------------------------------------------------------------
  --   Γ ⊢ J ⇒ (A : Set) → (x : A) → (y : A) ->
  --           (P : (x : A) → (y : A) → (eq : x =={A} y) → Set) →
  --           (p : (x : A) → P x x refl) →
  --           (eq : x =={A} y) ->
  --           P x y eq
  SA.J{} -> do
    h <- app J []
    return (h :∈ typeOfJ)

-- | Yields the constraints necessary to typecheck an application, and
--   reports it.
elaborateApp'
  :: (IsTerm t)
  => Type t
  -- ^ Type of the result of applying the head to the elims (B)
  -> SA.Head
  -- ^ Head
  -> [SA.Elim]
  -- ^ Elims
  -> ElabM t (Term t)
  -- ^ Term equivalent to  h @ ē, but which is easily  checked to be
  --   of type B.
elaborateApp' type_ h elims = do
  let msg = do
        typeDoc <- prettyMEnv type_
        return $
          "type:" //> typeDoc $$
          "head:" //> PP.pretty h $$
          "elims:" //> PP.pretty elims
  debugBracket DL.ElaborateApp msg $
    ifFastElaborate >>= \case
      True  -> expect       type_ =<< elaborateAppInfer h (fromList elims)
      False -> elaborateApp type_                       h (fromList elims)

-- | Helper function for elaborateApp'

--   Also, this function is not tail recursive,
--   it will use as much stack as the length of the list
--   of eliminators.
elaborateApp
  :: (IsTerm t)
  => Type t
  -- ^ Type of the result of applying the head to the elims
  -> SA.Head -> Bwd (SA.Elim)
  -> ElabM t (Term t)
elaborateApp type_ h [] = atSrcLoc h $ do
  --   Γ ⊢ h ⇒ A
  -- ------------------
  --   Γ ⊢ h · : A
  expect type_ =<< inferHead h
elaborateApp type_ h (elims :. SA.Apply arg) = atSrcLoc arg $ do
  --   Γ ⊢ h e̅ : (x : A) → B    Γ ⊢ u : A
  -- --------------------------------------
  --   Γ ⊢ h e̅ u : B[x := u]
  dom <- addMetaInEnv set
  
  cod <- Abs_ <$> (extendEnv_ ("_", dom) $ addMetaInEnv set)
  typeF <- pi dom cod
  arg' <- elaborate' dom arg
  f <- elaborateApp typeF h elims
  type' <- instantiate_ cod arg'
  t <- eliminate f [Apply arg']
  expect type_ (type' :∋ t)
elaborateApp type_ h (elims :. SA.Proj (projName0 :@@@ loc)) = atSrcLoc loc $ do
  --   Γ ⊢ h e̅ : D Δ
  --   π : (x : D Δ) → A ∈ Σ (π is a projection for D)
  -- -------------------------------------------------------
  --   Γ ⊢ h e̅ π : A[x := h e̅]
  (projName, Projection projIx tyCon projType) <- getOpenedDefinition projName0
  let proj  = first (`Projection'` projIx) projName
  tyConType <- definitionType =<< getDefinition tyCon
  tyConArgs <- fillArgsWithMetas tyConType
  typeRec <- def tyCon (map Apply tyConArgs)
  rec_ <- elaborateApp typeRec h elims
  type0 <- openContextual projType tyConArgs
  Pi _ type1 <- whnfView type0
  type' <- instantiate_ type1 rec_
  t <- eliminate rec_ [Proj (opndKey proj)]
  expect type_ (type' :∋ t)

--   Also, this function is not tail recursive,
--   it will use as much stack as the length of the list
--   of eliminators.
elaborateAppInfer
  :: (IsTerm t)
  => SA.Head -> Bwd (SA.Elim)
  -> ElabM t (Term t :∈ Type t)
elaborateAppInfer h [] = atSrcLoc h $ do
  --   Γ ⊢ h ⇒ A
  -- ------------------
  --   Γ ⊢ h · : A
  inferHead h
elaborateAppInfer h (elims :. SA.Apply arg) = atSrcLoc arg $ do
  (f :∈ typeF) <- elaborateAppInfer h elims
  --   Γ ⊢ t : (x : A) → B    Γ ⊢ u : A
  -- --------------------------------------
  --   Γ ⊢ t u : B[x := u]
  typeF & whnfView >>= \case
    Pi dom cod -> do
      -- It's already a Π-type, no need to create constraints or metas!
      arg'  <- elaborate' dom arg
      type' <- instantiate_ cod arg'
      t     <- eliminate f [Apply arg']
      return$ t :∈ type' 

    _ -> do 
      -- Let there be cake! (beat)

      -- Define a possible Π-type
      dom <- addMetaInEnv set
      cod <- Abs_ <$> (extendEnv_ ("_", dom) $ addMetaInEnv set)
      typeF' <- pi dom cod

      -- Make f be of that Π-type!
      f' <- expect typeF' (f :∈ typeF)

      -- Compute the type of the application
      arg'  <- elaborate' dom arg
      type' <- instantiate_ cod arg'
      t     <- eliminate f' [Apply arg']
      return (t :∈ type')

elaborateAppInfer h (elims :. SA.Proj (projName0 :@@@ loc)) = atSrcLoc loc $ do
  (f :∈ typeF) <- elaborateAppInfer h elims
  --   Γ ⊢ h e̅ : D Δ
  --   π : (x : D Δ) → A ∈ Σ (π is a projection for D)
  -- -------------------------------------------------------
  --   Γ ⊢ h e̅ π : A[x := h e̅]
  (projName, Projection projIx tyCon projType) <- getOpenedDefinition projName0
  let proj  = first (`Projection'` projIx) projName
  tyConType <- definitionType =<< getDefinition tyCon
  tyConArgs <- fillArgsWithMetas tyConType
  typeRec <- def tyCon (map Apply tyConArgs)
  rec_ <- expect typeRec (f :∈ typeF)
  type0 <- openContextual projType tyConArgs
  Pi _ type1 <- whnfView type0
  type' <- instantiate_ type1 rec_
  t <- eliminate rec_ [Proj (opndKey proj)]
  return (type' :∋ t)

-- Elaboration environment
------------------------------------------------------------------------

initEnv :: Ctx t -> Env t
initEnv ctx = Env [Block ctx HMS.empty] C0

-- Definitions

-- | Context in which the current definition should be elaborated.
--   Also, all variables that are accessible by the current definition.
envCtx :: Env t -> Ctx t
envCtx (Env blocks ctx) = mconcat $ reverse $ ctx : map _blockCtx blocks


envTel :: Env t -> Tel t
envTel (Env blocks ctx) = mconcat $ map ctxToTel $ reverse $ ctx : map _blockCtx blocks

-- | Opens an existing definition from the signature,
--   applying it to the arguments in the elaboration environment.
getOpenedDefinition
  :: forall t s qname. (IsTerm t, IsQName qname) => qname -> TC t (Env t) s (Opened qname t, Definition Opened t)
getOpenedDefinition name0 = do
  args <- getOpenedArgs name0
  sig <- askSignature
  def' <- openDefinition (sigGetDefinition sig name0) args
  return (Opened name0 args, def')
  where
    -- | Get the arguments of an opened name.
--    getOpenedArgs :: QName -> _ [t]
    getOpenedArgs :: qname -> TC t (Env t) s [Term t]
    getOpenedArgs name = do
      env <- ask
      go (ctxLength (env^.envPending)) (env^.envBlocks)
      where
        go _ [] = do
          __IMPOSSIBLE__
        go n (block : blocks) = do
          case HMS.lookup (getQName name) (block^.blockOpened) of
            Nothing   -> go (n + ctxLength (block^.blockCtx)) blocks
            Just args -> fmap coerce $ weaken_ n (coerce args :: [OpenTerm t])

-- | Open a definition with the given arguments.  Must be done in an
-- empty 'envPending'.
openDefinitionInEnv
  :: IsQName qname => qname -> [Term t] -> (Opened qname t -> TC t (Env t) s a)
  -> TC t (Env t) s a
openDefinitionInEnv name args cont = do
  env <- ask
  -- We can open a definition only when the context is empty (e.g. not
  -- inside a lambda) and there is at least one block.
  case env of
    Env (block : blocks) C0 -> do
      let block' = block & blockOpened . at (getQName name) ?~ args
      magnifyTC (const (Env (block' : blocks) C0)) $ cont $ Opened name args
    _ ->
      __IMPOSSIBLE__

-- | Open a definition using the arguments variables in 'elabCtx' as arguments.
--   Once the arguments are applied, the definition should be valid in an
--   empty context.
openDefinitionInEnv_
  :: (IsTerm t, IsQName qname)
  => qname -> (Opened qname t -> TC t (Env t) s a)
  -> TC t (Env t) s a
openDefinitionInEnv_ n cont = do
  args <- mapM var . ctxVars =<< asks envCtx
  openDefinitionInEnv n args cont

-- | Pushes a new block on 'envBlocks', using the current 'envPending'.
startBlock :: TC t (Env t) s a -> TC t (Env t) s a
startBlock cont = do
  Env blocks ctx <- ask
  let env' = Env (Block ctx HMS.empty : blocks) C0
  magnifyTC (const env') cont

-- | Appends the given 'Type' to the current 'envPending'
extendEnv_ :: (Name, Type t) -> TC t (Env t) s a -> TC t (Env t) s a
extendEnv_ type_ = extendEnv (C0 :< type_)

-- | Appends the given 'Ctx' to the current 'envPending'.
extendEnv :: Ctx t -> TC t (Env t) s a -> TC t (Env t) s a
extendEnv ctx = magnifyTC (over envPending (<> ctx))

-- | Adds a meta-variable using the current 'envCtx' as context.
addMetaInEnv :: (IsTerm t) => Type t -> ElabM t (Term t)
addMetaInEnv type_ = do
  ctx <- asks envCtx
  snd <$> addMetaInCtx ctx type_

-- | Looks up a name (i.e. a variable) in the current 'envCtx' (i.e. elaboration
--   environment.
lookupName
  :: (IsTerm t) => Name -> ElabM t (Maybe (Var, Type t))
lookupName n = do
  ctx <- asks envCtx
  ctxLookupName n ctx


-- Pretty printing
---------------------

prettyMEnv :: (MonadReader (Env u) m, MonadTerm t m, PrettyM t a) => a -> m PP.Doc
prettyMEnv a = asks envCtx >>= \ctx -> prettyMWithCtx ctx a

prettyPrecMEnv :: (MonadReader (Env u) m, MonadTerm t m, PrettyM t a) => Int -> a -> m PP.Doc
prettyPrecMEnv p a = asks envCtx >>= \ctx -> prettyPrecMWithCtx ctx p a

