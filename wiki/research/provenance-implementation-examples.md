# Provenance Implementation Examples from Production Systems

**Date:** 2026-05-06  
**Companion to:** [[provenance-deep-dive]]

This document provides **concrete code examples** from production elaborators showing how provenance tracking is implemented.

---

## 1. Lean 4: MetavarContext with Provenance

### 1.1 MetavarDecl Structure

**Source:** `src/Lean/MetavarContext.lean`

```lean
structure MetavarDecl where
  /-- Local context where the metavariable was declared -/
  lctx : LocalContext
  /-- Index in the local context for efficient lookup -/
  localInstances : Array LocalInstance
  /-- Type of the metavariable -/
  type : Expr
  /-- User-facing name for pretty-printing -/
  userName : Name
  /-- Depth level for universe constraints -/
  depth : Nat := 0
  /-- Index for ordering (creation time) -/
  index : Nat
  /-- Metavariable kind -/
  kind : MetavarKind
  /-- Number of delayed assignments -/
  numScopeArgs : Nat := 0
  deriving Inhabited

structure MetavarContext where
  /-- Counter for generating fresh metavariable IDs -/
  mvarCounter : Nat := 0
  /-- Map from metavariable ID to declaration -/
  decls : PersistentHashMap MVarId MetavarDecl := {}
  /-- Map from user-friendly names to IDs -/
  userNames : PersistentHashMap Name MVarId := {}
  /-- Assignment table for expression metavariables -/
  eAssignment : PersistentHashMap MVarId Expr := {}
  /-- Assignment table for level metavariables -/
  lAssignment : PersistentHashMap LMVarId Level := {}
  /-- Delayed assignments (for pattern variables) -/
  dAssignment : PersistentHashMap MVarId DelayedMetavarAssignment := {}
  deriving Inhabited
```

**Key observations:**
- Each `MetavarDecl` captures the **local context** at creation time
- `index` field provides creation ordering
- `kind` distinguishes synthetic vs. natural vs. synthetic opaque

### 1.2 Creating Metavariables with Context

**Source:** `src/Lean/Meta/Basic.lean`

```lean
def mkFreshExprMVar (type : Expr) (kind : MetavarKind := MetavarKind.natural)
    (userName : Name := Name.anonymous) : MetaM Expr := do
  let mctx ← getMCtx
  let lctx ← getLCtx
  let localInstances ← getLocalInstances
  let depth ← getLevel
  
  -- Create declaration with full context
  let decl := {
    lctx := lctx
    localInstances := localInstances
    type := type
    userName := userName
    depth := depth
    index := mctx.mvarCounter  -- Creation timestamp
    kind := kind
  }
  
  let mvarId := { name := `_uniq ++ toString mctx.mvarCounter }
  let mctx := mctx.addDecl mvarId decl
  setMCtx mctx
  return mkMVar mvarId
```

**Provenance captured:**
- ✅ Local context (`lctx`)
- ✅ Universe depth (`depth`)
- ✅ Creation index (`mvarCounter`)
- ✅ User-facing name (`userName`)
- ✅ Metavariable kind (`kind`)

---

## 2. Agda: MetaVariable with TargetType and Constraints

### 2.1 MetaVariable Structure

**Source:** `src/full/Agda/TypeChecking/Monad/Base.hs`

```haskell
data MetaVariable = MetaVariable
  { mvInfo :: MetaInfo
  , mvPriority :: MetaPriority
  , mvPermutation :: Permutation
  , mvJudgement :: Judgement MetaId
  , mvInstantiation :: MetaInstantiation
  , mvListeners :: Set Listener
  , mvFrozen :: Frozen
  , mvTwin :: Maybe MetaId
  }

data MetaInfo = MetaInfo
  { miClosRange :: Closure Range  -- Provenance: source location
  , miModality :: Modality
  , miMetaOccursCheck :: Bool
  , miNameSuggestion :: String  -- For error messages
  , miGeneralizable :: Arg DoGeneralize
  }
```

**Key provenance field:** `miClosRange :: Closure Range`

```haskell
-- A Closure wraps a value with its environment
data Closure a = Closure
  { clSignature :: Signature
  , clEnv :: TCEnv
  , clScope :: ScopeInfo
  , clModuleToSource :: ModuleToSource
  , clValue :: a
  }

-- When creating a meta:
newMetaFromContext :: Type -> TCM MetaId
newMetaFromContext typ = do
  range <- asks envRange  -- Current source range
  let info = MetaInfo
        { miClosRange = buildClosure range  -- Captures env!
        , miNameSuggestion = ""
        , ...
        }
  newMeta' Instantiable info normalMetaPriority (permuteVars) (HasType typ)
```

**Provenance captured:**
- ✅ Source range with environment (`Closure Range`)
- ✅ Name suggestion for error messages
- ✅ Permutation (variable scoping)
- ✅ Priority (for constraint solving order)

### 2.2 Constraint Structure with Origin

**Source:** `src/full/Agda/TypeChecking/Monad/Constraints.hs`

```haskell
data Constraint
  = ValueCmp Comparison CompareAs Term Term
  | ValueCmpOnFace Comparison Term Type Term Term
  | ElimCmp [Polarity] [IsForced] Type Term [Elim] [Elim]
  | SortCmp Comparison Sort Sort
  | LevelCmp Comparison Level Level
  | IsEmpty Range Type
  | CheckSizeLtSat Term
  | FindInstance MetaId (Maybe [Candidate])
  | ResolveInstanceHead QName
  | CheckFunDef Delayed DefInfo QName [Clause] TCErr
  | UnBlock MetaId  -- Wake up when meta solved
  | Guarded Constraint ProblemId

data ProblemConstraint = ProblemConstraint
  { theConstraint :: Closure Constraint
  , constraintProb :: ProblemId
  }
```

**Tracking blocked constraints:**
```haskell
-- When a constraint is blocked on a meta:
blockConstraintOn :: Blocker -> Constraint -> TCM ()
blockConstraintOn blocker c = do
  pid <- newProblem
  addConstraint blocker (ProblemConstraint (buildClosure c) pid)

-- Blocker: refined blocking information
data Blocker
  = UnblockOnMeta MetaId
  | UnblockOnDef QName
  | UnblockOnAll [Blocker]
  | UnblockOnAny [Blocker]
```

**When meta is solved:**
```haskell
assignV :: MetaId -> Args -> Term -> TCM ()
assignV x args v = do
  -- Solve the meta
  updateMetaVar x $ \mv -> mv { mvInstantiation = InstV args v }
  -- Wake up blocked constraints
  wakeupConstraints x

wakeupConstraints :: MetaId -> TCM ()
wakeupConstraints x = do
  cs <- takeConstraints (blockedOn x)
  solveAwakeConstraints cs
```

---

## 3. GHC: Zonking with Error Context

### 3.1 ZonkEnv and Origin Tracking

**Source:** `compiler/GHC/Tc/Zonk/Env.hs`

```haskell
data ZonkEnv = ZonkEnv
  { ze_flexi :: ZonkFlexi
  , ze_tv_env :: TyCoVarEnv TyCoVar  -- Skolemization mapping
  , ze_id_env :: IdEnv Id            -- Variable renaming
  , ze_meta_tv_env :: TyVarEnv Type  -- Solved metas cache
  }

data ZonkFlexi
  = DefaultFlexi      -- Default unbound tyvars to Any
  | SkolemiseFlexi    -- Skolemise unbound tyvars
  | RuntimeUnkFlexi   -- Keep unbound tyvars as RuntimeUnk
```

**Zonking with error reporting:**
```haskell
zonkTcTypeToType :: ZonkEnv -> TcType -> TcM Type
zonkTcTypeToType env ty = go ty
  where
    go (TyVarTy tv)
      | isTcTyVar tv
      = case tcTyVarDetails tv of
          MetaTv {} -> do
            mb_ty <- readMetaTyVar tv
            case mb_ty of
              Flexi -> zonkFlexiTyVar env tv  -- Error or default
              Indirect ty' -> go ty'
          _ -> zonkTyCoVarOcc env tv
      | otherwise = zonkTyCoVarOcc env tv

    go (AppTy t1 t2) = mkAppTy <$> go t1 <*> go t2
    -- ... other cases

zonkFlexiTyVar :: ZonkEnv -> TcTyVar -> TcM Type
zonkFlexiTyVar (ZonkEnv { ze_flexi = flexi }) tv
  = case flexi of
      DefaultFlexi -> do
        -- Unsolved meta: report error with context
        traceTc "Defaulting" (ppr tv)
        defaultTyVar tv

      SkolemiseFlexi -> do
        -- Convert to skolem for RULE LHS
        details <- readMetaTyVar tv
        skolemiseTcTyVar tv

      RuntimeUnkFlexi ->
        -- Keep as runtime unknown
        return (mkTyVarTy tv)
```

**Error context preservation:**
```haskell
-- When reporting unsolved meta:
reportUnsolvedMeta :: TcTyVar -> TcM a
reportUnsolvedMeta tv = do
  tidy_env <- tcInitTidyEnv
  let (tidy_env', tidy_tv) = tidyOpenTyCoVar tidy_env tv
  let msg = mkErrInfo tidy_env' $
              text "Couldn't match type variable" <+> quotes (ppr tidy_tv)
  failWithTcM (tidy_env', msg)
```

### 3.2 ObligationCause (Haskell's Constraint Origin)

**Source:** `compiler/GHC/Tc/Types/Constraint.hs`

```haskell
data CtOrigin
  = GivenOrigin SkolemInfo
  | OccurrenceOf Name
  | OccurrenceOfRecSel Name
  | AppOrigin
  | SpecPragOrigin UserTypeCtxt
  | TypeEqOrigin { uo_actual :: TcType
                 , uo_expected :: TcType
                 , uo_thing :: Maybe SDoc  -- What we're checking
                 }
  | KindEqOrigin TcType TcType CtOrigin (Maybe TypeOrKind)
  | IPOccOrigin HsIPName
  | LiteralOrigin HsOverLit
  | PatOrigin ConLike
  | ViewPatOrigin
  | CycleBreakerOrigin CtOrigin
  | FunDepOrigin1 PredType CtLoc PredType CtLoc
  | FunDepOrigin2 PredType CtOrigin PredType SrcSpan
  | -- ... 30+ more variants

data CtLoc = CtLoc
  { ctl_origin :: CtOrigin
  , ctl_env :: CtLocEnv
  , ctl_t_or_k :: Maybe TypeOrKind
  , ctl_depth :: SubGoalDepth
  }
```

**Creating constraints with origin:**
```haskell
emitWantedEq :: CtOrigin -> TypeOrKind -> TcType -> TcType -> TcM Coercion
emitWantedEq origin t_or_k ty1 ty2 = do
  loc <- getCtLocM origin (Just t_or_k)
  let ct = mkNonCanonical $
           CtWanted { ctev_pred = mkEqPred ty1 ty2
                    , ctev_dest = EvVarDest ev_id
                    , ctev_loc = loc
                    }
  emitSimple ct
  return (mkTcCoVarCo ev_id)
```

**Error reporting with origin:**
```haskell
reportWantedEqErr :: Ct -> TcM ErrMsg
reportWantedEqErr ct = do
  let loc = ctLoc ct
      origin = ctl_origin loc
      (ty1, ty2) = getEqPredTys (ctPred ct)

  tidy_env <- tcInitTidyEnv
  let msg = case origin of
        TypeEqOrigin { uo_thing = Just what } ->
          hang (text "Couldn't match" <+> what)
            2 (ppr_ty_app ty1 ty2)

        AppOrigin ->
          text "Couldn't match expected type" <+> quotes (ppr ty1) $$
          text "            with actual type" <+> quotes (ppr ty2)

        -- ... 30+ more cases with specific messages

  mkErrTcM (tidy_env, msg)
```

---

## 4. Idris 2: Core.Unify with Constraint Retry

### 4.1 UnifyState and Constraint Queue

**Source:** `src/Core/UnifyState.idr`

```idris
record UnifyState where
  constructor MkUnifyState
  holes : IntMap (FC, Name)  -- Unsolved holes with location
  currentHoles : IntMap (FC, Name)
  constraints : IntMap Constraint
  dotConstraints : IntMap Constraint
  nextName : Int
  nextConstraint : Int
  delayedWork : List (FC, Core ())
  logLevel : Nat

data Constraint : Type where
  MkConstraint : {vars : _} ->
                 FC -> (retry : Bool) -> (blocked : List Name) ->
                 Env Term vars -> (x : Term vars) -> (y : Term vars) ->
                 Constraint

data ConstraintSuccess
  = Success
  | NoMore  -- No more attempts needed
  | FailBlocked  -- Blocked on unsolved names
```

**Creating constraints with location:**
```idris
constrain : FC -> Env Term vars -> Term vars -> Term vars -> Core ()
constrain fc env x y = do
  c <- getNextConstraintID
  addConstraint c (MkConstraint fc True [] env x y)

unify : {vars : _} -> FC -> Env Term vars -> Term vars -> Term vars ->
        Core ()
unify fc env x y = do
  defs <- get Ctxt
  inMatch <- getInMatch
  comp <- getCompiling
  case comp of
    -- If compiling, just add constraint (don't solve immediately)
    CompileTime => constrain fc env x y
    _ => do
      -- Immediate unification
      res <- unifyWithMetas fc env x y
      case res of
        (True, []) => pure ()
        (_, cs) => traverse_ (\c => constrain fc env (fst c) (snd c)) cs
```

**Retry mechanism:**
```idris
retryDelayed : Core (List Error)
retryDelayed = do
  ust <- get UST
  let cs = constraints ust
  if null cs
    then pure []
    else do
      -- Try solving all constraints
      cs' <- traverse tryConstraint (IntMap.toList cs)
      let (solved, stuck) = partition isSolved cs'

      -- Remove solved constraints
      traverse_ (\(i, _) => deleteConstraint i) solved

      -- Report stuck constraints if no progress
      if length stuck == length cs
        then pure (map constraintError stuck)
        else retryDelayed  -- Loop until fixpoint

tryConstraint : (Int, Constraint) -> Core (Int, ConstraintSuccess)
tryConstraint (i, MkConstraint fc retry blocked env x y) = do
  defs <- get Ctxt
  case unifyNoEta fc env x y of
    Right () => pure (i, Success)
    Left err =>
      if retry
        then pure (i, FailBlocked)  -- Will retry
        else throw err  -- Hard failure
```

### 4.2 Error Reporting with FC (FileContext)

**Source:** `src/Core/FC.idr`

```idris
data FC = MkFC String (Int, Int) (Int, Int)  -- File, start pos, end pos
        | EmptyFC
        | VirtualFC String  -- Synthetic location

-- Attach FC to every term and constraint
data Term : List Name -> Type where
  Local : FC -> Elem x vars -> Term vars
  Ref : FC -> NameType -> Name -> Term vars
  Meta : FC -> Name -> Int -> List (Term vars) -> Term vars
  Bind : FC -> (x : Name) -> Binder (Term vars) ->
         Term (x :: vars) -> Term vars
  App : FC -> Term vars -> Term vars -> Term vars
  -- ... all constructors have FC
```

**Using FC in error messages:**
```idris
showError : {auto c : Ref Ctxt Defs} -> Error -> Core String
showError (CantUnify fc env x y) = do
  xstr <- toFullNames (quote (Erased fc False) env x)
  ystr <- toFullNames (quote (Erased fc False) env y)
  pure $ show fc ++ ":" ++
         "Mismatch between: " ++ show xstr ++ "\n" ++
         "            and : " ++ show ystr

-- Output:
-- example.idr:12:5--12:10:
-- Mismatch between: Nat
--             and : Bool
```

---

## 5. elaboration-zoo: Minimal Provenance Example

### 5.1 András Kovács' Approach

**Source:** `elaboration-zoo/03-holes/Main.hs`

```haskell
-- MetaContext stores metavariables
type MetaContext = IORef (IntMap MetaEntry)

data MetaEntry
  = Solved ~Val
  | Unsolved

-- Fresh meta creation
freshMeta :: Cxt -> VTy -> IO Tm
freshMeta cxt ~a = do
  m <- readIORef nextMeta
  writeIORef nextMeta $! (m + 1)
  let mty = eval [] $ closeTy (locals cxt) (quote (lvl cxt) a)
  modifyIORef' mcxt $ IM.insert m (Unsolved)
  pure $! InsertedMeta (MetaVar m) (bds cxt)
```

**No provenance tracked!** This is a **minimal teaching implementation**.

### 5.2 Adding Minimal Provenance (Extension)

```haskell
-- EXTENDED VERSION (not in original):
data MetaEntry
  = Solved ~Val
  | Unsolved
      { metaTy :: VTy
      , metaSource :: Maybe (FilePath, Pos, Pos)  -- Source location
      , metaOrigin :: String  -- "implicit arg" etc.
      }

freshMetaWithOrigin :: Cxt -> VTy -> String -> Maybe SourceSpan -> IO Tm
freshMetaWithOrigin cxt ~a origin srcSpan = do
  m <- readIORef nextMeta
  writeIORef nextMeta $! (m + 1)
  let mty = eval [] $ closeTy (locals cxt) (quote (lvl cxt) a)
  let entry = Unsolved { metaTy = mty
                       , metaSource = srcSpan
                       , metaOrigin = origin
                       }
  modifyIORef' mcxt $ IM.insert m entry
  pure $! InsertedMeta (MetaVar m) (bds cxt)

-- Error reporting:
reportUnsolvedMetas :: IO ()
reportUnsolvedMetas = do
  ms <- readIORef mcxt
  forM_ (IM.toList ms) $ \(i, entry) ->
    case entry of
      Unsolved { metaSource = Just (file, start, end), metaOrigin = orig } ->
        putStrLn $ file ++ ":" ++ show start ++ ": " ++
                   "unsolved metavariable ?" ++ show i ++ "\n" ++
                   "  created as: " ++ orig
      _ -> pure ()
```

---

## 6. RedPRL/cooltt: Tactic-Based Provenance

### 6.1 Refiner Monad with Provenance

**Source:** `cooltt/src/lib/Elaborator/Refiner.ml` (simplified)

```ocaml
type 'a m = {
  run : refine_state -> ('a * refine_state, error) result
}

type refine_state = {
  meta_ctx : meta_ctx;
  goals : goal list;
  current_span : source_span option;
  elab_path : elab_step list;  (* Derivation path *)
}

type elab_step =
  | IntroLam of Name.t
  | ElimApp of source_span
  | CheckAgainst of source_span * tp
  | SynthFrom of source_span

type meta_entry = {
  id : meta_id;
  ty : tp;
  tm : tm option;  (* solution *)
  provenance : meta_provenance;
}

type meta_provenance = {
  created_at : source_span;
  created_by : elab_step;
  typing_ctx : tm_ctx;
}
```

**Creating metas with provenance:**
```ocaml
let fresh_meta ~ty : tm m =
  let* span = get_current_span in
  let* path = get_elab_path in
  let* ctx = get_typing_ctx in

  let provenance = {
    created_at = Option.get span;
    created_by = List.hd path;
    typing_ctx = ctx;
  } in

  let* id = fresh_meta_id ~ty ~provenance in
  return (Meta (id, []))

-- Error reporting unwinds elab_path:
let rec report_stuck_meta id =
  let entry = lookup_meta id in
  Printf.printf "error: unsolved metavariable ?%d\n" id;
  Printf.printf "  created at: %s\n" (show_span entry.provenance.created_at);
  Printf.printf "  elaboration trace:\n";
  unwind_elab_path entry.provenance.created_by

and unwind_elab_path = function
  | [] -> ()
  | IntroLam x :: rest ->
      Printf.printf "    - introducing lambda %s\n" (Name.to_string x);
      unwind_elab_path rest
  | CheckAgainst (span, tp) :: rest ->
      Printf.printf "    - checking against type %s at %s\n"
        (show_tp tp) (show_span span);
      unwind_elab_path rest
  | _ :: rest -> unwind_elab_path rest
```

---

## 7. Summary Table: Provenance by System

| System | Meta Provenance | Constraint Provenance | Error Quality | LSP Integration |
|--------|----------------|----------------------|---------------|-----------------|
| **Lean 4** | ✅ Full (lctx, depth, index, kind) | ✅ Full (origin, location) | ⭐⭐⭐⭐⭐ | ✅ Custom RPC (InfoTree) |
| **Agda** | ✅ Full (Closure Range, priority) | ✅ Full (Blocker, ProblemId) | ⭐⭐⭐⭐ | ⚠️ Basic |
| **GHC** | ✅ Full (CtOrigin, CtLoc) | ✅ Full (ObligationCause) | ⭐⭐⭐⭐ | ❌ No |
| **Idris 2** | ⚠️ Partial (FC only) | ⚠️ Partial (FC, retry flag) | ⭐⭐⭐ | ⚠️ Basic |
| **cooltt** | ✅ Full (meta_provenance, elab_path) | ⚠️ Partial | ⭐⭐⭐ | ❌ No |
| **elab-zoo** | ❌ None | ❌ None | ⭐ | ❌ No |
| **HWML (current)** | ❌ None | ❌ None | ⭐⭐ | ❌ No |

---

## 8. Action Plan for HWML

### Phase 1: Minimal Provenance (Week 1)

```rust
// Add to MetaEntry
pub struct MetaEntry<'db> {
    // ... existing fields ...
    pub created_at: Location<'db>,
    pub origin: String,  // Simple string for now
}

// Update fresh_meta calls
impl SolverState {
    pub fn fresh_meta(
        &mut self,
        ty: RcTy<'db>,
        arity: usize,
        kind: MetaKind,
        location: Location<'db>,
        origin: String,
    ) -> MetaId { ... }
}
```

### Phase 2: Typed Origins (Week 2)

```rust
pub enum MetaOrigin<'db> {
    ImplicitArgument(Location<'db>),
    TypeInference(Location<'db>),
    UnificationVariable(Location<'db>),
}
```

### Phase 3: Constraint Origins (Week 3)

```rust
pub struct ConstraintEntry<'db> {
    // ... existing ...
    pub created_at: Location<'db>,
    pub origin: ConstraintOrigin<'db>,
}
```

### Phase 4: Rich Diagnostics (Week 4)

Use `ariadne` for multi-span errors with full provenance context.

---

**END OF IMPLEMENTATION EXAMPLES**

