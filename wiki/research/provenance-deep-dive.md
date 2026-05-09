# Provenance Tracking for Constraints and Metavariables: State of the Art

**Date:** 2026-05-06  
**Author:** Research conducted for HWML elaborator architecture  
**Status:** Deep Research Dive

---

## Executive Summary

This document presents a comprehensive research survey of **provenance tracking** for constraints and metavariables in dependently typed elaborators with asynchronous constraint solvers. The goal is to inform HWML's elaborator architecture with state-of-the-art error reporting and diagnostic infrastructure.

### Key Findings

1. **Provenance is not debug info—it's error reporting infrastructure** that must ALWAYS be present
2. **Birth certificates for metavariables** track WHERE and WHY each meta was created
3. **Constraint origin tracking** enables blame assignment and flow-based error messages
4. **InfoTree architecture** (Lean 4) provides LSP-ready interactive diagnostics
5. **Zonking with provenance** allows error reporting even for solved constraints
6. **Blocking/wake-up mechanisms** require careful tracking of "stuck on" relationships

---

## 1. The Provenance Tracking Philosophy (RedPRL Lineage)

### 1.1 Core Insight: Elaboration as Derivation Tree Construction

Traditional compilers attach **static source spans** to AST nodes (like MLIR's `mlir::Location`). In dependent type theory with async metavariables, **this is insufficient**.

**Why?** When a constraint `?α ≡ Nat` fails, you need to know:
- WHERE was `?α` introduced?
- WHY was it created? (implicit arg? hole? unification variable?)
- WHAT constraints were added to it?
- WHICH constraint caused the failure?

### 1.2 The RedPRL Solution: Birth Certificates

**Source:** Jon Sterling's thesis, RedPRL/redtt/cooltt implementations

Every metavariable gets a **"birth certificate"** containing:
```ocaml
type meta_provenance = {
  created_at: source_span;
  typing_context: context;  (* Γ at creation time *)
  elab_rule: elaboration_rule;  (* which rule created it *)
  expected_type: type_expr;
}
```

When elaboration is **not a function but a trace construction**, you can:
- Unwind the provenance tree on failure
- Generate stack traces: "Failed to unify X with Y, which was required to solve ?M, which was created while checking [Term] has type [Type]"

### 1.3 Constraint Traces: Pushdown Blame Stack

Instead of `Eq(Term, Term)`, constraints become:
```ocaml
type constraint = Eq of {
  lhs: term;
  rhs: term;
  provenance: provenance_tree;
}
```

As constraints spawn sub-constraints (e.g., decomposing `A → B ≡ C → D`), **provenance accumulates** in a pushdown stack.

---

## 2. State-of-the-Art CLI Diagnostics

### 2.1 Multi-Span Blame (Rust/Elm Style)

**Tools:** `ariadne`, `miette`, `codespan-reporting`

**Key features:**
- Multiple highlighted spans in a single error
- Color-coded by role (expected, actual, origin)
- Intelligent truncation of large contexts

**Example (dependency type error):**
```
error: type mismatch in equality constraint
  ┌─ vector.hwml:12:5
  │
10│ def replicate {n : Nat} (x : A) : Vec A n :=
  │                 ─────── parameter 'x' has type A
11│   match n with
12│     | succ m => cons (x + 1) (replicate x)
  │                      ^^^^^ cannot add to polymorphic type A
  │
  = note: metavariable ?α created for implicit type argument
  = help: add type constraint: {A : Type} → Num A → ...
```

### 2.2 Rich Span Diagnostics (Rust's approach)

**Rust's `rustc_errors` design:**
```rust
pub struct Diagnostic {
    pub level: Level,  // Error, Warning, Note
    pub message: String,
    pub code: Option<DiagnosticId>,
    pub span: MultiSpan,
    pub children: Vec<SubDiagnostic>,
}

pub struct MultiSpan {
    primary_spans: Vec<Span>,
    span_labels: Vec<(Span, String)>,
}
```

**Key insight:** Errors are NOT thrown at the first failure point. They are **accumulated** and rendered with full context.

### 2.3 Text Representation of Contexts

For dependent types, `Γ` can be massive. Best practices:
- **Only print free variables** appearing in the failed terms
- Use **pretty-printing with holes**: `Γ = x : A, y : B, <15 other bindings>, z : C`
- Offer `--verbose` flag for full context

---

## 3. LSP Integration: The InfoTree Architecture

### 3.1 Lean 4's Approach (Masterclass in Theorem Prover UX)

**Standard LSP is insufficient** for dependent types. It only provides:
- `textDocument/hover` (stateless)
- `textDocument/signatureHelp` (stateless)

**Lean 4 extends LSP with:**
- Custom JSON-RPC endpoints: `$/lean/goalState`, `$/lean/infoView`
- **InfoTree**: Spatial mapping of source positions → elaboration state

```rust
// Lean's InfoTree (simplified)
enum InfoTree {
    Context(PartialContextInfo, Box<InfoTree>),
    Node(Info, Vec<InfoTree>),
    Hole(MVarId),  // Unsolved metavariable
}

struct Info {
    syntax: Syntax,
    expr: Option<Expr>,
    expected_type: Option<Type>,
    // ... metavariable context at this point
}
```

### 3.2 How InfoTree Enables Rich Interactivity

When the user hovers at position `42:10`:
1. LSP server queries InfoTree for that position
2. Returns **structured JSON** (not raw text):
   ```json
   {
     "hypotheses": [{"name": "n", "type": "Nat"}],
     "goal": "Vec A (n + 1)",
     "metavariables": [
       {"id": "?α", "type": "Type", "created_at": "line 10"}
     ]
   }
   ```
3. **Editor-agnostic**: VSCode, Neovim (via `lean.nvim`), Emacs all consume the same RPC

**Critical for terminal workflows:** Neovim renders InfoView in split panes using the same RPC.

### 3.3 Building InfoTree During Elaboration

```rust
// HWML adaptation
pub struct InfoTreeState<'db> {
    enabled: bool,
    assignments: HashMap<MVarId, InfoTree<'db>>,
    trees: Vec<InfoTree<'db>>,
}

impl<'db> Elaborator<'db> {
    fn with_info_context(&mut self, span: SourceRange, f: impl FnOnce()) {
        if !self.info_tree_enabled { return f(); }

        let ctx = self.capture_context();
        self.info_tree.push_context(ctx);
        f();
        let tree = self.info_tree.finalize_node();
        self.info_tree.add_child(tree);
    }
}
```

### 3.4 Lazy InfoTree Construction (Lean 4 optimization)

**Problem:** Building InfoTree eagerly is expensive.

**Solution:** Use `Task<InfoTree>` (lazy thunks):
```rust
pub struct InfoTreeState<'db> {
    assignment: HashMap<MVarId, InfoTree<'db>>,
    lazy_assignment: HashMap<MVarId, Task<InfoTree<'db>>>,
    // ...
}
```

Only force the thunk when the LSP queries that position.

---

## 4. Async Constraint Solvers: Blocking and Zombie Errors

### 4.1 The UX Nightmare: Suspended Constraints

**Scenario:**
1. Elaborator finishes file
2. Constraint `?α ≡ Nat` is suspended (waiting for `?α` to be solved)
3. `?α` never gets solved → **zombie constraint**

**Bad error:**
```
error: unsolved metavariable ?α
```

**Good error:**
```
error: constraint blocked on unsolved metavariable ?α
  ┌─ example.ml:5:10
  │
5 │   map (??) xs
  │       ^^ metavariable ?α created here (implicit type argument)
  │
  = note: constraint ?α ≡ Nat (from 'replicate' signature at line 8)
  = note: constraint stuck: cannot proceed without solving ?α
  = help: add explicit type annotation
```

### 4.2 Forced Wakeup on EOF

**Best practice (from Lean 4, Agda):**

```rust
pub fn finalize_elaboration(&mut self) -> Result<(), Vec<ElabError>> {
    // 1. Wake up ALL suspended constraints
    self.solver.wake_all_blocked();

    // 2. Zonk all terms (instantiate metavariables)
    let zonked = self.zonk_all();

    // 3. Report errors with full provenance
    if !self.solver.unsolved_constraints().is_empty() {
        return Err(self.diagnose_zombie_constraints());
    }

    Ok(())
}
```

### 4.3 The "Stuck On" Diagnostic

**Constraint blocking tracking:**
```rust
pub struct ConstraintEntry<'db> {
    pub id: ConstraintId,
    pub constraint: Constraint<'db>,
    pub status: ConstraintStatus,

    // ESSENTIAL:
    pub created_at: Location<'db>,
    pub blocked_on: Vec<MetaId>,  // Which metas must be solved first
}

impl Solver {
    fn diagnose_stuck(&self, cid: ConstraintId) -> ElabError {
        let entry = self.constraints[cid];
        ElabError::ConstraintStuck {
            constraint_id: cid,
            location: entry.created_at,
            blocked_on: entry.blocked_on.iter()
                .map(|m| self.meta_info(*m))
                .collect(),
        }
    }
}
```

---

## 5. Metavariable Provenance: Implementation Details

### 5.1 What to Track (Minimal Set)

Every `MetaEntry` must include:

```rust
pub struct MetaEntry<'db> {
    pub id: MetaId,
    pub ty: RcTy<'db>,
    pub arity: usize,
    pub solution: Option<MetaSolution<'db>>,
    pub kind: MetaKind,

    // ===== ESSENTIAL FOR ERROR REPORTING =====
    pub created_at: Location<'db>,
    pub created_by: MetaOrigin<'db>,
    pub constrained_by: Vec<ConstraintId>,
}

pub enum MetaOrigin<'db> {
    ImplicitArgument {
        function_loc: Location<'db>,
        param_index: usize,
        param_name: String,
    },
    TypeInference {
        expression_loc: Location<'db>,
        reason: String,  // "cannot infer type for underscore"
    },
    UniverseLevel {
        type_annotation_loc: Location<'db>,
    },
    UnificationVariable {
        equation_loc: Location<'db>,
    },
    PatternSynthesis {
        pattern_loc: Location<'db>,
        constructor: String,
    },
}
```

**Memory overhead:** Approximately 40-80 bytes per metavariable. For a file with 1000 metas, this is ~80 KB—negligible.

### 5.2 Constraint Provenance

```rust
pub struct ConstraintEntry<'db> {
    pub id: ConstraintId,
    pub constraint: Constraint<'db>,
    pub status: ConstraintStatus,

    // ===== ESSENTIAL FOR ERROR REPORTING =====
    pub created_at: Location<'db>,
    pub origin: ConstraintOrigin<'db>,
}

pub enum ConstraintOrigin<'db> {
    FunctionApplication {
        function_loc: Location<'db>,
        argument_loc: Location<'db>,
    },
    TypeAnnotation {
        term_loc: Location<'db>,
        annotation_loc: Location<'db>,
    },
    PatternMatching {
        scrutinee_loc: Location<'db>,
        pattern_loc: Location<'db>,
        branch_index: usize,
    },
    UnificationDecomposition {
        parent_constraint: ConstraintId,
        decomposition_rule: &'static str,  // "Pi injectivity", "pair congruence"
    },
    // ... 10+ more variants
}
```

### 5.3 Example: Agda's Struggle (Issue #2073)

**Problem reported:**
```
error: Cannot instantiate _252 with term xs because xs is not in scope
```

**What users NEED to know:**
- `_252` was created as an implicit argument to `map`
- It couldn't be unified because `xs` was pruned from its scope
- The actual fix: add explicit type annotation

**Agda Issue #2073 conclusion:**
> "We need to keep track of:
> - Why the metavariable was introduced (implicit arg? postponed constraint?)
> - Source location of the function (if implicit arg)
> - Whether arguments were pruned or never in scope
> - Reason for pruning"

This is **exactly** what `MetaOrigin` provides.

---

## 6. Zonking with Provenance

### 6.1 The Challenge

**Zonking** = replacing metavariables with their solutions (GHC term).

**Problem:** After zonking, the metavariable is gone. How do you report errors about *why* a solution was wrong?

### 6.2 Solution: Zonk-Time Error Reporting

```rust
pub fn zonk_term(&self, tm: RcSyntax<'db>) -> Result<RcSyntax<'db>, ElabError<'db>> {
    match tm.as_ref() {
        Syntax::Meta(meta_id) => {
            let entry = self.state.meta_entry(*meta_id);

            match &entry.solution {
                Some(sol) => {
                    // Recursively zonk the solution
                    self.zonk_term(sol.syntax.clone())
                }
                None => {
                    // UNSOLVED META: Rich error with provenance
                    Err(ElabError::UnsolvedMeta {
                        meta: *meta_id,
                        created_at: entry.created_at.clone(),
                        origin: entry.created_by.clone(),
                        constraints: entry.constrained_by.iter()
                            .map(|cid| self.constraint_info(*cid))
                            .collect(),
                    })
                }
            }
        }
        // ... other cases
    }
}
```

### 6.3 GHC's Approach

GHC has **three zonking modes**:

1. **`ZonkM`** (within typechecker): Fast, preserves metavars
2. **`ZonkTcM`** (final zonk to `Type`): Strict, reports unsolved metas
3. **`ZonkEnv`**: Tracks variable renaming (skolemization)

**Key insight:** Zonking is NOT just substitution—it's **error reporting with context**.

---

## 7. Pattern Unification and Delayed Constraints

### 7.1 The Pattern Fragment

**Pattern unification** (Miller 1991) is decidable when metavariables appear only in patterns:
```
?M x y z = t    where x, y, z are distinct bound variables
```

**Outside the pattern fragment:**
```
?M (f x) (f x) = t    ← NOT a pattern (duplicate occurrences)
```

### 7.2 Dynamic Pattern Unification (Gundry, Pientka)

**Key innovation:** Don't fail immediately. **Postpone** constraints outside the pattern fragment.

**Why?** Solving other constraints might bring them back into the pattern fragment.

**Example:**
```
Constraint 1: ?M (f x) = Nat        [postponed - not a pattern]
Constraint 2: ?α ≡ Nat              [solved immediately]
Constraint 3: ?M y ≡ ?α             [solved: ?M := λy. Nat]
```

Now re-try Constraint 1:
```
Nat = Nat    [✓ solved!]
```

### 7.3 Blocking Metadata

```rust
pub struct ConstraintEntry<'db> {
    // ...
    pub blocking_reason: Option<BlockingReason<'db>>,
}

pub enum BlockingReason<'db> {
    NotPatternFragment {
        meta: MetaId,
        problematic_args: Vec<usize>,
    },
    WaitingForTypeInfo {
        metas: Vec<MetaId>,
    },
    RecursiveOccurrence {
        meta: MetaId,
        occurs_in: RcValue<'db>,
    },
}
```

This allows **precise error messages:**
```
error: cannot solve constraint (postponed)
  = note: blocked on ?M because arguments are not in pattern fragment
  = note: problematic argument positions: [0, 2]
  = help: this may resolve when ?M is solved by other constraints
```

---

## 8. Implementing Provenance in HWML

### 8.1 Current State Analysis

**Current `MetaEntry`:**
```rust
pub struct MetaEntry<'db> {
    pub id: MetaId,
    pub ty: RcTy<'db>,
    pub arity: usize,
    pub solution: Option<MetaSolution<'db>>,
    pub kind: MetaKind,
}
```

**Missing:**
- ❌ `created_at: Location<'db>`
- ❌ `created_by: MetaOrigin<'db>`
- ❌ `constrained_by: Vec<ConstraintId>`

**Current `ConstraintEntry`:**
```rust
pub struct ConstraintEntry<'db> {
    pub id: ConstraintId,
    pub constraint: Constraint<'db>,
    pub status: ConstraintStatus,
}
```

**Missing:**
- ❌ `created_at: Location<'db>`
- ❌ `origin: ConstraintOrigin<'db>`
- ❌ `blocking_reason: Option<BlockingReason<'db>>`

### 8.2 Implementation Roadmap

**Phase 1: Extend MetaEntry (1 week)**

1. Add provenance fields to `MetaEntry`
2. Update `fresh_meta()` signature:
   ```rust
   pub fn fresh_meta(
       &mut self,
       ty: RcTy<'db>,
       arity: usize,
       kind: MetaKind,
       created_at: Location<'db>,
       created_by: MetaOrigin<'db>,
   ) -> MetaId
   ```
3. Update all `fresh_meta()` call sites (30-40 locations)

**Phase 2: Extend ConstraintEntry (1 week)**

1. Add provenance fields to `ConstraintEntry`
2. Update `emit_eq()`, `emit_level_leq()`, etc.
3. Track blocking reasons in solver

**Phase 3: Rich Error Reporting (2 weeks)**

1. Implement `ElabError` variants with full context
2. Create `diagnostics.rs` module with multi-span rendering
3. Integrate with `ariadne` or `miette`

**Phase 4: LSP InfoTree (2 weeks)**

1. Add `InfoTreeState` to elaborator
2. Capture context at each `with_info_context` call
3. Implement custom RPC endpoints for goal state

### 8.3 Minimal Viable Provenance (MVP)

Start with the absolute essentials:

```rust
// MVP: Minimal provenance
pub struct MetaEntry<'db> {
    // ... existing fields ...
    pub created_at: Location<'db>,
    pub created_by: MetaOriginMVP,
}

pub enum MetaOriginMVP {
    ImplicitArgument(Location<'db>),
    TypeInference(Location<'db>),
    Other(Location<'db>),
}
```

This alone enables much better error messages:
```
error: unsolved metavariable ?42
  ┌─ adder.hwml:5:10
  │
5 │   xor a b
  │       ^ metavariable ?42 created here (implicit type argument)
```

---

## 9. Case Studies from Production Systems

### 9.0 RedPRL Family: Provenance Through Architecture

**See full research**: [`redprl-provenance.md`](./redprl-provenance.md)

The RedPRL family (RedPRL, redtt, cooltt) demonstrates that provenance can be **architectural** rather than bolted-on. Their "Dependent LCF" framework uses **telescopes of judgments**:

```
Telescope (ordered list):
  0: Γ ⊢ ?x : Nat                    [origin: user hole in expression]
  1: Γ, x:Nat ⊢ ?p : IsEven(?x)      [origin: Pi-intro rule, depends on ?x]
  2: Γ, x:Nat ⊢ ?q : P(?x)           [origin: application, depends on ?x]
```

**Provenance captured implicitly**:
- **WHERE**: Position in telescope = creation order
- **WHY**: The judgment form itself (e.g., "Γ ⊢ ?x : Nat" from user hole)
- **WHICH**: Dependencies explicit (later judgments reference earlier metavars)

**Error message example**:
```
Unsolved metavariable ?p
  Created by: Pi introduction rule
  Position in telescope: 1
  Goal: IsEven(?x)
  Depends on: ?x (position 0, also unsolved)
  Suggestion: Solve ?x first
```

**Key innovation**: redtt pioneered "boundary-sensitive holes" where holes in path types track their boundary conditions, providing even finer-grained provenance.

**Lesson for HWML**: Consider ordered storage (not HashMap) and richer "goal" information (not just type) for each metavar.

---

### 9.1 Lean 4: InfoTree Lifecycle

**Elaboration:**
```lean
def elaborate_application : TermElabM Unit := do
  -- Create info tree node
  withInfoContext (← getRef) do
    -- Elaborate function
    let f ← elabTerm funStx none
    -- Elaborate argument
    let arg ← elabTerm argStx expectedArgTy
    -- Unify types
    let u ← isDefEq fTy (← mkArrow argTy resTy)
    -- Result
    return mkApp f arg
```

**InfoTree created:**
```
Node(ApplicationInfo) {
  children: [
    Node(TermInfo funStx, fTy),
    Node(TermInfo argStx, argTy),
    Hole(?u)  // If unification postponed
  ]
}
```

**LSP Query:**
```typescript
// User hovers at funStx position
const response = await leanClient.request('$/lean/plainGoal', {
  textDocument: { uri: 'file:///example.lean' },
  position: { line: 5, character: 10 }
});

// Response:
{
  goals: ["n : Nat ⊢ Vec A (n + 1)"],
  metavariables: [
    { id: "?u", type: "Nat ≡ Nat", status: "postponed" }
  ]
}
```

### 9.2 Agda: Constraint Dependency Graph

Agda tracks **constraint dependencies** to avoid redundant work:

```haskell
data Constraint = Constraint {
  cid :: ConstraintId,
  constraint :: Closure Constraint,
  blockedOn :: Set MetaId,
  blockers :: Blocker,  -- Refined blocking info
  origin :: ConstraintOrigin
}

-- Wake up constraints when meta solved
solveMeta :: MetaId -> Term -> TCM ()
solveMeta m v = do
  updateMetaVar m v
  -- Wake up all constraints blocked on m
  wakeConstraints (blockedOn == {m})
```

**Blocker** (Agda 2.6.3+):
```haskell
data Blocker
  = UnblockOnMeta MetaId
  | UnblockOnDef QName
  | UnblockOnAll [Blocker]
  | UnblockOnAny [Blocker]
```

Allows fine-grained "stuck on" messages:
```
error: constraint stuck
  blocked on: all of {?α, ?β}
  will retry when both are solved
```

### 9.3 Idris 2: Core.Unify.solveConstraints

**Implementation** (`src/Core/Unify.hs`):

```haskell
solveConstraints :: Core ()
solveConstraints = do
  ust <- getUnifyState
  progress <- solveAll (constraints ust)
  when progress $
    solveConstraints  -- Loop until fixpoint

solveAll :: [Int] -> Core Bool
solveAll [] = pure False
solveAll (cid:cs) = do
  constraint <- lookupConstraint cid
  case constraint of
    Resolved -> solveAll cs  -- Skip solved
    Stuck ms -> solveAll cs  -- Skip blocked
    Constraint tm1 tm2 env -> do
      catch (do
        unify env tm1 tm2
        pure True)  -- Made progress
        (\err -> solveAll cs)  -- Try next
```

**Key insight:** Constraints revisited **multiple times** until fixpoint. Provenance essential for debugging infinite loops.

---

## 10. Advanced Topics

### 10.1 Non-Chronological Backtracking (Lean 3/4)

**Problem:** First-in-first-out (FIFO) constraint solving can fail when a later constraint should be solved first.

**Solution:** Attach **priorities** to constraints:
```rust
pub struct ConstraintEntry<'db> {
    // ...
    pub priority: ConstraintPriority,
}

pub enum ConstraintPriority {
    Pattern = 0,        // Highest priority (decidable)
    Ready = 1,          // All metas instantiated
    Regular = 2,        // Standard unification
    QuasiPattern = 3,   // Almost patterns
    FlexRigid = 4,      // Flex-rigid pairs
    FlexFlex = 5,       // Lowest (underconstrained)
}
```

**Solver becomes:**
```rust
pub fn solve_all(&mut self) -> Result<(), SolveError> {
    loop {
        // Sort active queue by priority
        self.active_queue.sort_by_key(|cid| self.priority(*cid));

        let Some(cid) = self.pop_active() else { break };
        match self.step(cid) {
            Ok(progress) if progress => continue,
            Ok(_) => {} // No progress, try next
            Err(e) => return Err(e),
        }
    }
}
```

### 10.2 Anti-Unification Variables (Sterling)

**Unique to Sterling's work (RedPRL/redtt/cooltt):**

Every equality constraint returns a **witness metavariable**:
```ocaml
constrainEquality : term -> term -> type -> MetaVarId
```

**Why?** For **well-typedness preservation**:
```
If Γ ⊢ a : A and Γ ⊢ b : A and we assert a ≡ b,
then we get a witness ?w : a ≡ b
```

This witness can be **used in extended contexts**:
```
Γ, x : Nat, p : (x ≡ 5) ⊢ ... use 'p' in type ...
```

**HWML equivalent:**
```rust
pub enum Constraint<'db> {
    Eq {
        lhs: RcValue<'db>,
        rhs: RcValue<'db>,
        ty: RcTy<'db>,
        witness: MetaId,  // ← Anti-unification variable
        depth: usize,
    },
}
```

When `lhs ≡ rhs` succeeds, solve `witness := common_value`.

### 10.3 Elaborator Reflection (Idris 1/2)

**Idris allows users to write custom elaborators:**

```idris
%runElab
myTactic : Elab ()
myTactic = do
  -- Inspect current goal
  goal <- getGoal
  -- Create fresh metavariable
  m <- metavar goal
  -- Fill hole
  fill (Var m)
  solve
```

**Provenance challenge:** User-written tactics can create metas. **Must track that origin**:
```rust
pub enum MetaOrigin<'db> {
    // ...
    UserTactic {
        tactic_name: String,
        invocation_loc: Location<'db>,
    },
}
```

---

## 11. Error Reporting Best Practices Summary

### 11.1 Don't Do This ❌

**Bad error (current HWML):**
```rust
ElabError::UnsolvedMeta {
    meta: MetaId(42),
    span: None,
}

// Renders as:
// error: unsolved metavariable ?42
```

**Why bad:**
- No location
- No explanation of WHY the meta exists
- No actionable advice

### 11.2 Do This Instead ✅

**Good error:**
```rust
ElabError::UnsolvedMeta {
    meta: MetaId(42),
    created_at: Location::file_range(..., 5, 10, 5, 12),
    origin: MetaOrigin::ImplicitArgument {
        function_loc: Location::file_range(..., 5, 5, 5, 8),
        param_index: 1,
        param_name: "n".to_string(),
    },
    constraints: vec![
        ConstraintInfo {
            id: ConstraintId(10),
            kind: "Eq(?42, Nat)",
            created_at: Location::file_range(..., 6, 3, 6, 10),
        },
    ],
}

// Renders as:
// error: unsolved metavariable ?42
//   ┌─ adder.hwml:5:10
//   │
// 5 │   xor a b
//   │       ^ metavariable ?42 created here
//   │         (implicit type argument for 'xor')
//   │
//   = note: constrained by:
//   = note:   constraint #10: ?42 ≡ Nat (at line 6)
//   = help: add explicit type annotation
```

### 11.3 Flow-Based Errors (Advanced)

**Instead of:**
```
error: type mismatch
  expected: Nat
  got: Bool
```

**Show data flow:**
```
error: Bool flows into Nat context
  ┌─ example.hwml:3:5
  │
1 │ def half_adder (a : Bit) : ... :=
  │                     ─── parameter 'a' has type Bit
2 │   let sum := xor a b in
  │              ─── function 'xor' expects Nat
3 │   (sum, carry)
  │    ^^^ Bool flows to Nat context
  │
  = help: the flow path is: a (Bit) → xor (expects Nat)
```

Users understand **flow** better than abstract type constraints.

---

## 12. Recommendations for HWML

### 12.1 Immediate Actions (Week 1)

1. **Extend `MetaEntry`:**
   ```rust
   pub struct MetaEntry<'db> {
       // ... existing ...
       pub created_at: Location<'db>,
       pub created_by: MetaOriginMVP,
   }

   pub enum MetaOriginMVP {
       ImplicitArgument(Location<'db>),
       TypeInference(Location<'db>),
       Other(String),  // Catch-all for now
   }
   ```

2. **Update `fresh_meta()` calls** (annotate with creation site)

3. **Enhance error messages:**
   ```rust
   impl Display for ElabError {
       fn fmt(&self, f: &mut Formatter) -> fmt::Result {
           match self {
               ElabError::UnsolvedMeta { meta, .. } => {
                   let entry = /* get from context */;
                   write!(f, "error: unsolved metavariable ?{}\n  created at: {}\n  reason: {:?}",
                       meta.0, entry.created_at, entry.created_by)
               }
               // ...
           }
       }
   }
   ```

### 12.2 Medium-Term (Month 1)

1. **Add `ConstraintEntry` provenance:**
   ```rust
   pub struct ConstraintEntry<'db> {
       // ... existing ...
       pub created_at: Location<'db>,
       pub origin: ConstraintOrigin<'db>,
   }
   ```

2. **Implement multi-span diagnostics** using `ariadne`

3. **Track constraint dependencies** (wake-up graph)

### 12.3 Long-Term (Months 2-3)

1. **Implement InfoTree** for LSP integration

2. **Add custom RPC endpoints:**
   - `$/hwml/goalState`
   - `$/hwml/metaInfo`
   - `$/hwml/constraintInfo`

3. **Build interactive debugger** for elaboration traces

---

## 13. References

### Academic Papers

1. **Miller (1991):** "A Logic Programming Language with Lambda-Abstraction, Function Variables, and Simple Unification" (original pattern unification)

2. **Gundry (2013):** "Type Inference, Haskell and Dependent Types" (dynamic pattern unification, PhD thesis)

3. **Pientka & Dunfield (2010):** "Beluga: A Framework for Programming and Reasoning with Deductive Systems" (contextual metavariables)

4. **Sterling & Harper (2018):** "Algebraic Foundations of Proof Refinement" (dependent LCF, provenance as derivation)

5. **Zhang & Myers (2014):** "Toward General Diagnosis of Static Errors" (constraint graph diagnosis, SHErrLoc)

6. **Vytiniotis et al. (2011):** "OutsideIn(X): Modular Type Inference with Local Assumptions" (Haskell's constraint solver)

### Implementation Artifacts

- **Lean 4:** `src/Lean/Elab/InfoTree/`, `src/Lean/MetavarContext.lean`
- **Agda:** `src/full/Agda/TypeChecking/MetaVars.hs`, `src/full/Agda/TypeChecking/Constraints.hs`
- **Idris 2:** `src/Core/Unify.idr`, `src/TTImp/Elab/Check.idr`
- **RedPRL/cooltt:** `src/lib/Core/Refine.ml`, `src/lib/Core/Evaluation.ml`
- **GHC:** `compiler/GHC/Tc/Zonk/`, `compiler/GHC/Tc/Solver/`

### Tools

- **ariadne** (Rust): https://docs.rs/ariadne/
- **miette** (Rust): https://docs.rs/miette/
- **codespan-reporting** (Rust): https://docs.rs/codespan-reporting/

---

## 14. Glossary

- **Birth Certificate:** Metadata attached to a metavariable recording its creation context
- **Blocking/Stuck:** A constraint cannot proceed until certain metavariables are solved
- **Contextual Metavariable:** A metavariable that closes over its typing context (Abel-Pientka)
- **InfoTree:** Spatial mapping from source positions to elaboration state (Lean 4)
- **Pattern Fragment:** Subset of higher-order unification that is decidable (Miller)
- **Provenance:** The origin and history of a metavariable or constraint
- **Pruning:** Removing variables from a metavariable's scope during unification
- **Wake-up:** Re-attempting a blocked constraint after a metavariable is solved
- **Zombie Constraint:** A suspended constraint that never gets solved
- **Zonking:** Replacing metavariables with their solutions (GHC term)

---

## Appendix A: HWML Current State Gaps

### What HWML Has ✅

- Metavariable entries with `id`, `ty`, `arity`, `solution`, `kind`
- Constraint entries with `id`, `constraint`, `status`
- Blocking mechanism (`ConstraintStatus::Blocked(Vec<MetaId>)`)
- Wake-up graph (`wake_on: HashMap<MetaId, Vec<ConstraintId>>`)
- Solver loop with progress tracking

### What HWML Lacks ❌

- ❌ Metavariable provenance (`created_at`, `created_by`)
- ❌ Constraint provenance (`created_at`, `origin`)
- ❌ Blocking reason tracking (`why` is it blocked?)
- ❌ Multi-span error rendering
- ❌ LSP custom RPC endpoints
- ❌ InfoTree for interactive queries

### Impact on User Experience

**Current error:**
```
error: unsolved metavariable ?42
```

**What it should be:**
```
error: unsolved metavariable ?42
  ┌─ Counter.hwml:15:10
  │
15│   increment state
  │             ^^^^^ metavariable ?42 created here
  │                   (implicit type argument for 'increment')
  │
  = note: constrained by:
  = note:   constraint #23: ?42 ≡ Nat (from 'increment' signature at line 8)
  = note:   constraint #25: ?42 ≡ BitVec 8 (from 'state' type at line 12)
  = error: conflict: Nat ≠ BitVec 8
```

---

## Appendix B: Example Implementation (Minimal)

```rust
// crates/hwml-elab/src/meta.rs

#[derive(Clone, Debug)]
pub struct MetaEntry<'db> {
    pub id: MetaId,
    pub ty: RcTy<'db>,
    pub arity: usize,
    pub solution: Option<MetaSolution<'db>>,
    pub kind: MetaKind,

    // NEW: Provenance
    pub created_at: Location<'db>,
    pub created_by: MetaOrigin<'db>,
}

#[derive(Clone, Debug)]
pub enum MetaOrigin<'db> {
    ImplicitArgument {
        function_loc: Location<'db>,
        param_name: String,
    },
    TypeInference {
        expression_loc: Location<'db>,
    },
    UnificationVariable {
        constraint_loc: Location<'db>,
    },
    Other(String),
}

// crates/hwml-elab/src/state.rs

impl<'db> SolverState<'db> {
    pub fn fresh_meta(
        &mut self,
        ty: RcTy<'db>,
        arity: usize,
        kind: MetaKind,
        created_at: Location<'db>,
        created_by: MetaOrigin<'db>,
    ) -> MetaId {
        let id = MetaId(self.next_meta);
        self.next_meta += 1;
        let entry = MetaEntry {
            id,
            ty,
            arity,
            solution: None,
            kind,
            created_at,
            created_by,
        };
        self.metas.insert(id, entry);
        id
    }
}

// crates/hwml-elab/src/error.rs

impl<'db> Display for ElabError<'db> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            ElabError::UnsolvedMeta { meta, created_at, origin, constraints } => {
                writeln!(f, "error: unsolved metavariable ?{}", meta.0)?;
                writeln!(f, "  created at: {}", created_at)?;
                match origin {
                    MetaOrigin::ImplicitArgument { function_loc, param_name } => {
                        writeln!(f, "  reason: implicit argument '{}' for function at {}",
                            param_name, function_loc)?;
                    }
                    MetaOrigin::TypeInference { expression_loc } => {
                        writeln!(f, "  reason: type inference for expression at {}",
                            expression_loc)?;
                    }
                    // ...
                }
                if !constraints.is_empty() {
                    writeln!(f, "  constrained by:")?;
                    for c in constraints {
                        writeln!(f, "    - {} (at {})", c.kind, c.created_at)?;
                    }
                }
                Ok(())
            }
            // ... other variants
        }
    }
}
```

---

**END OF RESEARCH REPORT**

