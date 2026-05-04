# ADR-010: Metavariable Scoping and Constraint Solver Integration

**Status:** Approved  
**Date:** 2026-05-03  
**Deciders:** Core team  
**Related:** [[ADR-007-salsa-driven-compilation]], [[ADR-001-lcf-kernel]], [[research/modern-incremental-compilation]]

---

## Context

HWML uses dependent type elaboration with metavariables (type holes) and constraint solving. This creates a fundamental tension with Salsa's demand-driven architecture:

**Salsa requires:**
- Pure, stateless functions (`Input → Output`)
- Deterministic execution (same inputs → same outputs)
- Cacheable results

**Dependent type elaboration requires:**
- Stateful metavariable context (mutable, grows during elaboration)
- Constraint worklist (emits constraints like `?X == Int`, solves iteratively)
- "Asynchronous" constraint resolution (constraints may be blocked until other AST branches solve metavariables)

**The problem:** If we naively try to make constraint solving into Salsa queries, the compiler fails:
- **Cycle panics:** Constraint A depends on constraint B depends on constraint A → Salsa detects false cycle
- **Cache defeats:** Every metavariable unification mutates global state → Salsa cache invalidated constantly
- **Non-determinism:** Constraint solver ordering varies → different outputs from same inputs → Buck2 caching breaks

**The question:** How do we bridge a constraint-based elaborator with Salsa's demand-driven query system?

---

## Decision

**The Golden Rule: Metavariables Never Escape Salsa Queries**

We adopt a **three-level architecture** where metavariables and constraint solving are strictly local to individual Salsa query executions:

### Level 1: Cross-Library Dependencies (Salsa-Driven)

```rust
#[salsa::tracked]
pub fn library_interface(db: &dyn Db, root: WorkspaceRoot, lib_name: String) 
    -> Result<Hwmli, ElabError> 
{
    // ✅ Pure, cacheable, cross-library dependency handling
    for dep in &manifest.dependencies {
        library_interface(db, root, dep.name.clone())?;
    }
    
    let files = library_source_files(db, root, lib_name.clone());
    
    // ⚠️ Enter constraint solver world (but still a Salsa query)
    elaborate_library_with_local_solver(db, root, lib_name, files)
}
```

**Salsa handles:** Library-level dependencies, caching, incremental recompilation

### Level 2: Within-Library Elaboration (Local Solver)

```rust
#[salsa::tracked]
pub fn elaborate_library_with_local_solver(
    db: &dyn Db,
    root: WorkspaceRoot,
    lib_name: String,
    files: Vec<FileId>
) -> Result<Hwmli, ElabError> 
{
    // Compute SCCs for mutual recursion within library
    let sccs = compute_declaration_sccs(db, files)?;
    
    let mut elaborated_decls = HashMap::new();
    
    // Process each SCC in topological order
    for scc in sccs.topo_order() {
        // 🔥 CRITICAL: Fresh ElabState per SCC
        let result = elaborate_scc_with_local_state(db, root, lib_name.clone(), scc)?;
        elaborated_decls.extend(result);
    }
    
    // ✅ Return pure, metavariable-free declarations
    Ok(Hwmli {
        version: 1,
        library_name: lib_name,
        declarations: elaborated_decls.into_values().collect(),
    })
}
```

**This query handles:** SCC discovery, topological ordering within library, aggregating results

### Level 3: SCC Elaboration (The "Async" Solver)

```rust
/// NOT a Salsa query! Regular function with interior mutability.
/// Metavariables are born, live, and die within this function.
fn elaborate_scc_with_local_state(
    db: &dyn Db,
    root: WorkspaceRoot,
    lib_name: String,
    scc: Scc
) -> Result<HashMap<DeclId, Declaration>, ElabError> 
{
    // === Local State (lives only for this SCC) ===
    let mut elab_state = ElabState {
        metas: MetavariableContext::new(),
        worklist: Vec::new(),
    };
    
    // === PHASE 1: Elaborate Signatures ===
    let mut signatures = HashMap::new();
    
    for decl_id in &scc.members {
        let surface_sig = get_surface_signature(db, decl_id)?;
        
        // Generate metavariables, emit constraints
        let (core_sig, constraints) = elaborate_signature(&mut elab_state, surface_sig)?;
        elab_state.worklist.extend(constraints);
        signatures.insert(decl_id, core_sig);
    }
    
    // Solve signature constraints to fixpoint
    solve_constraints_to_fixpoint(&mut elab_state)?;
    
    // Replace metavars with solutions (zonking)
    let zonked_sigs = zonk_signatures(&elab_state, signatures)?;
    
    // === PHASE 2: Elaborate Bodies ===
    elab_state.clear_for_bodies();
    
    let mut bodies = HashMap::new();
    
    for decl_id in &scc.members {
        let surface_body = get_surface_body(db, decl_id)?;
        let expected_ty = &zonked_sigs[decl_id];
        
        // Elaborate body against known signature
        let (core_body, constraints) = elaborate_term(
            &mut elab_state, 
            surface_body, 
            expected_ty
        )?;
        elab_state.worklist.extend(constraints);
        bodies.insert(decl_id, core_body);
    }
    
    // === THE "ASYNC" SOLVER LOOP ===
    solve_constraints_to_fixpoint(&mut elab_state)?;
    
    // === ZONKING ===
    let zonked_bodies = zonk_terms(&elab_state, bodies)?;
    
    // === LCF KERNEL VERIFICATION ===
    for (decl_id, (sig, body)) in zonked_sigs.iter().zip(&zonked_bodies) {
        kernel::verify_declaration(db, body, sig)?;
    }
    
    // === RETURN TO SALSA ===
    // ElabState destroyed here. Salsa only sees pure CoreTerms.
    Ok(zonked_sigs.into_iter()
        .zip(zonked_bodies.into_iter())
        .map(|((id, sig), (_, body))| (id, Declaration { sig, body }))
        .collect())
}
```

**This function handles:** All metavariable/constraint complexity, isolated from Salsa

---

## The Worklist Solver (The "Async" Engine)

The term "asynchronous" does NOT mean Rust `async/await`. It means constraints can be **blocked** waiting for other constraints to solve first.

```rust
struct ElabState {
    /// Maps MetaId → Unsolved | Solved(CoreTerm)
    metas: MetavariableContext,
    /// Constraints waiting to be solved
    worklist: Vec<Constraint>,
}

fn solve_constraints_to_fixpoint(state: &mut ElabState) -> Result<(), ElabError> {
    const MAX_ITERATIONS: usize = 1000;
    
    for _iteration in 0..MAX_ITERATIONS {
        let mut progressed = false;
        let mut stalled = Vec::new();
        
        for constraint in state.worklist.drain(..) {
            match try_solve_constraint(constraint, &mut state.metas) {
                SolveResult::Solved => { 
                    progressed = true; 
                }
                SolveResult::Stalled(c) => { 
                    // Blocked on unsolved metavar, try again next iteration
                    stalled.push(c); 
                }
                SolveResult::Error(e) => { 
                    return Err(e); 
                }
            }
        }
        
        state.worklist = stalled;
        
        if !progressed {
            if state.worklist.is_empty() {
                return Ok(()); // All constraints solved!
            } else {
                // Apply defaulting rules or error
                return apply_defaulting_or_error(state);
            }
        }
    }
    
    Err(ElabError::SolverLoopExceededIterations)
}
```

**Key properties:**
- **Local iteration:** Loop runs entirely within one function call
- **Progress tracking:** If no constraint makes progress in an iteration, we're done (or stuck)
- **Stalled constraints:** Blocked constraints re-enter worklist for next iteration
- **Determinism:** Same input constraints → same solving order → same output (critical for caching)

---

## Rationale

### 1. Perfect Caching (The Core Benefit)

**Without this architecture:**
```rust
// ❌ BAD: Global metavariable state
static GLOBAL_METAS: Mutex<MetaContext> = ...;

#[salsa::tracked]
fn elaborate_term(db: &dyn Db, term: SurfaceTerm) -> CoreTerm {
    let meta = GLOBAL_METAS.lock().fresh_meta();
    // ... elaboration ...
    // Salsa cache defeated! Output depends on global state.
}
```

**With this architecture:**
```rust
// ✅ GOOD: Local metavariable state
#[salsa::tracked]
fn elaborate_library(...) -> Result<Hwmli> {
    let mut elab_state = ElabState::new(); // Fresh state

    for scc in sccs {
        elaborate_scc(&mut elab_state, scc)?;
    }

    let zonked = zonk(&elab_state); // Pure output
    // ElabState destroyed
    return Ok(zonked);
}
```

**Salsa caches:**
- **Input:** Surface AST (pure, immutable)
- **Output:** Zonked CoreTerms (pure, metavariable-free)
- **NOT cached:** `ElabState` (ephemeral, destroyed after query)

**Result:** Change one file in library → Salsa re-runs `elaborate_library` for that library only. The solver loop runs fresh, produces deterministic output, Salsa caches it.

### 2. Deterministic Output (Required for Buck2)

Buck2's remote execution requires bit-identical outputs from identical inputs. Non-determinism breaks caching.

**Sources of non-determinism in constraint solvers:**
- **Constraint processing order:** HashSet iteration order varies
- **Metavariable ID assignment:** Global counter varies across runs
- **Solver heuristics:** "Try unification first" vs "Try defaulting first"

**Our solution:**
- **Fixed processing order:** `Vec<Constraint>` processed sequentially
- **Fresh state per SCC:** MetaId starts at 0 for each SCC
- **Deterministic heuristics:** Same input → same heuristic choices

**Verification:** The LCF kernel sits at the boundary. If the elaborator's solver produces a proof of the wrong thing due to non-determinism, the kernel catches it.

### 3. No Cycle Panics (Salsa Safety)

Salsa panics if Query A calls Query B which calls Query A. This is the right behavior for cross-library dependencies (actual cycles in the build graph).

But constraint solving has "apparent cycles" that aren't real:
```
Constraint 1: Unify(?X, Int → ?Y)
Constraint 2: Unify(?Y, Bool)
Constraint 1 (retry): Now ?Y = Bool, so ?X = Int → Bool
```

**If these were Salsa queries:**
```rust
#[salsa::tracked]
fn solve_constraint_1(db: &dyn Db) -> CoreTy {
    let y = solve_constraint_2(db); // Query call
    CoreTy::Arrow(Int, y)
}

#[salsa::tracked]
fn solve_constraint_2(db: &dyn Db) -> CoreTy {
    let x = solve_constraint_1(db); // 💥 CYCLE PANIC
    // ...
}
```

**With worklist solver:**
```rust
// NOT Salsa queries, just regular function calls
fn try_solve(constraint: Constraint, metas: &mut MetaContext) -> SolveResult {
    match constraint {
        Unify(X, Arrow(Int, Y)) => {
            if metas.is_solved(Y) {
                SolveResult::Solved
            } else {
                SolveResult::Stalled(constraint) // Try again later
            }
        }
    }
}
```

No Salsa cycle, just iteration until fixpoint.

### 4. Unified with LCF Kernel (ADR-001)

HWML's LCF kernel is the trusted computing base. It must NEVER see metavariables.

**The pipeline:**
```
Surface AST
    ↓ (elaborate_scc - untrusted)
CoreTerm with metavars (?X, ?Y)
    ↓ (solve_constraints - untrusted)
Solved metavars (?X := Int, ?Y := Bool)
    ↓ (zonk - untrusted)
Pure CoreTerm (no metavars)
    ↓ (kernel::verify - TRUSTED)
✓ or Error
```

The kernel only sees the final, zonked `CoreTerm`. If the elaborator hallucinates a false proof, the kernel rejects it.

**Example:**
```rust
// Elaborator BUG: Solver incorrectly unified ?X = String when it should be Int
let zonked = CoreTerm::Var(0); // Claims x : Int, but actually bound to String

// Kernel catches this:
kernel::verify(db, zonked, expected_ty)
    → Err(TypeError::VarTypeMismatch)
```

This is why metavariables MUST NOT escape: the kernel can't verify terms with holes.

### 5. Matches State-of-the-Art Compilers

**rust-analyzer (Salsa + chalk):**
- Salsa queries at crate/item granularity
- Trait solving (constraint solving) local to query execution
- Output is pure, cached by Salsa

**GHC 9+ (with -fwrite-if-simplified-core):**
- Constraint solving local to module compilation
- Output interface files are pure, deterministic
- Incremental recompilation via interface file hashing

**Sorbet (Stripe's Ruby typechecker):**
- Salsa-like query system
- Type inference with constraints
- Constraints solved within query, don't escape

**Lean 4:**
- Metavariables local to elaboration context
- Kernel verification at boundary
- Deterministic output for caching

Our architecture matches these proven designs.

---

## Consequences

### Positive

1. **Salsa caching works perfectly**
   - Pure inputs (Surface AST), pure outputs (CoreTerm)
   - Change detection automatic
   - Incremental recompilation across libraries

2. **Deterministic builds**
   - Same inputs → same outputs (bit-identical)
   - Buck2 remote execution works
   - Reproducible builds

3. **No false cycle panics**
   - Constraint iteration happens locally, not via Salsa queries
   - Real cycles (cross-library) still caught by Salsa

4. **LCF kernel boundary respected**
   - Kernel never sees metavariables
   - Elaborator bugs caught at verification boundary

5. **Understandable architecture**
   - Clear separation: Salsa (cross-library), Solver (intra-library), Kernel (verification)
   - Metavariable lifetime is obvious (local to function)

### Negative

1. **Elaboration not incrementalized within a library**
   - Change one file in library → re-elaborate entire library
   - *Mitigation:* Most libraries are small (<10 files). Re-elaboration <100ms.
   - *Future:* Could cache at SCC granularity if needed

2. **Solver loop complexity**
   - Worklist algorithm is non-trivial
   - *Mitigation:* Well-understood pattern (unification algorithms textbook material)

3. **Two topological sorts**
   - Salsa handles cross-library topo-sort
   - We handle intra-library SCC topo-sort
   - *Mitigation:* These are different concerns. Intra-library SCCs are for mutual recursion.

### Neutral

- **Constraint solver must be complete within an SCC**
  - Cannot defer constraints to "later SCCs"
  - This is by design: mutual recursion requires explicit signatures in HWML

---

## Alternatives Considered

### Alternative 1: Global Metavariable Context

**What:** Maintain a global `MetaContext` shared across all Salsa queries

**Why rejected:**
- Defeats Salsa caching (every elaboration mutates global state)
- Non-deterministic (MetaId assignment depends on query execution order)
- Not thread-safe without heavy locking
- Violates Salsa's purity requirements

### Alternative 2: Constraint Solving as Salsa Queries

**What:** Make `solve_constraint` a Salsa query

```rust
#[salsa::tracked]
fn solve_constraint(db: &dyn Db, constraint: Constraint) -> Solution {
    match constraint {
        Unify(a, b) => {
            let a_solved = solve_metavar(db, a); // ← Cycle panic!
            let b_solved = solve_metavar(db, b);
            // ...
        }
    }
}
```

**Why rejected:**
- Apparent cycles cause Salsa panics
- Can't represent "stalled" constraints (Salsa queries must return a value)
- Constraint solving order matters (not declarative enough for Salsa)

### Alternative 3: Pure Constraint-Free Elaboration

**What:** Require all types to be fully annotated, no inference

**Why rejected:**
- Poor user experience (verbosity)
- Defeats purpose of dependent types (type-level computation)
- Still need metavariables for implicit arguments

### Alternative 4: Lazy Constraint Solving (Return Constraints to Salsa)

**What:** Have `elaborate_library` return `(CoreTerm, Vec<Constraint>)`, solve later

```rust
#[salsa::tracked]
fn elaborate_library(...) -> (CoreTerm, Vec<Constraint>) {
    // Return unsolved constraints
}

// Later, outside Salsa:
let (term, constraints) = elaborate_library(db, ...);
solve(constraints); // ← Not cached!
```

**Why rejected:**
- Salsa can't cache constraint solutions (solving happens outside queries)
- Non-deterministic (solving order varies)
- Breaks incremental compilation

---

## Implementation Notes

### ElabState Structure

```rust
pub struct ElabState {
    /// Metavariable context
    metas: MetavariableContext,

    /// Constraint worklist
    worklist: Vec<Constraint>,

    /// Diagnostics accumulated during elaboration
    diagnostics: Vec<Diagnostic>,
}

impl ElabState {
    pub fn new() -> Self {
        Self {
            metas: MetavariableContext::new(),
            worklist: Vec::new(),
            diagnostics: Vec::new(),
        }
    }

    pub fn clear_for_bodies(&mut self) {
        // Keep metas (signatures already solved), clear worklist
        self.worklist.clear();
    }
}
```

### MetavariableContext

```rust
pub struct MetavariableContext {
    solutions: HashMap<MetaId, MetaSolution>,
    next_id: u32,
}

pub enum MetaSolution {
    Unsolved { level: UniverseLevel },
    Solved(CoreTerm),
}

impl MetavariableContext {
    pub fn fresh_meta(&mut self, level: UniverseLevel) -> MetaId {
        let id = MetaId(self.next_id);
        self.next_id += 1;
        self.solutions.insert(id, MetaSolution::Unsolved { level });
        id
    }

    pub fn solve(&mut self, meta: MetaId, solution: CoreTerm) -> Result<()> {
        // Occurs check, universe level check
        self.solutions.insert(meta, MetaSolution::Solved(solution));
        Ok(())
    }

    pub fn zonk_term(&self, term: &CoreTerm) -> CoreTerm {
        // Replace all MetaIds with their solutions (recursively)
    }
}
```

### Constraint Types

```rust
pub enum Constraint {
    /// Unification: two terms must be equal
    Unify { lhs: CoreTerm, rhs: CoreTerm, span: Span },

    /// Subtyping: lhs must be subtype of rhs (for implicit coercions)
    Subtype { sub: CoreTerm, sup: CoreTerm, span: Span },

    /// Instance search: find instance of typeclass (future)
    Instance { class: CoreTerm, span: Span },
}

pub enum SolveResult {
    /// Constraint solved, metavars updated
    Solved,

    /// Constraint blocked on unsolved metavars
    Stalled(Constraint),

    /// Constraint cannot be satisfied
    Error(ElabError),
}
```

### Zonking (Replacing Metavars with Solutions)

```rust
fn zonk_term(metas: &MetavariableContext, term: &CoreTerm) -> Result<CoreTerm, ElabError> {
    match term {
        CoreTerm::Meta(id) => {
            match metas.solutions[id] {
                MetaSolution::Solved(ref solution) => {
                    // Recursively zonk the solution (may contain metas)
                    zonk_term(metas, solution)
                }
                MetaSolution::Unsolved { .. } => {
                    Err(ElabError::UnsolvedMetavariable(*id))
                }
            }
        }
        CoreTerm::Lam(param, body) => {
            Ok(CoreTerm::Lam(
                zonk_term(metas, param)?,
                zonk_term(metas, body)?
            ))
        }
        // ... other cases
    }
}
```

---

## Migration Path

**Phase 1 (Current):** Single-file elaboration works

**Phase 2 (This ADR):**
- Create `ElabState` struct
- Implement worklist solver
- Implement zonking
- Integrate with Salsa queries as shown above

**Phase 3 (Future optimization):**
- Cache at SCC granularity instead of library granularity
- Parallel SCC elaboration (Salsa 2022+ parallel queries)

---

## Success Metrics

- [ ] No global metavariable state in codebase
- [ ] All constraint solving happens within Salsa query execution (local `ElabState`)
- [ ] Elaboration is deterministic (same input → same output, tested with repeated builds)
- [ ] Kernel verification never sees metavariables
- [ ] Salsa cache hit rate >80% on incremental builds
- [ ] No Salsa cycle panics from constraint solving

---

## References

**Related ADRs:**
- [[ADR-007-salsa-driven-compilation]] - Demand-driven query execution
- [[ADR-001-lcf-kernel]] - Trusted kernel verification
- [[research/modern-incremental-compilation]] - Salsa, rust-analyzer, chalk

**Academic Background:**
- Pierce, *Types and Programming Languages* - Constraint-based typing
- McBride, *Elaborating Inductive Definitions* - Elaboration and metavariables
- Norell, *Towards a Practical Programming Language Based on Dependent Type Theory* - Agda's constraint solver

**Implementation References:**
- rust-analyzer + chalk: Trait solving local to query execution
- Lean 4: MetavarContext per elaboration
- Idris 2: Unification state in ElabInfo

---

**Status:** Approved
**Next Steps:**
1. Design `ElabState` and `MetavariableContext` types
2. Implement worklist solver algorithm
3. Implement zonking
4. Update `elaborate_library` query to use local state
5. Add kernel verification at boundary
6. Test determinism with repeated builds


