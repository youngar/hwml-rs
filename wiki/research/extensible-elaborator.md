# ExEl: Building an Elaborator Using Extensible Constraints

**Source:** `external/extensible-elaborator/paper/main.md`  
**Type:** Research Paper  
**Authors:** Liesnikov et al.  
**Repository:** [github.com/liesnikov/extensible-elaborator](https://github.com/liesnikov/extensible-elaborator)  
**Archived:** [doi.org/10.4121/e74fd14a-da79-4686-97e8-143ac5e0858d.v1](https://doi.org/10.4121/e74fd14a-da79-4686-97e8-143ac5e0858d.v1)  
**Created:** 2026-05-03  
**Relevance:** High - Directly applicable to HWML's elaborator design

---

## Overview

This paper presents a **new architecture for building extensible elaborators** for dependently typed languages. The key innovation is treating **constraints as an extensible datatype** with **pluggable solvers**, rather than having a monolithic unifier.

### Core Idea

Instead of one large unifier that handles all type checking, metavariable solving, and implicit argument resolution:

1. **Extensible Constraints** - New constraint types can be added via plugins
2. **Modular Solvers** - Each feature has its own solver that registers for specific constraint types
3. **Clear Separation** - Type-checking raises constraints, solvers fulfill them asynchronously

---

## Key Contributions

1. **Extensible Architecture Blueprint** - How to build elaborators that support:
   - Type classes
   - Implicit arguments
   - Implicit coercions
   - Tactic arguments

2. **Metavariables as Communication Channels** - Viewing metas as async primitives for solver communication

3. **Decomposed Unification** - Breaking monolithic unifiers into suites of small, interleaved solvers

4. **Working Prototype** - Implemented dependently typed language demonstrating the design

---

## Problem: Elaborators Are Complex and Fragile

### Example: Agda's Unifier

- **2200 lines of code** spread across ~100 functions
- Mixes "business logic" with metavariable bookkeeping
- Uses functions like `noConstraints`, `dontAssignMetas`, `catchConstraint`, `patternViolation`
- Hard to understand, brittle, risky to modify
- The core logic is only ~20 lines, rest is infrastructure

### Example: Adding Implicit Arguments

In existing languages like Agda/Idris:
- Must create specific kinds of metavariables for each implicit type
- Search procedures are inlined into application checking
- Each new feature requires modifying core elaboration logic
- Features interact in unexpected ways

### Example: Extending Unification

Adding user-extensible features like:
- Canonical structures (required 15 years to document properly in Coq)
- Injective type constructors
- Associativity/commutativity rules (2000 line changes in Agda)

---

## Solution: Constraint-Based Extensible Architecture

### Architecture Diagram

```
┌─────────────────────────────────────────────────────────┐
│                    Syntax Traversal                      │
│              (Bidirectional Type Checking)               │
│                   Raises Constraints                     │
└────────────────────┬────────────────────────────────────┘
                     │
                     ▼
┌─────────────────────────────────────────────────────────┐
│                  Solver Dispatcher                       │
│         (Traverses constraints, calls solvers)           │
└────────┬───────────────────────────────┬────────────────┘
         │                               │
         ▼                               ▼
┌──────────────────┐           ┌──────────────────┐
│   Plugin A       │           │  Unification     │
│ ┌──────────────┐ │           │ ┌──────────────┐ │
│ │   Handler    │ │           │ │   Handler    │ │
│ └──────────────┘ │           │ └──────────────┘ │
│ ┌──────────────┐ │           │ ┌──────────────┐ │
│ │   Solver     │ │           │ │   Solver     │ │
│ └──────────────┘ │           │ └──────────────┘ │
└──────────────────┘           └──────────────────┘
```

### Key Components

1. **Syntax Traversal** - Bidirectional type checking that raises constraints
2. **Solver Dispatcher** - Matches constraints to appropriate solvers
3. **Plugins** - User-defined or built-in (unification, type classes, etc.)
   - **Handler**: Decides if plugin can solve this constraint
   - **Solver**: Actually solves it

---

## Base Constraints

Three fundamental constraint types for the base language:

```haskell
-- Two terms should be equal
data EqualityConstraint e =
     EqualityConstraint Term Term Type MetaVarId

-- This term must be filled in eventually
data FillInTheTerm e =
     FillInTheTerm Term (Maybe Type)

-- This term should be a type constructor
data TypeConstructorConstraint e =
     TypeConstructorConstraint Type
```

---

## Example: Syntactic Equality Solver

```haskell
-- Handler: decides if solver should fire
syntacticHandler :: (EqualityConstraint :<: c)
                 => HandlerType c
syntacticHandler constr = do
  let eqcm = match @EqualityConstraint constr
  case eqcm of
    Just (EqualityConstraint t1 t2 ty _) ->
      return $ aeq t1 t2  -- alpha-equality
    Nothing ->
      return False

-- Solver: executes when handler approves
syntacticSolver :: (EqualityConstraint :<: c)
                => SolverType Bool

-- Plugin registration
syntactic :: Plugin
syntactic = Plugin { solver  = syntacticSolver
                   , handler = syntacticHandler
                   , ...
                   }
```

**Key Insight:** Separation between fast read-only decision (handler) and potentially slow effectful solving (solver).

---

## Case Study: Implicit Arguments

### Surface Syntax Preprocessing

Desugar function declarations:
```
def f : {A : Type} -> {a : A} -> B a -> C
```
becomes:
```
def f : (A : Implicit Type)
     -> (a : Implicit (deImp A))
     -> (b : B (deImp a)) -> C
```

Insert placeholders at call sites: `f b1` → `f _ _ b1`

### Elaboration

The `Implicit` case in syntax traversal:
```haskell
checkType (Implicit) ty = do
  m <- createMetaTerm
  raiseConstraint $ FillInTheMeta m ty
  return m
```

### Solving

Simple solver checks if meta was instantiated:
```haskell
fillInImplicitHandler constr = do
  let ficm = match @FillInImplicit constr
  case ficm of
    Just (FillInImplicit term ty) ->
      case term of
        MetaVar (MetaVarClosure mid _) ->
          isMetaSolved mid
        _ -> return False
    Nothing -> return False
```

The actual solving happens via **unification** - the constraint just ensures eventual instantiation.

---

## Case Study: Type Classes

### New Constraint Type

```haskell
data InstanceSearch e = InstanceSearch TCName Type MetaVarId
```

### Plugin Architecture

Contained in a single file, the plugin:
1. Defines `InstanceSearch` constraint
2. Transforms `FillInTheTerm ? (InstanceT _)` → `InstanceSearch`
3. Implements instance search solver

### Instance Search Solver

```haskell
instanceConcreteSolver constr = do
  let (Just (InstanceSearch tcn ty m)) =
        match @InstanceSearch constr
  alldecls <- collectInstancesOf tcn <$> SA.getDecls
  sty <- SA.substAllMetas ty
  case Map.lookup sty alldecls of
    Just i -> do
      SA.solveMeta m (I.Var i)
      return True
    Nothing -> return False
```

### Example Elaboration

Given:
```
plus : {A : Type} -> {{PlusOperation A}}
    -> (a : A) -> (b : A) -> A

instance BoolPlus : PlusOperation Bool where
  plus = orb

m = plus True False
```

After preprocessing:
```
m = plus _ _ True False
```

Constraints raised:
```
C1: FillInTheTerm ?_1 (Implicit Type)
C2: FillInTheTerm ?_2 (InstanceT PlusOperation (deImp ?_1))
C3: EqualityConstraint (deImp ?_1) Bool Type
C4: EqualityConstraint (deImp ?_1) Bool Type
```

Solving:
1. Unifier solves C3, C4 → `?_1 = Implicit Bool`
2. C1 discarded (already solved)
3. Type class plugin transforms C2 → `InstanceSearch PlusOperation Bool ?_2`
4. Instance search finds `instanceBoolPlus`, solves `?_2`

---

## Case Study: Pi-Type Injectivity

Implements the "decomposition of functions" rule from higher-order unification.

### Handler

```haskell
piEqInjectivityHandler constr = do
  let eqcm = match @EqualityConstraint constr
  case eqcm of
    Just (EqualityConstraint pi1 pi2 _ _) ->
      case (pi1, pi2) of
        (I.Pi _ _ _, I.Pi _ _ _) -> return True
        _ -> return False
    _ -> return False
```

### Solver

```haskell
piEqInjectivitySolver constr = do
  let (Just (EqualityConstraint (I.Pi a1 b1)
                                (I.Pi a2 b2) _ m)) =
        match @EqualityConstraint constr

  -- Constrain domain equality
  ma <- constrainEquality a1 a2 I.Type

  -- Constrain codomain equality in extended context
  (x, tyB1) <- unbind b1
  (y, tyB2') <- unbind b2
  let tyB2 = subst y (I.Var x) tyB2'
      mat  = I.identityClosure ma
  mb <- extendCtx (I.TypeSig (I.Sig x a1 mat)) $
                  constrainEquality tyB1 tyB2 I.Type

  -- Solve anti-unification variable
  let mbt = bind x $ I.identityClosure mb
  solveMeta m (I.Pi mat mbt)
  return True
```

**Key Technique:** Anti-unification variables (`ma`, `mb`) serve as communication channels between solvers, handling the "spine problem" for well-typed terms in extended contexts.

---

## Case Study: User-Defined Injectivity

Users can declare functions as injective, extending unification.

### Implementation

```haskell
userInjectivitySolver constr = do
  let (Just EqualityConstraint
              (I.App (I.Var f) a)
              (I.App (I.Var g) b) _ m)) =
        match @EqualityConstraint constr
  if f == g
  then do
    ifM (queryInjectiveDeclarations f)
        (do
           ms <- constrainEquality a b I.Type
           solveMeta m ms
           return True)
        (return False)
  else return False
```

### Solver Ordering

Plugin specifies when to fire:
```haskell
userInjectivityPlugin =
  Plugin { ...
         , solver = userInjectivitySolver
         , pre = [unifyNeutralsDecomposition,
                  unificationEndMarkerSymbol]
         , suc = [unificationStartMarkerSymbol]
         }
```

The `pre` and `suc` fields create a partial order on solvers, linearized at runtime.

**Impact:** Non-invasive extension - doesn't modify core language.

---

## Relevance to HWML

### Direct Applications

1. **Modular Elaborator Design**
   - HWML's elaborator could use the same constraint-based architecture
   - Each feature (implicits, type classes, coercions) in separate plugins
   - Easier to maintain and extend

2. **Extensible Type System**
   - Users could add custom constraint solvers
   - Enable domain-specific elaboration extensions
   - Support hardware-specific type elaboration rules

3. **Cleaner Unification**
   - Break HWML's unifier into small, testable solvers
   - Each unification rule in its own module
   - Easier to debug and verify

### Design Patterns

1. **Separation of Concerns**
   - Syntax traversal: raise constraints
   - Solver dispatcher: orchestrate solving
   - Solvers: implement feature-specific logic

2. **Handler/Solver Split**
   - Fast read-only filtering (handlers)
   - Slow effectful solving only when needed
   - No rollback of unnecessary effects

3. **Anti-Unification Variables**
   - Communication channels between solvers
   - Preserve well-typedness in extended contexts
   - Handle "spine problem" elegantly

### Potential Improvements for HWML

1. **Plugin System**
   - Allow hardware vendors to add domain-specific elaboration
   - Clock domain inference, resource usage tracking, etc.
   - Without modifying core HWML compiler

2. **Constraint Visualization**
   - Could expose constraint graph to users
   - Help debug type errors
   - Show why elaboration succeeded/failed

3. **Staged Elaboration**
   - Clear phases: syntax → constraints → solving
   - Better error messages (know which phase failed)
   - Potential for parallel constraint solving

---

## Implementation Details

### Language Foundation

Based on **pi-forall** with extensions:
- Dependent types (Pi, Sigma)
- Indexed inductive types
- Equality types (built-in, not user-defined inductives)
- Metavariables in core syntax
- Implicit arguments in surface syntax

### Core Term Syntax

```haskell
data Term =
    Type
  | Var TName
  | Lam (Bind TName Term)
  | App Term Arg
  | Pi Type (Bind TName Type)
  | Sigma Term (Bind TName Term)
  | Prod Term Term
  | LetPair Term (Bind (TName, TName) Term)
  | TyEq Term Term
  | Refl
  | Subst Term Term
  | Contra Term
  | TCon TCName [Arg]        -- Type constructors
  | DCon DCName [Arg]        -- Data constructors
  | Case Term [Match]
  | MetaVar MetaClosure      -- Metavariables with closures
```

### Bidirectional Type Checking

Syntax traversal raises constraints instead of directly solving:

**Checking against known type:**
```haskell
checkType tm ty = do
  (etm, ty') <- inferType tm
  constrainEquality ty' ty I.Type
  return etm
```

**Decomposing Pi-types:**
```haskell
checkType (S.Lam lam) ty = do
  mtyA <- createMetaTerm
  mtx <- createUnknownVar
  mtyB <- extendCtx (I.TypeSig (I.Sig mtx mtyA))
                    (createMetaTerm)
  let metaPi = I.Pi mtyA (bind mtx mtyB)
  constrainEquality ty metaPi I.Type
  -- Continue with mtyA and mtyB available
  ...
```

**With continuation (blocking):**
```haskell
checkType t@(S.DCon c args) ty = do
  elabpromise <- createMetaTerm
  constrainTConAndFreeze ty $ do
    mty <- substMetas ty
    case mty of
      (I.TCon tname params) -> ...
      _ -> error "impossible"
```

### Contextual Metavariables

Following Abel (2011), metavariables use **contextual style**:

```haskell
data MetaClosure = MetaVarClosure MetaVarId Closure
```

Closures track delayed substitutions, handling:
- Variables going in/out of scope
- Delayed application of anti-unification results
- Occurs check and invertibility checks

### Anti-Unification Variables

Every equality constraint returns a metavariable:

```haskell
constrainEquality :: Term -> Term -> Type -> SolverMonad MetaVarId
```

This meta represents the unified term, used for:
- Extended contexts (Pi-type codomains, data constructor arguments)
- Well-typedness preservation
- Solving the "spine problem"

Can block on these metas if needed by other solvers.

---

## Suite of Unification Solvers

The prototype implements these modular solvers:

1. **identityPlugin** - Syntactic equality (alpha-equivalence)
2. **propagateMetasEqPlugin** - Meta propagation rules
3. **reduceLeftPlugin** - Reduce left side of equality
4. **reduceRightPlugin** - Reduce right side of equality
5. **leftMetaPlugin** - Left side is unsolved meta
6. **rightMetaPlugin** - Right side is unsolved meta
7. **typeConstructorPlugin** - Type constructor constraints
8. **typeConstructorWithMetasPlugin** - TyCon with meta arguments
9. **piEqInjectivityPlugin** - Pi-type decomposition
10. **tyEqInjectivityPlugin** - Equality type decomposition
11. **consInjectivityPlugin** - Data constructor injectivity
12. **typeInjectivityPlugin** - Type injectivity
13. **unificationStartMarker** - Ordering marker
14. **unificationEndMarker** - Ordering marker

Each is 10-50 lines of code, testable in isolation.

### Example: Left Meta Solver

```haskell
leftMetaSolver constr = do
  let (Just (EqualityConstraint t1 t2 _ m)) =
        match @EqualityConstraint constr
      (MetaVar (MetaVarClosure m1 c1)) = t1

  mt2 <- occursCheck m1 t2
  case mt2 of
    Left e -> return False  -- Occurs check failed
    Right t2 ->
      case (invertClosureOn c1 (freeVarList t2)) of
        Just s -> do
          let st2 = substs s t2
          solveMeta m1 st2            -- Solve the meta
          solveMeta m st2              -- Solve anti-unification var
          return True
        Nothing -> return False        -- Closure not invertible
```

---

## Solver Ordering and Priorities

### Partial Order Specification

Plugins declare ordering preferences:

```haskell
rightMetaPlugin =
  Plugin { handler = rightMetaHandler
         , solver  = rightMetaSolver
         , symbol  = rightMetaSymbol
         , pre = []                    -- Run before these
         , suc = [leftMetaSymbol]      -- Run after these
         }
```

### Linearization

At compile time:
1. Collect all `pre` and `suc` constraints
2. Build partial order graph
3. Linearize to total order (topological sort)
4. Dispatcher uses this order

Allows fine-grained control without hardcoding execution order.

---

## Extensibility Examples

### Adding Canonical Structures

Would require:
1. New constraint type for projection injectivity
2. Solver that fires on canonical structure projections
3. Integration with instance search

Conjectured to be "relatively simple" due to:
- Openness of unification procedure
- Openness of instance search
- Existing plugin infrastructure

### Adding Tactic Arguments

Similar to type classes:
1. Preprocess `{! tactic !}` syntax → `Tactic tacticName`
2. Transform `FillInImplicit ? (Tactic t)` → `RunTactic t ?`
3. Solver executes tactic (can run arbitrary type-checking actions)

### Adding Coercive Subtyping

More preprocessing-heavy:
1. Insert coercion placeholders around arguments, heads, types
2. Raise constraints for each placeholder
3. Solver searches for coercion chains
4. Must handle non-local constraint resolution

Paper notes this is more complex than other extensions.

---

## Comparison to Existing Systems

### Agda (v2.6.4)

**Problems:**
- 19 constraint constructors grown organically
- Unifier: 2200 lines across 100 functions
- Bookkeeping mixed with business logic
- Functions: `noConstraints`, `dontAssignMetas`, `catchConstraint`
- Fragile, hard to extend
- Features interact unexpectedly (instance search + sized types)

**ExEl Approach:**
- Open constraint datatype
- Each rule ~10-50 lines in own module
- Clear separation: what vs when
- Modular, extensible

### Idris 2

**Problems:**
- Only 2 constraint types (term equality, term list equality)
- Instance search inlined through elaboration call chain
- Adding new implicit kinds requires deep modification

**ExEl Approach:**
- Arbitrary constraint types
- Dispatch to specialized solvers
- New implicit kinds = new constraint + solver

### Lean 4

**Advantage:**
- Has elaboration reflection (metaprogramming)
- Users can define surface-level features

**But:**
- Lean 3 was conventional
- Core still has monolithic components

**ExEl Approach:**
- Extensibility built into architecture
- Not just surface syntax, but elaboration itself

### Coq

**Problems:**
- Canonical structures undocumented for 15 years
- Unpredictable results
- 1.8kloc unifier

**ExEl Approach:**
- Each feature self-contained
- Easier to document and understand
- Plugin isolation

---

## Technical Innovations

### 1. Metavariables as Async Primitives

View metavariables as **communication channels** between solvers:
- Solvers "write" by instantiating metas
- Solvers "read" by checking meta solutions
- Can "block" waiting for meta instantiation
- Similar to futures/promises in async programming

This perspective clarifies:
- When to retry postponed constraints (when blocking meta solved)
- How to coordinate multiple solvers
- Error handling in elaboration

### 2. Open Data Types (Data Types à la Carte)

Constraints use Swierstra (2008) technique:

```haskell
-- Base constraint types
data EqualityConstraint e = ...
data FillInImplicit e = ...

-- User extension
data InstanceSearch e = ...

-- Combined via (:<:) type class
type MyConstraints =
  EqualityConstraint :<: FillInImplicit :<: InstanceSearch
```

Allows:
- Type-safe constraint matching
- Modular constraint definition
- Plugin-local constraint types

### 3. Handler/Solver Duality

**Design Choice:** Separate decision from execution

**Handler (fast, read-only):**
- Decides if solver can handle constraint
- No effects (or rollback-able)
- Runs on many non-matching constraints
- Returns `Bool`

**Solver (slow, effectful):**
- Actually solves the constraint
- Can modify state, raise new constraints
- Only runs when handler approves
- Returns success/failure

**Benefit:** Avoid rolling back effects from unsuccessful solving attempts.

### 4. Anti-Unification as First-Class

Traditional unification: `unify(t1, t2) -> success/failure`

ExEl unification: `unify(t1, t2) -> Meta representing unified term`

**Why:**
- Solves "spine problem" (well-typed terms in extended contexts)
- Provides communication channel between solvers
- No duplication between unification and anti-unification

**Criticism:** Tog+ (2020) argues Agda's separate anti-unification is bug-prone

**Defense:** ExEl unifies them - anti-unification IS unification

---

## Limitations and Future Work

### Current Limitations

1. **No Plugin Dynamic Loading**
   - Must recompile to add plugins
   - Could add dynamic loading (like GHC Plugins)

2. **Implicit Arguments Restrictions**
   - Only "obvious" implicits (syntactically in declaration)
   - Insertion before type info available
   - Can't support Haskell-like impredicativity

3. **No Formal Verification**
   - Modularity doesn't enforce correctness
   - Properties (soundness, completeness) still need proof
   - Harder to prove than monolithic systems?

4. **Coercive Subtyping Complexity**
   - Requires extensive preprocessing
   - Non-local constraint resolution
   - More research needed

### Proposed Future Work

1. **First-Class Implicits**
   - Kovaćs (2020) style
   - More comprehensive support
   - Solves impredicativity issues

2. **Formal Semantics**
   - Prove soundness of plugin architecture
   - Verify that solver ordering preserves properties
   - Ensure plugin isolation guarantees

3. **Parallel Solving**
   - Independent constraints could solve in parallel
   - Requires careful dependency tracking
   - Could significantly speed elaboration

4. **Constraint Visualization**
   - For debugging type errors
   - Show constraint dependency graph
   - Explain elaboration failures

5. **More Case Studies**
   - Sized types (problematic in Agda)
   - Cubical features
   - Linear types
   - Hardware-specific elaboration

---

## Key Takeaways

### For Language Implementers

1. **Constraints Should Be Central**
   - Not just a gadget for unification
   - Core abstraction for elaborator architecture

2. **Modular Is Maintainable**
   - 20-line solvers vs 2200-line unifiers
   - Each feature in one file
   - Easier to debug, extend, document

3. **Separate What from When**
   - Type-checking raises constraints (what)
   - Solver dispatcher orchestrates (when)
   - Solvers implement logic (how)

4. **Async Thinking Helps**
   - Metavariables are communication channels
   - Blocking is explicit
   - Error handling clearer

### For Language Users

1. **Predictable Extensions**
   - Each feature isolated
   - Understand one plugin at a time
   - Interactions explicitly ordered

2. **Better Error Messages**
   - Know which phase failed (syntax/constraints/solving)
   - See constraint that couldn't be solved
   - Trace solver attempts

3. **User Extensibility**
   - Add domain-specific solvers
   - Declare custom injectivity
   - Implement project-specific tactics

### For HWML

1. **Apply Architecture**
   - Constraint-based elaborator from start
   - Modular unification
   - Plugin system for domain features

2. **Hardware-Specific Extensions**
   - Clock domain inference as plugin
   - Resource constraints as constraint type
   - Timing elaboration as solver

3. **Better Engineering**
   - Easier to maintain
   - Safer to extend
   - Clearer for contributors

---

## References and Links

### Paper

- **Full Paper:** `external/extensible-elaborator/paper/main.md`
- **Repository:** [github.com/liesnikov/extensible-elaborator](https://github.com/liesnikov/extensible-elaborator)
- **Archived:** [doi.org/10.4121/e74fd14a-da79-4686-97e8-143ac5e0858d.v1](https://doi.org/10.4121/e74fd14a-da79-4686-97e8-143ac5e0858d.v1)

### Key Citations

- **Abel (2011):** Higher-Order Dynamic Pattern Unification (contextual metavariables)
- **Swierstra (2008):** Data Types à la Carte (open datatypes)
- **McBride:** "Write more types and fewer programs"
- **Peyton Jones (2019):** Type Inference via Constraint Solving (Haskell/GHC approach)
- **Mahboubi (2013):** Canonical Structures Working Guide
- **Kovaćs (2020):** Elaboration with First-class Implicit Function Types

### Related Systems

- **pi-forall:** Foundation for ExEl implementation
- **Agda:** Example of organic constraint growth
- **Idris 2:** Elaborator reflection
- **Lean 4:** Elaboration monads
- **Coq:** Canonical structures, evars

### Related HWML Docs

- [[ADR-002-bidirectional-typing]] - HWML uses bidirectional typing
- [[entities/nbe]] - Normalization technique (complementary to elaboration)
- See also: LCF kernel pattern for trusted core

---

## Discussion Points for HWML

### Q: Should HWML Adopt This Architecture?

**Pros:**
- Better modularity from day one
- Easier to extend with hardware features
- Cleaner codebase, easier onboarding
- Proven in prototype

**Cons:**
- More upfront design complexity
- Need to learn constraint-based thinking
- May complicate correctness proofs
- Not yet battle-tested at scale

**Recommendation:** Seriously consider for initial elaborator design. The benefits for maintainability and extensibility align well with HWML's goals.

### Q: What Would HWML-Specific Plugins Look Like?

**Clock Domain Inference:**
```haskell
data ClockDomainConstraint e =
  ClockDomainConstraint Signal Signal ClockDomain

clockDomainSolver :: SolverType
-- Infers clock domains for signals
-- Raises errors on domain crossings without proper synchronizers
```

**Resource Usage:**
```haskell
data ResourceConstraint e =
  ResourceConstraint Module Resources

resourceSolver :: SolverType
-- Tracks FPGA resource usage
-- Warns when approaching capacity
```

**Timing Constraints:**
```haskell
data TimingConstraint e =
  TimingConstraint Path Frequency

timingSolver :: SolverType
-- Elaborates timing requirements
-- Suggests pipeline insertion
```

### Q: How Does This Relate to LCF Kernel?

**Complementary:**
- LCF kernel: **trusted core** for term construction
- ExEl architecture: **elaborator** from surface syntax to core

**Interaction:**
- Solvers operate *outside* kernel
- Only instantiate metas via kernel API
- Kernel guarantees well-formedness
- Elaborator provides convenience

**HWML Could Use Both:**
- Kernel for soundness
- Extensible elaborator for usability

### Q: Implementation Timeline?

**Phase 1 (Current):**
- Simple bidirectional checker
- Monolithic unification
- Get basic language working

**Phase 2 (Refactor):**
- Extract constraint types
- Split unifier into plugins
- Add solver dispatcher

**Phase 3 (Extend):**
- User plugin API
- Hardware-specific solvers
- Advanced features

**Pragmatic:** Start simple, refactor to ExEl architecture as language matures.

---

## Conclusion

ExEl demonstrates that **constraint-based architecture with pluggable solvers** is viable for dependently typed languages. The approach yields:

- **Modularity:** Each feature in one file, ~20 lines per solver
- **Extensibility:** New constraints and solvers without core changes
- **Clarity:** Separation between "what" (constraints) and "when" (dispatch)
- **Maintainability:** Easier to understand, debug, and extend

For HWML, this architecture could be particularly valuable:
- Hardware-specific elaboration as plugins
- Domain-specific constraint types
- Easier to onboard contributors
- Better positioned for future extensions

**Next Steps:**
1. Review full paper details
2. Prototype constraint-based elaborator for HWML subset
3. Evaluate performance and complexity
4. Decide on adoption vs adaptation

---

**Last Updated:** 2026-05-03
**Status:** Complete summary of ExEl paper
**Cross-References:** [[ADR-002-bidirectional-typing]], [[entities/nbe]]

