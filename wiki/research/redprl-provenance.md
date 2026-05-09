# RedPRL Family: Provenance Through Dependent LCF

**Research Date**: 2026-05-07  
**Research Focus**: How the RedPRL family (RedPRL, redtt, cooltt) tracks metavariable provenance through their "Dependent LCF" refinement architecture

---

## Executive Summary

The RedPRL family of proof assistants (RedPRL, redtt, cooltt) implements a novel approach to proof refinement called **Dependent LCF**, which provides inherent provenance tracking through its use of **telescopes of judgments**. This architecture represents a fundamental innovation over classical LCF-style refiners, where each metavariable is created as part of a telescope that naturally captures both **WHERE** (position in telescope) and **WHY** (the judgment that created it).

**Key Insight for HWML**: RedPRL's telescope structure means provenance is **architectural**, not bolted-on. Each hole/metavariable exists within a judgment in a telescope, so its "birth certificate" is its position and the judgment itself.

---

## What is Dependent LCF?

### The Problem with Classical LCF

Classical LCF (Logic for Computable Functions) proof assistants maintain:
- A **list of subgoals** (independent goals to prove)
- A **validation function** that combines sub-proofs into the main proof

**Problem**: When subgoals depend on each other (e.g., proving `∃x. P(x)` requires first finding `x`, then proving `P(x)` using that specific `x`), classical LCF breaks down. The subgoals aren't truly independent.

### RedPRL's Solution: Telescopes

From the Dependent LCF library documentation:

> "A proof state is a **telescope of judgments**, where each judgment binds a metavariable in the rest of the telescope, together with a term that takes its free metavariables from the telescope."

**Telescope Structure**:
```
[J₁ ⊢ ?α : A₁,  J₂(α) ⊢ ?β : A₂(α),  J₃(α,β) ⊢ ?γ : A₃(α,β), ...]
```

- Each judgment `Jᵢ` introduces a metavariable `?αᵢ`
- Later judgments can **depend on** earlier metavariables
- The "validation" is now an **open term** with free metavariables, not a function

---

## How This Provides Provenance

### 1. Position = WHERE

Every metavariable lives at a specific **position in the telescope**:
- Position 0: Created by the first refinement step
- Position 1: Created by the second refinement step (may depend on position 0)
- Position n: Created by the nth refinement step

**Provenance Captured**: The telescope index directly tells you the order and context of creation.

### 2. Judgment = WHY

Each telescope entry is a **judgment** of the form:
```
Γ ⊢ ?α : A
```

This judgment captures:
- **Γ**: The typing context (what variables are in scope)
- **A**: The type being solved for
- **The judgment form itself**: E.g., "check term against type" vs "synthesize type of term"

**Provenance Captured**: The judgment tells you exactly what refinement rule created the hole.

### 3. Dependencies = WHICH

The telescope structure makes dependencies explicit:
```
[?x : Nat,  ?p : IsEven(?x),  ?q : Proof(P(?x))]
```

Here we can see:
- `?p` depends on `?x` (must wait for `?x` to be solved)
- `?q` also depends on `?x`
- `?p` and `?q` are independent of each other

**Provenance Captured**: The dependency structure shows which holes block which other holes.

---

## RedPRL's "Boundary-Sensitive" Holes

From the redtt documentation:

> "redtt pioneered the **boundary-sensitive treatment of holes** that now appears in Cubical Agda and cooltt."

### What Are Boundary Conditions?

In cubical type theory, when you have a hole of type `(i : I) → A`, the hole might need to satisfy **boundary conditions**:
- At `i=0`, the solution must equal some term `a₀`
- At `i=1`, the solution must equal some term `a₁`

### Provenance of Boundary Conditions

RedPRL tracks:
1. **Which boundaries exist** for each hole
2. **Where the boundaries came from** (which refinement step imposed them)
3. **What the boundary values are** (the terms the solution must match)

This is stored in the telescope judgment, making it part of the hole's inherent provenance.

---

## Architecture: Modules Relevant to Provenance

From examining the source code structure:

### In `redtt/src/lib/`:

1. **`RefineEnv.ml`**: Environment tracking
   - Maintains the current telescope
   - Tracks local metavariables and their bindings

2. **`RefineError.ml`**: Error reporting
   - Reports unsolved holes with context
   - Uses the telescope structure to explain dependencies

3. **`RefineState.ml`**: Global state
   - Manages all active telescopes
   - Tracks which holes are solved vs unsolved

4. **`Elaborator.ml`**: The refinement engine
   - Creates new telescope entries when refinement rules fire
   - Each rule specifies the judgments it produces

### In `cooltt/src/lib/`:

Similar structure, with emphasis on:
- **Cofibration tracking**: Which holes have boundary conditions
- **System elimination**: How to handle disjunctions in hole boundaries

---

## Comparison with HWML's Current Design

| Aspect | HWML (Current) | RedPRL (Dependent LCF) |
|--------|----------------|------------------------|
| **Metavariable Storage** | Flat `HashMap<MetaId, MetaEntry>` | Telescope of judgments |
| **Provenance** | Must add `created_at`, `origin` fields | Inherent in telescope position + judgment |
| **Dependencies** | Implicit (discovered during unification) | Explicit (telescope structure) |
| **Error Messages** | "Unsolved ?42" | "Unsolved ?α from judgment Γ ⊢ ?α : A at position 3" |
| **Boundary Conditions** | Not applicable (non-cubical) | Tracked per-hole in judgment |

---

## Key Lessons for HWML

### 1. **Structured Storage Over Flat Maps**

RedPRL doesn't use `metavar_id → metadata`. Instead:
- Metavariables live **in** a telescope
- Their position and judgment **are** their metadata

**For HWML**: Consider whether `SolverState` should maintain a telescope-like structure, even if HWML isn't using dependent refinement rules. The telescope could just track creation order.

### 2. **Judgment = Origin**

RedPRL doesn't need an `origin: Origin` field because the **judgment itself** is the origin:
- Judgment `Γ ⊢ _ : A → B` → "metavar created by Pi-intro rule"
- Judgment `Γ ⊢ _ : A` in context of `f : A → B` → "metavar created by application"

**For HWML**: Consider storing a richer "judgment" or "goal" with each `MetaEntry`, not just the type.

### 3. **Error Messages from Structure**

When RedPRL reports an unsolved hole, it can say:
```
Unsolved metavariable ?α
  Created by judgment: Γ ⊢ ?α : Nat
  Position in telescope: 2
  Depends on: ?β (position 0)
  Blocks: ?γ, ?δ (positions 4, 5)
```

**For HWML**: The provenance data enables this. We should store enough to reconstruct:
- What rule created the metavar
- What other metavars it depends on
- What other metavars depend on it

### 4. **Schematic Variables vs Object Variables**

From the Algebraic Foundations paper:

> "In what follows, we will often refer to variables as 'schematic variables' in order to emphasize that these are variables which range over evidence in the proof refinement apparatus, as opposed to variables from the object logic."

**Insight**: RedPRL distinguishes:
- **Object variables**: Regular variables in the type theory (like `x : Nat` in user code)
- **Schematic variables** (metavariables): Variables representing unknown evidence

This is analogous to HWML's distinction between:
- **Term-level variables**: Introduced by lambda, let, etc.
- **Metavariables**: Introduced by elaborator (implicit args, type inference, holes)

**For HWML**: Track which elaboration phase created each metavar (parsing? type checking? unification?).

---

## Code Example: Telescope in Practice

From `redtt/src/lib/Elaborator.ml`, a simplified example of how holes are created:

```ocaml
(* When elaborating a Pi-intro rule *)
let intro ?(ident = Ident.anon) (tac_body : T.var -> T.Chk.tac) : T.Chk.tac =
  T.Chk.brule ~name:"Pi.intro" @@
  function
  | D.Pi (base, _, fam), phi, phi_clo ->
    (* Create a new metavariable in the telescope *)
    T.abstract ~ident base @@ fun var ->
      let* fib = RM.lift_cmp @@ Sem.inst_tp_clo fam @@ T.Var.con var in
      (* Continue refinement with the new judgment *)
      let+ tm = T.Chk.brun (tac_body var) (fib, phi, ...) in
      S.Lam (ident, tm)
  | tp, _, _ ->
    RM.expected_connective `Pi tp
```

**Key observations**:
1. `~name:"Pi.intro"` - The rule name is recorded (provenance: WHY)
2. `T.abstract ~ident base` - Creates new telescope entry (provenance: WHERE)
3. `tac_body var` - Passes metavar to continuation (provenance: dependency structure)

---

## Boundary-Sensitive Holes: A Deep Dive

### The Problem

In cubical type theory, you often have holes of path type:
```
?p : Path A a b   where i=0 ⊢ ?p(i) ≡ a
                        i=1 ⊢ ?p(i) ≡ b
```

The hole `?p` must satisfy **boundary conditions**: at the endpoints, it must match given terms.

### RedPRL's Solution

The judgment in the telescope includes the boundary:
```
Γ | φ ↝ [i=0 ↦ a, i=1 ↦ b] ⊢ ?p : Path A a b
```

Where:
- `φ` is a cofibration (formula over dimension variables)
- `[i=0 ↦ a, i=1 ↦ b]` is the boundary specification

### Error Messages

When `?p` can't be solved, RedPRL can report:
```
Unsolved path hole ?p
  Type: Path Nat 0 1
  Required to equal:
    - At i=0: 0
    - At i=1: 1
  Suggested fix: Use connection/composition rules
```

**Provenance tracked**:
- The boundary conditions themselves (WHAT constraints)
- Where they came from (which refinement rule imposed them)
- Why they can't be satisfied (which unification failed)

---

## Practical Impact: Holes in RedPRL vs HWML

### RedPRL User Experience

When a user writes `?` in RedPRL, the elaborator:
1. Creates a new telescope judgment for the hole
2. Records the current context (Γ) and goal type
3. Records any boundary conditions from enclosing path types
4. Returns the hole to the user with full context

User sees:
```
?0 : Nat
  Context: x : Bool, y : Nat
  Goal: Nat
  No boundary conditions
```

### HWML Current Experience (to be improved)

When elaboration creates a metavar in HWML:
1. Adds entry to `SolverState.metas: HashMap<MetaId, MetaEntry>`
2. `MetaEntry` has only: `ty: Term`, `solution: Option<Term>`
3. No context or origin tracked

User sees:
```
error: unsolved metavariable ?42
```

**No information about**:
- Why ?42 was created
- Where in the source code it came from
- What it's supposed to solve
- What other metavars it depends on

---

## Recommendations for HWML Provenance

Based on RedPRL's architecture:

### Immediate (Phase 1)

1. **Add to `MetaEntry`**:
   ```rust
   pub struct MetaEntry<'db> {
       pub ty: Term<'db>,
       pub solution: Option<Term<'db>>,
       // NEW:
       pub created_at: Location<'db>,  // Source location
       pub origin: Origin<'db>,         // What created this
   }
   ```

2. **Define `Origin` enum**:
   ```rust
   pub enum Origin<'db> {
       ImplicitArg { fn_name: Ident<'db>, param_idx: usize },
       TypeInference { expr: TermId<'db>, expected: Term<'db> },
       UserHole { span: Span },
       Unification { lhs: Term<'db>, rhs: Term<'db> },
   }
   ```

### Medium-Term (Phase 2-3)

3. **Add dependency tracking**:
   ```rust
   pub struct MetaEntry<'db> {
       // ... existing fields ...
       pub depends_on: Vec<MetaId>,      // Metavars this one needs
       pub blocks: Vec<MetaId>,          // Metavars that need this one
   }
   ```

4. **Use creation order** (telescope-inspired):
   ```rust
   pub struct SolverState<'db> {
       // Instead of HashMap, use ordered structure:
       pub metas: Vec<(MetaId, MetaEntry<'db>)>,  // Creation order preserved
   }
   ```

### Long-Term (Phase 4-5)

5. **Rich error context** (RedPRL-style):
   ```rust
   pub struct MetaEntry<'db> {
       // ... existing fields ...
       pub creation_context: ElabContext<'db>,  // Full context at creation
       pub goal: Goal<'db>,                     // What we're trying to solve
   }
   ```

---

## References

1. **Sterling & Harper**: "Algebraic Foundations of Proof Refinement" (2017)
   - Introduces Dependent LCF
   - Defines telescopes of judgments
   - https://arxiv.org/abs/1703.05215

2. **Angiuli et al.**: "The RedPRL Proof Assistant" (LFMTP 2018)
   - Practical implementation of Dependent LCF
   - Boundary-sensitive holes

3. **RedPRL Dependent LCF Library**: https://github.com/RedPRL/sml-dependent-lcf
   - Production implementation
   - Clean separation: refinement rules vs tactics

4. **redtt Source Code**: https://github.com/RedPRL/redtt
   - `RefineEnv.ml`, `RefineError.ml`, `RefineState.ml`
   - Shows how telescopes are maintained in practice

5. **cooltt Source Code**: https://github.com/RedPRL/cooltt
   - Modern iteration with improved error handling
   - More sophisticated boundary tracking

---

## Conclusion

The RedPRL family demonstrates that **provenance is architectural**. By structuring the solver state as a telescope of judgments rather than a flat map of metavariables, provenance information becomes inherent rather than added.

For HWML, we don't need to adopt the full Dependent LCF architecture (we're not doing dependent proof refinement), but we can learn from how RedPRL structures metavariable creation:

1. **Every metavar has a judgment** - not just a type, but a full goal
2. **Creation order matters** - store metavars in order, not in a HashMap
3. **Dependencies are first-class** - track what depends on what
4. **Errors come from structure** - the telescope tells you what went wrong

**Next Step for HWML**: Implement Phase 1 (add `created_at` and `origin` to `MetaEntry`) using the lessons from how RedPRL structures its refinement state.
