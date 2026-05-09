# Beneš (2025): Flow-Based Variational Type-Checking for Overloading

**Paper:** "The Simple Essence of Overloading: Making Ad-Hoc Polymorphism More Algebraic with Flow-Based Variational Type-Checking"
**Authors:** Jiří Beneš, Jonathan Immanuel Brachthäuser (University of Tübingen)
**Published:** OOPSLA 2025
**DOI:** https://doi.org/10.1145/3763168
**Artifact:** https://github.com/se-tuebingen/oopsla-2025-artifact-overloading
**Date Analyzed:** 2026-05-06

---

## Executive Summary

Beneš (2025) presents a **flow-based variational framework** for type-directed overload resolution that **eliminates backtracking** during type inference. The key innovation is representing overloaded symbols as **"choices"** (variations) in a choice calculus, then using **algebraic subtyping-style constraint solving** to eliminate invalid choices WITHOUT backtracking the type-checker.

### Key Claim

**"Our approach avoids typical problems of backtracking implementations through type-directed overload resolution with clear phase separation"** (from artifact README).

This directly addresses the question from our previous research: **Can we avoid interleaving type-checking and parsing where type-based disambiguation waits for types but does NOT backtrack once type-checking starts?**

---

## 1. Core Conceptual Framework

### 1.1 Variational Calculus

The paper extends λ-calculus with a **choice calculus**:

```
e ::= x | λx.e | e₁ e₂ | choice^a { e₁, e₂, ... }
```

**Key idea:** An overloaded symbol like `+` is desugared to:

```ocaml
(+) = choice^a {
  case Int:    λ(x:Int)    λ(y:Int)    → (primAdd x y : Int),
  case Float:  λ(x:Float)  λ(y:Float)  → (primAddF x y : Float),
  case String: λ(x:String) λ(y:String) → (primConcat x y : String)
}
```

The choice is **labeled** with dimension `a` (the overload site).


### 1.2 Variational Types

Types are also variational:

```
τ ::= α | τ₁ → τ₂ | Int | String | Float | choice^a { τ₁, τ₂, ... }
```

**Example:** The type of the overloaded `+` above is:

```
choice^a {
  case Int:    Int → Int → Int,
  case Float:  Float → Float → Float,
  case String: String → String → String
}
```

### 1.3 "Worlds" (Configurations)

A **world** (or configuration) is a **selection** from each choice dimension. Formally: `w : Dim → Case`

**Example worlds:**
- `w₁ = { a ↦ Int }`     // Use Int version of `+`
- `w₂ = { a ↦ Float }`   // Use Float version of `+`
- `w₃ = { a ↦ String }`  // Use String version of `+`

A program is **valid in world w** if selecting all `w(d)` branches type-checks.

---

## 2. The Crucial Innovation: No Backtracking

### 2.1 Traditional Backtracking Approach (BAD)

```rust
fn resolve_overload_backtracking(symbol: Symbol, context: TypeCtx) -> Type {
    for definition in symbol.definitions() {
        let checkpoint = context.checkpoint();

        match typecheck_with_definition(definition, context) {
            Ok(ty) => return ty,  // Success!
            Err(_) => {
                context.restore(checkpoint);  // BACKTRACK
                continue;  // Try next definition
            }
        }
    }

    error!("No valid overload")
}
```

**Problems:**
- ❌ Exponential: tries all combinations
- ❌ Must save/restore type environment
- ❌ Poor error messages (which attempt to report?)
- ❌ Not compositional: nested overloads interact badly

### 2.2 Variational Approach (GOOD)

```rust
fn resolve_overload_variational(symbol: Symbol, context: TypeCtx) -> Type {
    // Phase 1: Generate constraints for ALL definitions (in parallel)
    let choice_var = fresh_choice_var();
    let constraints = symbol.definitions().map(|def| {
        generate_constraints_for(def, choice_var)
    });

    // Phase 2: Solve constraints (NO backtracking!)
    let bounds = solve_constraints(constraints)?;

    // Phase 3: Extract valid worlds
    let valid_worlds = extract_worlds(bounds)?;

    // Phase 4: Require EXACTLY ONE valid world
    match valid_worlds.len() {
        0 => error!("No valid overload"),
        1 => Ok(specialize(bounds, valid_worlds[0])),
        _ => error!("Ambiguous overload")
    }
}
```

**Key difference:** ALL definitions are type-checked ONCE in "variational mode", producing a choice-aware type. Then constraint solving PRUNES invalid worlds.

---

## 3. Flow-Based Algebraic Subtyping

The paper combines variational typing with **algebraic subtyping** (Dolan & Mycroft 2017).

### 3.1 Polar Types

Types are classified as:
- **Positive** (outputs): produced by terms
- **Negative** (inputs): consumed by terms

**Why?** This enables **flow-based constraint solving** similar to Flow.js:

```
τ⁺ <: τ⁻
```

Constraint: "positive type τ⁺ flows into negative type τ⁻"

### 3.2 Biunification

**Not traditional unification!** Instead: **subtyping constraints** accumulated in **upper and lower bounds**:

```rust
struct TypeBounds {
    lower: Set<Type>,  // τ₁ <: α, τ₂ <: α, ... (things that flow INTO α)
    upper: Set<Type>,  // α <: τ₃, α <: τ₄, ... (things α flows INTO)
}
```

**Example:**

```
x + y  where  typeof(x) = α,  typeof(y) = β

Choice constraint:
  choice^a {
    Int → Int → Int,
    Float → Float → Float,
    String → String → String
  } <: α → β → γ
```

Becomes three disjuncts (one per world):

```
World a=Int:
  (Int → Int → Int) <: (α → β → γ)
  ⟹  α <: Int,  β <: Int,  Int <: γ

World a=Float:
  (Float → Float → Float) <: (α → β → γ)
  ⟹  α <: Float,  β <: Float,  Float <: γ

World a=String:
  (String → String → String) <: (α → β → γ)
  ⟹  α <: String,  β <: String,  String <: γ
```

**Crucially:** The solver doesn't TRY each world sequentially. It maintains all three sets of bounds SIMULTANEOUSLY, then prunes inconsistent worlds.

---

## 4. Key Algorithm: Variational Constraint Solving

From the artifact implementation (`src/solve.rs`):

### 4.1 Constraint Representation

```rust
enum Constraint {
    // Subtyping constraint (with choice dimension)
    Sub { lower: Type, upper: Type, dim: Option<ChoiceDim> },

    // Instantiation (generalize/instantiate type variables)
    Inst { ty: Type, pol: Polarity },
}

// Choice dimension = which overload site
type ChoiceDim = String;  // e.g., "a₁", "a₂", ...

// Polarity = direction of information flow
enum Polarity { Pos, Neg }
```

### 4.2 Core Solving Loop

```rust
fn solve(constraints: Vec<Constraint>) -> Result<Bounds> {
    let mut bounds = Bounds::empty();

    for constraint in constraints {
        match constraint {
            Sub { lower, upper, dim } => {
                // Add bound, potentially in specific world
                add_bound(&mut bounds, lower, upper, dim)?;
            }
            Inst { ty, pol } => {
                // Instantiate type variable
                instantiate(&mut bounds, ty, pol)?;
            }
        }
    }

    // Check consistency: for each world, check bounds are satisfiable
    prune_inconsistent_worlds(&mut bounds)?;

    Ok(bounds)
}
```
### 4.3 World Pruning

The key optimization: **detect contradictions early**

```rust
fn prune_inconsistent_worlds(bounds: &mut Bounds) -> Result<()> {
    for (var, var_bounds) in &bounds.vars {
        for world in all_worlds() {
            // Get bounds in this specific world
            let lower_in_world = var_bounds.lower.in_world(world);
            let upper_in_world = var_bounds.upper.in_world(world);

            // Check: ∃ τ₁ ∈ lower, τ₂ ∈ upper s.t. τ₁ <: τ₂ is FALSE?
            if !is_consistent(lower_in_world, upper_in_world) {
                // This world is IMPOSSIBLE, remove it
                bounds.remove_world(world);
            }
        }
    }

    Ok(())
}
```

**Example:** If world `a=Int` requires `α <: Int` AND `String <: α`, this is impossible → prune `a=Int`.

---

## 5. Connection to SPPF + Constraints (HWML's Need)

### 5.1 Parallel with Parse Ambiguity

| **Concept** | **Beneš (Overloading)** | **SPPF (Parsing)** |
|-------------|-------------------------|---------------------|
| **Ambiguity source** | Multiple overload definitions | Multiple parse trees |
| **Representation** | `choice^a { def₁, def₂, ... }` | SPPF ambiguity node |
| **Constraint gen** | Type constraints per definition | Constraints per parse alternative |
| **Resolution** | Prune worlds via bound inconsistency | Prune parse trees via satisfiability |
| **Output** | Unique world (or error) | Unique parse tree (or error) |

### 5.2 Unified Framework for HWML

```rust
enum Constraint {
    // Traditional: unify two types
    Unify(Type, Type),

    // Suspension: wait for type variable
    Suspended {
        blocked_on: Vec<MetaVar>,
        resume: Box<dyn FnOnce(Substitution) -> Constraint>,
    },

    // NEW (from Beneš): multiple alternatives
    Choice {
        dimension: ChoiceDim,    // Which ambiguity site?
        alternatives: Vec<ConstraintSet>,  // One per alternative
        source: ChoiceSource,
    },
}

enum ChoiceSource {
    ParseAmbiguity(SPPFNode),    // From SPPF
    Overloading(Symbol),         // From type-directed overload
    DotNotation(Expr, Field),    // From universal dot notation
}
```

### 5.3 Integrated Solving

```rust
fn solve_constraints_unified(cs: ConstraintSet) -> Result<Substitution> {
    let mut subst = Substitution::empty();
    let mut suspended = Vec::new();
    let mut choices = Vec::new();  // NEW: from Beneš

    for c in cs {
        match c {
            Unify(t1, t2) => {
                subst.compose(unify(t1, t2)?);
            }

            Suspended { blocked_on, resume } => {
                if blocked_on.all_known_in(&subst) {
                    let resumed = resume(subst.clone());
                    solve_constraint(resumed)?;
                } else {
                    suspended.push(c);
                }
            }

            // NEW: Handle choices via Beneš-style pruning
            Choice { dimension, alternatives, source } => {
                // Generate bounds for each alternative
                let mut valid_alts = Vec::new();

                for alt_constraints in alternatives {
                    let alt_bounds = solve_as_world(alt_constraints, dimension)?;

                    // Check if this world is consistent
                    if is_world_consistent(&alt_bounds) {
                        valid_alts.push(alt_bounds);
                    }
                }

                match valid_alts.len() {
                    0 => return Err(NoValidAlternative(source)),
                    1 => {
                        // Unique solution! Commit to this world
                        subst.compose(specialize(valid_alts[0], dimension)?);
                    }
                    _ => {
                        // Still ambiguous, keep choice
                        choices.push(Choice { dimension, alternatives: valid_alts, source });
                    }
                }
            }
        }
    }

    // Fixpoint: resume suspended, prune choices
    if suspended.is_empty() && choices.is_empty() {
        Ok(subst)
    } else if made_progress() {
        solve_constraints_unified(suspended + choices)
    } else {
        Err(StillAmbiguous { suspended, choices })
    }
}
```

---

## 6. Key Insights for HWML

### 6.1 What Beneš Adds to Our Previous Research

Our previous SPPF research showed:
- ✅ Can separate parse-level backtracking from type-checker backtracking
- ✅ Use SPPF to represent all parses compactly
- ✅ Prune SPPF via satisfiability checking

**Beneš shows HOW to do the constraint solving:**
- ✅ Use **flow-based biunification** instead of traditional unification
- ✅ Maintain **all worlds simultaneously** via labeled bounds
- ✅ **Incrementally prune** worlds as inconsistencies emerge
- ✅ **No backtracking** in the constraint solver!

### 6.2 Specific Techniques for HWML

**1. Adopt Flow-Based Biunification**

Replace traditional Hindley-Milner unification with algebraic subtyping-style bounds:
- Accumulate lower bounds: `τ₁ <: α, τ₂ <: α, ...`
- Accumulate upper bounds: `α <: τ₃, α <: τ₄, ...`
- Check consistency: `∀ (τ_l ∈ lower, τ_u ∈ upper) : τ_l <: τ_u`

**2. Choice Constraints for SPPF Ambiguities**

```rust
// Parse produces SPPF with ambiguity
let sppf = parse(source);

for amb_node in sppf.ambiguous_nodes() {
    // Generate choice constraint
    let alternatives = amb_node.children().map(|child| {
        elaborate_to_constraints(child)
    });

    emit_constraint(Choice {
        dimension: amb_node.id(),
        alternatives,
        source: ParseAmbiguity(amb_node),
    });
}
```

**3. Incremental World Pruning**

Don't wait until all constraints are gathered! Prune eagerly:

```rust
fn add_bound(bounds: &mut Bounds, lower: Type, upper: Type, dim: Option<ChoiceDim>) {
    bounds.add_raw(lower, upper, dim);

    // IMMEDIATELY check for contradictions
    if let Some(world) = find_inconsistent_world(bounds) {
        bounds.remove_world(world);

        // Error if no worlds left!
        if bounds.num_worlds() == 0 {
            return Err("No consistent parse/overload resolution");
        }
    }
}
```

**4. Unify Suspended and Choice Constraints**

Both are forms of "delayed decision-making":
- **Suspended:** Wait for type variable to be known
- **Choice:** Wait for other constraints to prune alternatives

```rust
fn make_progress(suspended: &Vec<Constraint>, choices: &Vec<Constraint>) -> bool {
    // Resume any suspended constraints whose blockers are now known
    let resumed = suspended.retain(|s| !s.blocked_on.all_known());

    // Prune any choice constraints whose alternatives are now invalid
    let pruned = choices.iter_mut().map(|c| c.prune_invalid_worlds());

    resumed.len() > 0 || pruned.any(|p| p)
}
```

---

### 6.3 Performance Characteristics

From the Beneš artifact benchmarks (Section 5 of paper):

**Scalability:** Time complexity is **O(N × M)** where:
- N = number of type variables
- M = number of choice dimensions (overload sites)

**Not exponential!** Because:
- Worlds are pruned incrementally
- No backtracking
- Constraint solving is polynomial (algebraic subtyping)

**Compared to Swift's backtracking:**
- Swift: exponential in number of nested overloads
- Beneš: polynomial

---

## 7. Practical Implementation Notes

### 7.1 From the Artifact

The artifact (`oopsla-2025-artifact-overloading`) demonstrates:

**Website Interface:** Interactive WASM-based playground showing:
- Input: Variational Core program
- Output: Constraints, bounds, worlds, resolution result

**Key Files:**
- `src/constraints.rs` - Constraint generation
- `src/solve.rs` - Variational constraint solver with world pruning
- `src/types.rs` - Variational types representation
- `examples/` - All paper examples plus benchmarks

**Example Run:**

```bash
$ nix run .#native -- examples/sec-1-1-1.over

Constraints:
  (Int, Int) => Int <:^a₁ over_a_0
  (String, String) => String <:^a₂ over_a_0
  over_a_0 <: (Int, Int) => app_1

Bounds:
  Int^a₁, String^a₂ <: app_1 <: ∅
  (Int, Int) => Int^a₁, (String, String) => String^a₂ <: over_a_0 <: (Int, Int) => app_1

Worlds: One
Solutions: a₁
```

**Interpretation:**
- Overload `a` has two alternatives (a₁=Int, a₂=String)
- Given context `(Int, Int) =>`, only world `a₁` is consistent
- Resolution: `a = a₁` (Int version)

### 7.2 Complexity Comparison

| **Approach** | **Constraint Gen** | **Solving** | **Total** |
|--------------|-------------------|-------------|-----------|
| **Backtracking** | O(N) per attempt | O(N²) per attempt | O(2^M × N²) |
| **Beneš Variational** | O(M × N) | O(N² × M) | **O(M × N²)** |

Where M = #overload sites, N = #type variables.

**Crucially:** Beneš is **polynomial** in M, not exponential!

---

## 8. Application to HWML's Specific Needs

### 8.1 Mixfix + Overloading

**Scenario:** Mixfix operator `if_then_else_` with overloaded condition type

```haskell
if_then_else_ : Bool → α → α → α   // Boolean condition
if_then_else_ : Int → α → α → α    // Integer (0 = false)
```

**Traditional:** Backtrack between the two definitions.

**Beneš approach:**

```rust
let cond_type = fresh_var();
let branch_type = fresh_var();

// Choice constraint
Choice {
    dimension: "if_then_else_cond",
    alternatives: [
        [cond_type <: Bool, branch_type <: α],    // World 1
        [cond_type <: Int, branch_type <: α],     // World 2
    ],
    source: Overloading("if_then_else_"),
}

// Context provides: cond_type = typeof(condition_expr)
// If condition_expr : String, both worlds pruned → error
// If condition_expr : Bool, World 2 pruned → use World 1
```

### 8.2 Precedence Ambiguity

**Scenario:** `a * b / c` where `*` and `/` have incomparable precedence

**SPPF:** Two alternatives
1. `(a * b) / c`
2. `a * (b / c)`

**Choice constraint:**

```rust
Choice {
    dimension: "prec_multiply_divide",
    alternatives: [
        elaborate((a * b) / c),  // Left-associative
        elaborate(a * (b / c)),  // Right-associative
    ],
    source: ParseAmbiguity(sppf_node),
}
```

If `a : Int, b : Int, c : Int`:
- Both worlds consistent → **still ambiguous!**
- Report to user: "Ambiguous precedence, please parenthesize"

If `a : Matrix, b : Scalar, c : Matrix`:
- World 1: `(Matrix * Scalar) / Matrix` → type error
- World 2: `Matrix * (Scalar / Matrix)` → type error
- **No valid worlds** → different error message

---

## 9. Comparison with Related Work

### 9.1 vs. Frozen Constraints (Scherer et al. 2021)

**Similarities:**
- Both avoid backtracking
- Both suspend decisions

**Differences:**
- Frozen: Suspend SINGLE constraint until variable known
- Beneš: Maintain MULTIPLE worlds, prune inconsistent ones

**Beneš advantage:** Handles disjunction (multiple overloads) naturally.

### 9.2 vs. Algebraic Subtyping (Dolan & Mycroft 2017)

**Beneš builds on algebraic subtyping:**
- Adds: **choice dimensions** for overloading
- Adds: **world pruning** for resolution
- Keeps: **bi-unification**, **polarity**, **biunification**

**Key extension:** Dolan & Mycroft don't handle ad-hoc polymorphism (overloading).

### 9.3 vs. Type Classes (Haskell)

**Type classes:** Resolve at CALL SITE based on argument types

**Overloading (Beneš):** Resolve at DEFINITION SITE based on ALL constraints

**Example:**
```haskell
-- Haskell type classes
class Show a where
  show : a → String

instance Show Int where ...
instance Show Bool where ...

f x = show x  -- Resolved at call site: which Show instance?
```

```ocaml
(* Overloading (Beneš) *)
show : Int → String
show : Bool → String

f x = show x  -- Resolved at definition site: which version of show?
```

**Key difference:** Type classes **defer** resolution (runtime dictionary passing). Beneš overloading **resolves early** (compile-time monomorphization).

---

## 10. Limitations and Open Questions

### 10.1 What Beneš Does NOT Solve

**1. Parse Ambiguity**
The paper focuses on **overloading**, not general parsing. We must still:
- Integrate with SPPF (our previous research)
- Handle mixfix operator precedence (Danielsson-Norell)
- Combine parse-level and type-level choices

**2. Principal Types**
Variational typing **loses principal types** in the traditional sense. Instead:
- **Principal bounds** (most general lower/upper bounds)
- **Unique world** (if resolution succeeds)

**3. Error Messages**
The paper briefly mentions error messages but doesn't deeply address:
- How to explain which worlds were pruned and why
- How to suggest fixes when no worlds are valid
- How to handle "still ambiguous" cases

**NOTE:** See Section 14 below for an in-depth analysis challenging the assumption that variational/choice-based systems produce poor error messages.

### 10.2 Integration Challenges for HWML

**1. Mixing HM and Algebraic Subtyping**
- HWML currently uses Hindley-Milner unification
- Beneš uses algebraic subtyping (biunification)
- Can we hybrid: HM for most code, subtyping only for overloads?

**2. Dependent Types**
- Beneš extends to simple dependent types (Section 4.5 of paper)
- But HWML has richer dependence
- How do choices interact with universe levels, refinements?

**3. Incremental Compilation**
- World pruning is global (requires all constraints)
- How to make this incremental for IDE use?
- Can we cache world-pruning results across edits?

---

## 11. Conclusion: Roadmap for HWML

### 11.1 Short-Term (Prototype)

**Goal:** Demonstrate variational type-checking for simple overloading

**Tasks:**
1. Implement `Choice` constraint type in constraint solver
2. Extend constraint generation to emit `Choice` for ambiguities
3. Add basic world pruning (consistency checking)
4. Test with simple overload examples (like Beneš examples)

**Success criterion:** Can resolve `+` for `Int` vs `Float` without backtracking.

### 11.2 Medium-Term (SPPF Integration)

**Goal:** Connect parse-level ambiguity (SPPF) to type-level resolution (Beneš)

**Tasks:**
1. Parse to SPPF (using GLL parser)
2. For each SPPF ambiguity node, emit `Choice` constraint
3. Unify suspended constraints (from mixfix) with choice constraints
4. Test with precedence-ambiguous expressions

**Success criterion:** Can disambiguate `a * b / c` based on types.

### 11.3 Long-Term (Production)

**Goal:** Full variational type-checking with all HWML features

**Tasks:**
1. Extend to dependent types + choices
2. Incremental world pruning for IDE
3. Rich error messages showing pruned worlds
4. Performance optimization (memoization, caching)

**Success criterion:** Fast, backtracking-free type-checking for real HWML programs.

---

## 12. Key Takeaways for HWML

### 12.1 Direct Applicability

✅ **YES, Beneš directly solves our problem:**
- Avoid type-checker backtracking ✓
- Maintain multiple alternatives simultaneously ✓
- Prune inconsistent alternatives incrementally ✓
- Polynomial complexity (not exponential) ✓

✅ **Perfect fit for SPPF + constraints architecture:**
- SPPF ambiguity node → `Choice` constraint with parse alternatives
- Type-directed overload → `Choice` constraint with overload alternatives
- Suspended elaboration → `Suspended` constraint (orthogonal to `Choice`)
- Unified solver handles both!

### 12.2 Recommended Approach

**Phase 1:** Simple overloading (Beneš-style)
- Implement variational types
- Add choice constraints
- Basic world pruning

**Phase 2:** SPPF integration
- Parse ambiguities as choices
- Connect to type-checker
- Prune parse alternatives via types

**Phase 3:** Full integration
- Mixfix + overloading + dot notation
- All three use same `Choice` mechanism
- All pruned via same bound-checking logic

### 12.3 Why This Is Better Than Backtracking

| **Aspect** | **Backtracking** | **Beneš Variational** |
|------------|------------------|----------------------|
| **Type-checker state** | Save/restore | Never backtracks |
| **Complexity** | O(2^M × N²) | O(M × N²) |
| **Compositionality** | Poor (nested choices explode) | Good (choices compose) |
| **Error messages** | Confusing (which attempt?) | Clear (show all pruned worlds) |
| **Incrementality** | Hard (diverging states) | Easy (stable bounds) |

---

## 13. References

### 13.1 Primary Source

Jiří Beneš and Jonathan Immanuel Brachthäuser. 2025.
**"The Simple Essence of Overloading: Making Ad-Hoc Polymorphism More Algebraic with Flow-Based Variational Type-Checking"**
*Proc. ACM Program. Lang.* 9, OOPSLA2, Article 390 (October 2025), 27 pages.
DOI: https://doi.org/10.1145/3763168

**Artifact:**
GitHub: https://github.com/se-tuebingen/oopsla-2025-artifact-overloading
Zenodo: (see README for DOI)

### 13.2 Foundations

**Choice Calculus:**
- Martin Erwig and Eric Walkingshaw. 2011.
  **"The choice calculus: A representation for software variation"**
  *ACM Trans. Softw. Eng. Methodol.* 21, 1 (2011), 6:1–6:27.

**Variational Type Checking:**
- Sheng Chen, Martin Erwig, and Eric Walkingshaw. 2014.
  **"Extending type inference to variational programs"**
  *ACM Trans. Program. Lang. Syst.* 36, 1 (2014), Article 1, 54 pages.

**Algebraic Subtyping:**
- Stephen Dolan and Alan Mycroft. 2017.
  **"Polymorphism, subtyping, and type inference in MLsub"**
  *POPL 2017*, 60–72.

### 13.3 Related Work (from Our Research)

**Frozen Constraints:**
- Gabriel Scherer, Didier Rémy, and Christophe Raffalli. 2021.
  **"A fresh look at ML type inference with frozen type variables"**
  *ML Workshop 2021*.

**SPPF + Disambiguation:**
- Jan Rekers and Wilco Koorn. 1994.
  **"Using filters for disambiguation in scannerless generalized LR parsing"**
  *Software—Practice & Experience* 24, 10 (1994), 1037–1060.

- Elizabeth Scott and Adrian Johnstone. 2010.
  **"GLL parsing"**
  *Electronic Notes in Theoretical Computer Science* 253, 7 (2010), 177–189.

### 13.4 Error Messages and Comparison

**On variational error quality:**
- Chen et al. (2014): Error-tolerant type system for variational programs
- Chen, Erwig, Smeltzer (2016): "Exploiting Diversity" - 25% improvement
- Erwig et al. (2012): Counter-factual typing for change suggestions
- Meredith (2018): "Better Flow Error Messages" - Flow Blog
- Alpert (2018): "Type Errors Need Stacks" - sophiebits.com
- Pavlinovic et al. (2024): "Getting into the Flow" - arXiv:2402.12637

**On no-ambiguity approaches:**
- Rust error codes documentation - E0282 analysis
- Elm compiler releases: 0.9, 0.15.1, 0.16, 0.19.1 - error message improvements
- GHC Haskell documentation: "Ambiguous types and the ambiguity check"
- TypeScript handbook: "Understanding Errors"
- Czaplicki (2020): "New Elm Release Helps Developers Learn Syntax" - InfoQ

### 13.5 HWML Research Context

This research builds on our previous wiki documents:
- `mixfix-type-directed-parsing.md` - Survey of mixfix, overloading, dot notation
- `mixfix-backtracking-free-parsing.md` - Analysis of Danielsson-Norell parsing
- `parse-forest-type-disambiguation.md` - SPPF + constraint pruning architecture

---

**Document Status:** ✅ Complete deep dive + comprehensive analysis + practical implementation guide
**Extended:** 2026-05-06 (added Section 14: Error Messages in Variational Systems)
**Extended:** 2026-05-06 (added Section 15: No-Ambiguity vs Variational Comparison)
**Extended:** 2026-05-07 (added Section 16: Critical Analysis - Are Variational Constraints Backtracking?)
**Extended:** 2026-05-07 (added Section 17: Practical Implementation + SPPF Integration)

---

## 14. Error Messages in Variational Type-Checking: Challenging the "Horrible" Assumption

### 14.1 The Common Assumption (WRONG!)

**Conventional wisdom:** "When things are ambiguous, error messages are horrible."

**Why this assumption exists:**
- Traditional backtracking systems try multiple alternatives, fail on most, then report ONE failure
- No indication of which alternatives were tried or why they failed
- Error location may be far from the actual source (nested inference)
- "No matching overload" messages that don't explain what went wrong

**Example of BAD traditional error (C#):**
```
error CS0121: The call is ambiguous between the following methods or properties:
  'Method1(int, A)'
  'Method2(float, B)'
```

**What's missing:** WHY are both ambiguous? What types did the arguments have? What could I change?

---

### 14.2 Variational Type-Checking IMPROVES Error Messages!

**Key insight from research:** Variational/choice-based systems can produce **BETTER** error messages than backtracking because they maintain **ALL** alternatives simultaneously and can show **exactly** what went wrong with each.

#### Evidence from Literature

**1. Chen et al. (2014): "Extending Type Inference to Variational Programs"**
- **Problem solved:** Traditional approach type-checks each variant separately → errors reported in terms of specific variants, not source code
- **Variational solution:** Type-check ALL variants simultaneously → errors localized to the CHOICE that introduced the problem
- **Key quote:** "Our extended type system supports locating ill-typed variants and the incremental development of variational programs"

**2. Chen, Erwig, & Smeltzer (2016): "Exploiting Diversity in Type Checkers for Better Error Messages"**
- **Result:** Combining lazy typing (variational approach) with traditional type-checking improved accuracy by **25%/20%** over either approach alone
- **Why:** Different approaches excel in different situations; variational typing catches errors traditional systems miss (premature error commitment)

**3. Erwig et al. (2012): "Counter-Factual Typing"**
- **Approach:** Use choices to represent hypothetical fixes: `choice { existing_code, potential_fix }`
- **Output:** Comprehensive set of change suggestions, each of which COULD fix the type error
- **Application:** Instead of saying "type error here", say "if you changed X to Y, the error would be fixed"

**4. Walkingshaw et al. (2016): "Variational Programming Calculus"**
- **Key advantage:** "Opportunities for improved error messages" (cited as primary motivation)
- **Mechanism:** Named choices provide dimension polymorphism → errors can reference the CHOICE DIMENSION, not just locations

---

### 14.3 Concrete Advantages for Error Messages

#### Advantage 1: Show ALL Invalid Worlds (Not Just One)

**Traditional backtracking:**
```
error: No matching overload for '+' with arguments (x, y)
  tried: Int + Int     // failed
  tried: Float + Float // failed
  tried: String + String // gave up here
```

**Variational (Beneš-style):**
```
error: No valid world for choice 'plus_operator' at line 42

Attempted worlds:
  World {plus=Int}:
    ✗ Pruned because: x : String <: Int failed
    Required: x flows into Int
    Actual: x has lower bound String

  World {plus=Float}:
    ✗ Pruned because: x : String <: Float failed
    Required: x flows into Float
    Actual: x has lower bound String

  World {plus=String}:
    ✗ Pruned because: y : Int <: String failed
    Required: y flows into String
    Actual: y has lower bound Int

Suggestion: x and y must have the same type.
  Consider: annotate x or y to clarify intent
```

**Key difference:** Shows **why each alternative failed** with precise constraint information.

---

#### Advantage 2: Pinpoint the DIVERGENCE Point

**Problem with traditional systems:** Error reported far from source

**Variational solution:** Track when worlds diverge

```rust
fn explain_ambiguity(choice: ChoiceConstraint) -> ErrorMessage {
    let worlds = choice.valid_worlds();

    match worlds.len() {
        0 => {
            // No valid worlds: show WHY each was pruned
            let reasons = choice.alternatives.map(|alt| {
                let pruned_at = find_first_inconsistency(alt);
                format!("World {}: pruned at {} because {}",
                    alt.name, pruned_at.location, pruned_at.reason)
            });

            ErrorMessage::NoValidWorlds {
                choice_location: choice.source_location,
                reasons,
                suggestion: suggest_fix_from_patterns(reasons),
            }
        }

        1 => {
            // Unique world: success! (no error)
            Ok(worlds[0])
        }

        _ => {
            // Multiple valid worlds: show DIFF between them
            let diff = compute_world_diff(worlds);

            ErrorMessage::StillAmbiguous {
                choice_location: choice.source_location,
                valid_worlds: worlds,
                divergence_points: diff.where_they_differ,
                suggestion: suggest_disambiguation(diff),
            }
        }
    }
}
```

**Example output:**

```
error: Ambiguous choice 'operator_precedence' at line 15

Expression: a * b / c

Valid interpretations:
  1. (a * b) / c  :  Int
  2. a * (b / c)  :  Int

These differ only in:
  - Associativity of * and /
  - Evaluation order (affects side effects)

Suggestion: Add explicit parentheses to disambiguate
```

---

#### Advantage 3: Flow-Based Explanations (Human-Intuitive)

**Beneš uses flow-based constraints:** `τ₁ <: α <: τ₂` means "data flows from τ₁ through α to τ₂"

**Why this helps errors:** Programmers already reason about data flow!

**Traditional error (Haskell-like):**
```
Couldn't match expected type 'Int' with actual type 'String'
  In the expression: foo x
  In the equation for 'bar': bar x = baz (foo x)
```

**Flow-based error (Beneš-style):**
```
Type flow violation at line 23: foo x

Data flow path:
  x : String              (line 22, parameter)
    ↓
  foo : String → Int      (line 10, definition)
    ↓
  result : Int            (inferred from foo's return)
    ↓
  baz : String → Bool     (line 15, expected String)
    ↗ CONFLICT: Int cannot flow into String

Suggestion:
  - Either change baz to accept Int, or
  - Change foo to return String
```

**Why better:** Shows the **CHAIN** of inference, not just the mismatch point.

---

### 14.4 Research-Backed Error Message Improvements

#### From Flow.js Team (2018-2023)

**Problem:** Flow's structural typing + inference made errors inscrutable

**Solutions implemented:**
1. **Error stacks** showing inference path (Sophie Alpert, 2018)
   - "Here's the 20 steps I took to get here"
   - Allows user to add annotation in the MIDDLE to cut the chain

2. **Flow-based error format** (Flow 0.66+, 2018)
   - Redesigned to show data flow, not constraint solving internals
   - Fixed error locations (many errors pointed to wrong place)

3. **Local type inference** (2023)
   - Require more annotations at module boundaries
   - **Result:** More localized errors, easier to understand

**Key lesson:** Flow-based + inference can have good errors **IF** designed intentionally.

---

#### From Variational Typing Research (Chen et al. 2014)

**Error-Tolerant Type System for VLC:**

**Problem:** If ANY variant has a type error, traditional approach fails for entire variational expression

**Solution:** Extended type system that CONTINUES even with errors

**Benefits:**
1. **Locate ill-typed variants precisely** (not just "somewhere in this huge expression")
2. **Partial unifiers:** Find types that minimize error count across variants
3. **Incremental development:** Can have some broken variants while fixing others

**Example:**

```ocaml
(* Variational expression with error *)
let x = choice^a {
  case V1: 42,           (* Int *)
  case V2: "hello",      (* String *)
  case V3: true + 1      (* ERROR! *)
}
```

**Traditional error:**
```
Type error in variational expression at line 5
```

**Error-tolerant variational:**
```
Type error in variant V3 only:
  Cannot apply (+) : Int → Int → Int to Bool and Int

Other variants type-check successfully:
  V1: Int
  V2: String

Principal type (excluding V3): choice^a { V1: Int, V2: String }

Suggestion: Fix V3 or remove it from the choice
```

---

### 14.5 Application to HWML: Concrete Error Message Design

#### Scenario 1: Parse Ambiguity (SPPF)

**Code:**
```rust
let result = a * b / c;
```

**SPPF:** Two parse trees due to precedence ambiguity

**Bad traditional error:**
```
error: Ambiguous parse
```

**Good variational error:**
```
error[E0420]: Parse ambiguity at line 3

Expression: a * b / c

Multiple valid parses:
  Parse 1: (a * b) / c
    Type: Int     (if a, b, c : Int)

  Parse 2: a * (b / c)
    Type: Int     (if a, b, c : Int)

Both parses are type-correct, but have different semantics:
  - Parse 1: Multiply first, then divide
  - Parse 2: Divide first, then multiply with result

Suggestion: Add explicit parentheses to clarify intent
  help: (a * b) / c  or  a * (b / c)

Location: main.rs:3:14
```

---

#### Scenario 2: Overload Ambiguity

**Code:**
```hwml
def show : Int → String
def show : Bool → String

def process (x : α) : String =
  show x  // ERROR: which show?
```

**Bad traditional error:**
```
error: Ambiguous overload for 'show'
```

**Good variational error:**
```
error[E0421]: Overload resolution failed at line 5

Call: show x

No valid overload because type variable 'α' is unconstrained:

Available overloads:
  1. show : Int → String
     ✗ Would require: α = Int

  2. show : Bool → String
     ✗ Would require: α = Bool

Neither overload can be selected without knowing the type of 'α'.

Suggestion: Add a type constraint or annotation
  help: def process (x : Int) : String = show x
  help: def process (x : Bool) : String = show x

Location: main.hwml:5:3
```

---

#### Scenario 3: Parse Disambiguation via Types (SUCCESS!)

**Code:**
```hwml
// Matrix type has different precedence needs
def (*) : Matrix → Scalar → Matrix
def (/) : Matrix → Matrix → Matrix

let m1 : Matrix = ...
let s : Scalar = ...
let m2 : Matrix = ...

let result = m1 * s / m2  // Ambiguous parse, but...
```

**SPPF:** Two alternatives
1. `(m1 * s) / m2`  : Matrix
2. `m1 * (s / m2)`  : type error (Scalar / Matrix invalid)

**Good variational success message:**
```
info[I0100]: Parse disambiguation via types

Expression: m1 * s / m2  (line 9)

Initial parse ambiguity resolved by type constraints:

Parse 1: (m1 * s) / m2
  ✓ Type-checks: Matrix
  Flow: Matrix * Scalar → Matrix, Matrix / Matrix → Matrix

Parse 2: m1 * (s / m2)
  ✗ Pruned: No overload for (/) : Scalar → Matrix → _

Resolved to: Parse 1

This was disambiguated automatically based on types.
No action needed.
```

**Why this is GREAT:** User sees disambiguation happened, understands why, but doesn't need to act.

---

#### Scenario 4: Multiple Errors Across Worlds

**Code:**
```hwml
def add : Int → Int → Int
def add : String → String → String

let x = if condition then 42 else "hello"
let y = if condition then 99 else "world"

let result = add x y
```

**Good variational error:**
```
error[E0422]: Type inconsistency across worlds

Call: add x y  (line 7)

World analysis:
  World {condition=true}:
    x : Int, y : Int
    ✓ Valid: add : Int → Int → Int
    Result: Int

  World {condition=false}:
    x : String, y : String
    ✓ Valid: add : String → String → String
    Result: String

PROBLEM: Result type varies between worlds!
  - In world {condition=true}: Int
  - In world {condition=false}: String

HWML requires a single, deterministic type for each expression.

Suggestion: Refactor to make types consistent across branches
  help: Ensure x and y have the same type in all branches
  help: Or use explicit branching:
        if condition then add_int x y else add_string x y

Location: main.hwml:7:14
```

**Key insight:** Shows that EACH world is valid individually, but they're incompatible when composed.

---

### 14.6 Implementation Sketch for HWML

```rust
pub struct ErrorReporter {
    choice_constraints: Vec<ChoiceConstraint>,
    world_prune_history: Vec<PruneEvent>,
}

pub enum PruneEvent {
    WorldPruned {
        world: World,
        choice_dimension: ChoiceDim,
        reason: PruneReason,
        location: SourceLocation,
    },
    WorldResolved {
        choice_dimension: ChoiceDim,
        selected_world: World,
        alternatives_pruned: Vec<(World, PruneReason)>,
    },
}

pub enum PruneReason {
    BoundInconsistency {
        var: TypeVar,
        lower_bound: Type,
        upper_bound: Type,
        conflict: String,  // "Int <: String failed"
    },
    NoMatchingOverload {
        symbol: Symbol,
        required_type: Type,
        available: Vec<Type>,
    },
    ParseInvalid {
        sppf_node: SPPFNodeId,
        syntax_error: String,
    },
}

impl ErrorReporter {
    pub fn report_choice_resolution_failure(
        &self,
        choice: &ChoiceConstraint,
    ) -> ErrorMessage {
        let pruned = self.world_prune_history
            .iter()
            .filter(|e| e.choice_dimension == choice.dimension)
            .collect();

        match choice.valid_worlds().len() {
            0 => self.report_no_valid_worlds(choice, pruned),
            1 => Ok(()),  // Success!
            _ => self.report_still_ambiguous(choice),
        }
    }

    fn report_no_valid_worlds(
        &self,
        choice: &ChoiceConstraint,
        prune_events: Vec<&PruneEvent>,
    ) -> ErrorMessage {
        let mut msg = ErrorMessage::new(ErrorCode::E0420);

        msg.set_title(format!(
            "{} resolution failed",
            choice.source.kind()  // "Parse" | "Overload" | "Dot notation"
        ));

        msg.set_location(choice.source_location);

        // Show each alternative and WHY it was pruned
        for (alt, event) in choice.alternatives.zip(prune_events) {
            msg.add_world_failure(
                alt.name,
                event.reason.explain(),
                event.reason.suggest_fix(),
            );
        }

        // Synthesize high-level suggestion from patterns
        msg.add_suggestion(self.infer_fix_from_patterns(prune_events));

        msg
    }

    fn infer_fix_from_patterns(&self, events: Vec<&PruneEvent>) -> String {
        // Pattern matching on common error patterns

        // Pattern 1: All worlds pruned for same variable
        if let Some(var) = events.iter().all_same_var() {
            return format!(
                "Add a type annotation for '{}' to constrain its type",
                var.name
            );
        }

        // Pattern 2: Type mismatch across worlds
        if events.iter().all_type_mismatches() {
            return "Ensure consistent types across all branches".to_string();
        }

        // Pattern 3: Missing overload
        if events.iter().all_no_matching_overload() {
            let required = events[0].extract_required_type();
            return format!(
                "Add an overload for type: {}",
                required.display()
            );
        }

        // Default
        "See individual world failures above for details".to_string()
    }
}
```

---

### 14.7 Comparison: Traditional vs Variational Error Quality

| **Aspect** | **Traditional Backtracking** | **Variational (Beneš + HWML)** |
|------------|----------------------------|--------------------------------|
| **What failed** | Reports one failed attempt | Shows ALL failed alternatives |
| **Why it failed** | Generic "type mismatch" | Precise flow constraint violation |
| **Where it failed** | Often far from source | Tracks exact pruning location |
| **Suggestions** | Rare | Pattern-based, actionable |
| **Ambiguous cases** | "Ambiguous call" | Shows DIFF between valid alternatives |
| **Data flow** | Hidden | Explicit flow path shown |
| **Incremental** | All-or-nothing | Can have partial success |
| **User experience** | Frustrating | Educational |

---

### 14.8 Key References on Error Messages

**Variational Typing for Errors:**
- Chen et al. (2014): "Extending Type Inference to Variational Programs" - ACM TOPLAS
- Chen, Erwig, Smeltzer (2016): "Exploiting Diversity in Type Checkers for Better Error Messages" - J. Visual Languages & Computing

**Flow-Based Error Messages:**
- Meredith (2018): "Better Flow Error Messages for the JavaScript Ecosystem" - Flow Blog
- Alpert (2018): "Type Errors with Inference Need Stacks" - Personal Blog
- Flow Team (2023): "Local Type Inference for Flow" - Flow Blog

**Counter-Factual Typing:**
- Erwig et al. (2012): "Counter-factual typing for debugging type errors" - NSF Award Abstract #1219165

**Error Localization:**
- Pavlinovic et al. (2024): "Getting into the Flow: Towards Better Type Error Messages for Constraint-Based Type Inference" - arXiv:2402.12637

---

### 14.9 Conclusion: Error Messages Are a STRENGTH, Not a Weakness

**THESIS:** Variational/choice-based type-checking can produce **superior** error messages compared to traditional backtracking.

**Why:**
1. ✅ **Maintains all alternatives** → can show why each failed
2. ✅ **Flow-based constraints** → explanations match human intuition (data flow)
3. ✅ **Tracks pruning history** → knows exactly when/why worlds were eliminated
4. ✅ **Computes differences** → for "still ambiguous" cases, shows what differs
5. ✅ **Error tolerance** → can partially succeed, localize errors to specific choices
6. ✅ **Counter-factual reasoning** → can suggest fixes ("if you changed X to Y...")

**For HWML:**
- Parse ambiguity errors: Show all parses, explain differences
- Overload errors: Show which overloads were tried, why each failed
- Type-directed disambiguation: Explain successful disambiguation (educational!)
- Mixed errors: Show per-world analysis



---

## 15. No-Ambiguity Systems vs Variational Systems: Error Message Comparison

### 15.1 The No-Ambiguity Philosophy

**Core principle:** "Reject ambiguity at the language level to simplify error messages."

**Implementations:**
- **Rust:** Requires type annotations when inference is ambiguous
- **Elm:** Designed for friendly errors by avoiding ambiguous constructs
- **Haskell with strict mode:** `AllowAmbiguousTypes` off by default
- **TypeScript (strict mode):** Requires explicit types in many contexts

**Claimed advantage:** "If nothing is ambiguous, error messages are always clear."

---

### 15.2 The Reality: No-Ambiguity ≠ Good Error Messages

**Research finding:** Banning ambiguity does NOT automatically produce good error messages. In fact, it can create NEW error message problems!

#### Problem 1: "Type Annotations Needed" (Rust E0282)

**Scenario:** Inference fails, compiler demands annotation

**Rust error:**
```rust
error[E0282]: type annotations needed
  --> src/main.rs:10:13
   |
10 |     let mut something = des();
   |         ^^^^^^^^^^^^^
11 |     something.value = 100;
   |     --------- type must be known at this point
   |
help: consider giving `something` an explicit type
   |
10 |     let mut something: /* Type */ = des();
   |                      ++++++++++++
```

**Problems:**
- ❌ Doesn't explain WHY type must be known at line 11
- ❌ Suggests adding annotation but doesn't say WHAT type
- ❌ User must manually trace backwards to figure out constraints
- ❌ Error location may be far from the actual source of ambiguity

**What users say:** "Rust can't infer the type but rust-analyzer can show it in the IDE. Why doesn't the compiler just tell me what type to add?"

**Reality:** The compiler COULD infer it with more context, but Rust's inference algorithm is deliberately limited (top-to-bottom, no backtracking) to keep compilation fast and modular.

---

#### Problem 2: Cascading Errors

**Elm's approach:** Reject ambiguity early, require annotations

**Problem:** When ONE missing annotation causes MULTIPLE errors downstream

**Example (from Elm issue #911):**
```elm
Error: Type mismatch between the following types on line 214:

    String

    ()

It is related to the following expression:

    {locals | update = pageUpdate}
```

**User reaction:** "This is completely vague. The fix was related to `locals` but the error gave no indication. I was lucky to remember my recent changes."

**Root cause:** Missing type annotation on `locals.openNoteId : LocalChannel ()` (should have been `LocalChannel Identifier` where `Identifier = String`)

**Why this is ironic:**
- Elm is DESIGNED for friendly error messages
- Elm REQUIRES explicit types to avoid ambiguity
- Yet the error message is STILL confusing!
- Error location is wrong (line 214 vs actual source)

**Lesson:** Banning ambiguity doesn't prevent confusing errors.

---

#### Problem 3: Annotation Burden vs Inference Quality Trade-off

**The dilemma:**

```
More annotations required
        ↓
Less inference power
        ↓
Simpler type checker
        ↓
Better error messages?  ← NOT GUARANTEED!
```

**Rust's design choice:**
- Function signatures: NO inference (must annotate)
- Function bodies: Full inference

**Rationale (from Rust FAQ):**
1. Enforce interface stability
2. Improve code comprehension (no IDE needed)
3. Simplify inference (only one function at a time)

**But:**
- Still get E0282 errors inside function bodies
- Still get confusing "type mismatch" errors
- Still need turbofish syntax: `foo::<T>()`

**Example of turbofish hell:**
```rust
let v: Vec<_> = vec![].iter().collect();  // E0282

// Must write:
let v = vec![].iter().collect::<Vec<i32>>();
// OR:
let v: Vec<i32> = vec![].iter().collect();
```

**User complaint:** "I have to add type annotations everywhere, yet I STILL get ambiguity errors!"

---

#### Problem 4: Haskell's Ambiguity Check Rejects Valid Programs

**Haskell's approach:** Reject ambiguous types at definition site

**Example:**
```haskell
class Foo a where
  bar :: a -> Int

-- ERROR: Ambiguous type
f :: Foo a => Int
f = bar undefined
```

**Error:**
```
Could not deduce (Foo a0) arising from a use of 'bar'
from the context: Foo a
The type variable 'a0' is ambiguous
```

**Why rejected:** "There can be no legal calls to `f`"

**But wait:** With `-XTypeApplications`, this IS callable:
```haskell
result = f @Int  -- Explicit type application
```

**Solution:** `-XAllowAmbiguousTypes` (opt-in)

**The irony:**
- Default: Reject ambiguity → simpler errors
- Reality: Must enable ambiguity for modern Haskell code
- Result: Module-wide flag that allows ALL ambiguity (not fine-grained)

**Recent proposal (GHC #232):** Per-signature `{-# AMBIGUOUS #-}` pragma

**Why needed:** "Ambiguous signatures are more likely to be an error than intended, even for code using TypeApplications"

**Lesson:** Even Haskell admits that blanket ambiguity-rejection is too coarse!

---

### 15.3 The Paradox: "No Ambiguity" Creates Hidden Ambiguity

**Observation:** Languages that ban syntactic ambiguity often have TYPE-LEVEL ambiguity that's harder to diagnose!

#### Case Study: TypeScript Structural Typing

**TypeScript philosophy:** Structural types, inference-heavy

**Error example:**
```typescript
type Thing = "none" | { name: string };
const a: Thing = { name: 0 };  // ERROR
```

**Error message:**
```
Type 'number' is not assignable to type 'string'.
```

**Good!** But here's a complex case:

```typescript
type A = { m: number[] };
type B = { m: string[] };
const a: A = ...;
const b: B = ...;
a = b;  // ERROR
```

**Error message (TypeScript's actual output):**
```
Type 'B' is not assignable to type 'A'.
  Types of property 'm' are incompatible.
    Type 'string[]' is not assignable to type 'number[]'.
      Type 'string' is not assignable to type 'number'.
```

**This is GOOD!** TypeScript shows the full path of inference.

**But:** This is effectively a "flow-based" error message (shows chain of reasoning)

**Lesson:** Good error messages NEED to show the inference path, whether or not ambiguity exists!

---

#### Case Study: Elm's Trade-offs

**Elm's explicit goal:** "Users do not see runtime errors in practice"

**Achieved via:**
- Strong static typing
- No null, no exceptions
- Friendly compiler errors

**Error message evolution:**
- 0.9: "Type checker completely rewritten for better errors"
- 0.15.1: "Improved error location, content, formatting, hints"
- 0.16: "Better type diffs, more context, eliminated cascading errors"
- 0.19.1: "Improved error messages for learning syntax"

**Result:** Objectively EXCELLENT error messages!

**Example (Elm):**
```
-- TYPE MISMATCH -- Main.elm

The 1st argument to `drop` is not what I expect:

8|   List.drop (String.toInt userInput) [1,2,3,4,5,6]
                ^^^^^^^^^^^^^^^^^^^^^^

This `toInt` call produces:

    Maybe Int

But `drop` needs the 1st argument to be:

    Int

Hint: Use Maybe.withDefault to handle possible errors.
```

**This is FANTASTIC!** Shows:
- What was expected
- What was found
- Actionable suggestion

**BUT:** Elm achieves this NOT by banning ambiguity, but by:
1. ✅ Limiting language features (no type classes, no GADTs)
2. ✅ Custom error message infrastructure
3. ✅ Community error message catalog
4. ✅ Manual heuristics for common mistakes

**Cost:**
- Less expressive language (can't express some abstractions)
- Error messages are hard-coded (not compositional)
- Each new feature requires NEW error message heuristics

**Critique from users:** "Elm treats everyone like a novice. For experts, verbose explanations get annoying."

**Key insight:** Elm's good errors come from ENGINEERING EFFORT, not from "no ambiguity".

---

### 15.4 Comparative Analysis: Three Approaches

| **Aspect** | **No-Ambiguity (Rust)** | **Friendly-First (Elm)** | **Variational (Beneš)** |
|------------|------------------------|--------------------------|-------------------------|
| **Philosophy** | Ban ambiguity via required annotations | Ban ambiguity via limited features | Embrace ambiguity as data |
| **Type System** | HM + traits, partial inference | HM-lite, full inference in limited domain | HM + subtyping + choices |
| **Annotation burden** | Function signatures required | Minimal (inferred) | Minimal (inferred) |
| **Expressiveness** | High (traits, GADTs via hacks) | Low (no type classes) | High (overloading, variational) |
| **Error clarity** | Mixed (E0282 confusing, others good) | Excellent (hand-crafted) | Potentially superior (compositional) |
| **Error engineering** | Per-error-code effort | Massive investment | Falls out of system design |
| **Scales to new features** | Requires new error codes | Requires new heuristics | Automatic |
| **User experience** | Experienced: good; Learners: confusing | Beginners: great; Experts: verbose | Universal: informative |

---

### 15.5 The Fundamental Insight

**Question:** Why do "no-ambiguity" systems still have error message problems?

**Answer:** Because error messages are about EXPLAINING INFERENCE, not just REPORTING AMBIGUITY.

**Three types of errors:**
1. **Actual type errors:** `"hello" + 42` is nonsense
2. **Ambiguity errors:** `foo()` could mean multiple things
3. **Inference failures:** "I can't figure out what you meant"

**No-ambiguity systems:**
- ✅ Eliminate #2 (ambiguity errors)
- ❌ Still have #3 (inference failures) → E0282
- ✅/❌ Have #1 but location/explanation may be wrong

**Variational systems:**
- ✅ Convert #2 into DATA (choices)
- ✅ Can explain #3 via world pruning ("no world satisfies constraints")
- ✅ Better #1 via flow-based explanations

---

### 15.6 Evidence: When "No Ambiguity" Hurts

#### Rust Issue #139168: "Should be inferred automatically"

**Code:**
```rust
fn des<T: Deserialize>() -> T { ... }

fn main() {
    let mut something = des();
    something.value = 100;  // ERROR: type annotations needed
}
```

**User complaint:** "Rust SHOULD be able to infer this! rust-analyzer can!"

**Compiler team response:** "Type checking goes top-to-bottom. When checking `des()`, type is unknown. We don't defer or backtrack."

**Why this is ironic:**
- Rust bans ambiguity to simplify inference
- But simplified inference is TOO simple
- Needs more annotations than necessary
- Variational approach COULD defer this choice until line 2

---

#### Haskell GADTs: Annotations Don't Help

**Problem:** GADTs introduce local type equations → ambiguities

**Traditional solution:** Require annotations

**Reality:** Sometimes NO annotation helps!

**Example (from Simonet & Pottier 2007):**
```haskell
data T a where
  MkT :: T Int

f :: T a -> a -> Int
f MkT x = x + 1  -- ERROR: Ambiguous 'a'
```

**User adds annotation:**
```haskell
f :: T Int -> Int -> Int  -- ERROR: Doesn't match signature!
```

**Root cause:** `a` is BOTH:
- In outer scope: `forall a. T a -> a -> Int`
- In inner scope: `a ~ Int` (from GADT match)

**No annotation resolves this!**

**Solution (modern GHC):** Constraint solving instead of annotation propagation

**Lesson:** "Just add annotations" doesn't always work. Need smarter solving.

---

### 15.7 Variational Advantages Highlighted by Comparison

**What variational systems provide that no-ambiguity systems don't:**

#### 1. Deferred Resolution = Better Inference

**No-ambiguity (Rust):**
```rust
let x = foo();     // ERROR: E0282 type annotations needed
x.bar();           // Would resolve if we got here!
```

**Variational:**
```rust
let x = foo();     // Creates choice: { FooType1, FooType2, ... }
x.bar();           // Prunes to types that have .bar()
// Type resolved!
```

**Benefit:** Fewer annotations needed.

---

#### 2. Comprehensive Error Context

**No-ambiguity (Haskell):**
```haskell
f = bar undefined  -- ERROR: Ambiguous type 'a'
```

**Tells you:** "This is ambiguous"
**Doesn't tell you:** What types were considered, why each failed

**Variational:**
```haskell
f = bar undefined  -- ERROR: Ambiguous choice 'f_type'

Possible types for 'a':
  a=Int:    ✓ Type-checks but requires explicit TypeApplications
  a=String: ✓ Type-checks but requires explicit TypeApplications
  a=Float:  ✗ No instance Foo Float

Ambiguous between Int and String. Use TypeApplications to disambiguate.
```

**Benefit:** Shows ALL possibilities, not just "ambiguous".

---

#### 3. Successful Disambiguation is Informative

**No-ambiguity systems:** Silent success (no message)

**Variational systems:** Can report successful disambiguation!

```
info[I0100]: Parse disambiguation via types

Expression: m1 * s / m2

Resolved parse 1 (of 2) based on type constraints.
The other parse would have been a type error.
```

**Benefit:** User learns WHY their code works (educational!)

---

### 15.8 The Spectrum of Error Message Quality

```
┌─────────────────────────────────────────────────────────────────┐
│                                                                 │
│  WORST                                                   BEST   │
│                                                                 │
│  Traditional   Rust       Elm         TypeScript    Variational │
│  backtracking  E0282      friendly    structured   flow-based   │
│                                       diff                      │
│      │           │          │            │              │       │
│      ├───────────┴──────────┴────────────┴──────────────┤       │
│                                                                 │
│  "Try until    "Need       "Here's      "Here's        "Here's  │
│   one works"   annotation  what I       inference      all      │
│                 here"      expected     chain"         worlds   │
│                            vs found"                   + why"   │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

**Key finding:** Error message quality is INDEPENDENT of ambiguity policy!

---

### 15.9 Synthesis: Error Message Design Principles

**What makes good error messages (from all approaches):**

1. ✅ **Show the full inference chain** (TypeScript, Flow.js)
2. ✅ **Explain what was expected vs found** (Elm)
3. ✅ **Provide actionable suggestions** (Elm, Rust help messages)
4. ✅ **Locate error precisely** (all modern systems)
5. ✅ **Show WHY alternatives failed** (variational systems ONLY)
6. ✅ **Allow deferred resolution** (variational systems ONLY)
7. ✅ **Compositional error reporting** (variational systems ONLY)

**What DOESN'T help:**
- ❌ Banning ambiguity (doesn't prevent E0282, cascading errors)
- ❌ Requiring annotations (can't always resolve ambiguities)
- ❌ Limiting expressiveness (reduces errors but limits usefulness)
- ❌ Ad-hoc heuristics (doesn't scale to new features)

**Best approach for HWML:**
- Variational type-checking (Beneš)
- + Flow-based explanations (TypeScript/Flow.js)
- + Friendly formatting (Elm)
- + Comprehensive world analysis (our contribution)
- = **Superior error messages that SCALE**

---

### 15.10 Conclusion: Challenging the No-Ambiguity Dogma

**Initial assumption:** "No ambiguity → good error messages"

**Research finding:** **FALSE!**

**Evidence:**
1. ✅ Rust requires annotations but still has E0282 (confusing!)
2. ✅ Elm limits features but still has cascading errors
3. ✅ Haskell bans ambiguity but must enable it for modern code
4. ✅ TypeScript shows good errors are about inference chains, not ambiguity policy

**Correct principle:** "Good error messages come from explaining the type inference process clearly."


---

## 16. Critical Analysis: Are Variational Constraints Just Backtracking in Disguise?

### 16.1 The Valid Concern

**User's observation:** "Variational constraints seem like backtracking to me - just rephrased."

**The worry:**
- Backtracking: Try alternative 1, fail, try alternative 2, fail, ...
- Variational: Maintain alternatives 1, 2, 3, ... and prune incrementally
- **Aren't these the SAME THING?**
- Both must "explain to the user everything we tried"
- Both have potentially exponential alternatives to consider

**This is a LEGITIMATE concern** that deserves serious analysis.

---

### 16.2 The Fundamental Difference: State Management

#### Backtracking (Traditional)

```rust
fn type_check_with_backtracking(expr: Expr, ctx: Context) -> Result<Type> {
    match expr {
        Expr::Overload(symbol, args) => {
            for defn in symbol.definitions() {
                // CHECKPOINT: Save entire context state
                let checkpoint = ctx.save();

                match type_check_definition(defn, args, ctx) {
                    Ok(ty) => return Ok(ty),  // Success!
                    Err(_) => {
                        // RESTORE: Roll back all changes
                        ctx.restore(checkpoint);
                        continue;  // Try next
                    }
                }
            }
            Err("No valid overload")
        }
        // ... other cases also do checkpointing
    }
}
```

**Key operations:**
- `ctx.save()`: Deep copy entire type environment
- `ctx.restore()`: Throw away all work, roll back
- **Sequential:** Try A, fail, try B, fail, try C
- **Destructive:** Each attempt destroys the previous one

**Complexity:**
- Time: O(alternatives × constraint_solving_cost)
- Space: O(context_size) per checkpoint
- **Exponential:** Nested overloads multiply: 3 × 3 × 3 = 27 attempts

---

#### Variational (Beneš)

```rust
fn type_check_variational(expr: Expr, ctx: Context) -> Result<Type> {
    match expr {
        Expr::Overload(symbol, args) => {
            let choice_dim = fresh_dimension();

            // NO CHECKPOINTING!
            // Generate constraints for ALL definitions IN PARALLEL
            let mut all_constraints = Vec::new();
            for (idx, defn) in symbol.definitions().enumerate() {
                let world = World { choice_dim, case: idx };

                // Add: "In world W, these constraints must hold"
                let constraints = generate_constraints(defn, args, world);
                all_constraints.extend(constraints);
            }

            // Solve ALL constraints ONCE
            // No rolling back, no retrying
            solve_constraints(all_constraints)?;

            // Check which worlds survived
            let valid_worlds = ctx.get_valid_worlds(choice_dim);

            match valid_worlds.len() {
                0 => Err("No valid overload"),
                1 => Ok(specialize_type(ctx, valid_worlds[0])),
                _ => Err("Ambiguous overload"),
            }
        }
    }
}
```

**Key operations:**
- NO `save()`/`restore()`
- **Parallel:** Generate constraints for all alternatives simultaneously
- **Additive:** Each alternative ADDS constraints, doesn't replace
- **Monotonic:** Constraints accumulate, worlds only shrink (never backtrack)

**Complexity:**
- Time: O(alternatives + constraint_solving_cost)  ← **SAME COST** regardless of alternatives!
- Space: O(alternatives × constraint_count)
- **Polynomial:** 3 nested overloads = 3 + 3 + 3 = 9 constraint sets, NOT 27!

---

### 16.3 The Crucial Distinction: "Try" vs "Represent"

**Backtracking mindset:** "Try different things until one works"

```
Try A → Fail → Undo
Try B → Fail → Undo
Try C → Success!
```

**Variational mindset:** "Represent uncertainty as data, let constraints eliminate inconsistencies"

```
Represent: choice { A, B, C }
Add constraints from context
Observe: A inconsistent (pruned)
Observe: B inconsistent (pruned)
Observe: C consistent (unique solution)
```

**Analogy:**

**Backtracking = Sequential search:**
```python
def find_solution(candidates):
    for c in candidates:
        if test(c):
            return c
    return None
```

**Variational = Filter/reduce:**
```python
def find_solution(candidates):
    valid = [c for c in candidates if test(c)]
    return unique(valid)
```

**Key difference:** In filtering, `test(c)` doesn't MODIFY global state!

---

### 16.4 Practical Implication: Nested Choices

**Scenario:** Nested overloaded calls

```rust
let result = foo(bar(x));
// foo has 3 overloads
// bar has 3 overloads
```

#### Backtracking Approach

```
Try bar₁:
  Try foo₁: checkpoint, type-check, fail, restore
  Try foo₂: checkpoint, type-check, fail, restore
  Try foo₃: checkpoint, type-check, fail, restore
  All failed, backtrack from bar₁

Try bar₂:
  Try foo₁: checkpoint, type-check, fail, restore
  Try foo₂: checkpoint, type-check, fail, restore
  Try foo₃: checkpoint, type-check, success!

Total: 6 type-checks, 6 save/restore cycles
```

**Complexity:** O(3 × 3) = **O(9)** attempts

#### Variational Approach

```
Generate constraints:
  For bar₁: constraints C_bar₁
  For bar₂: constraints C_bar₂
  For bar₃: constraints C_bar₃

  For foo₁: constraints C_foo₁
  For foo₂: constraints C_foo₂
  For foo₃: constraints C_foo₃

Solve once with ALL constraints:
  World {bar=1, foo=1}: C_bar₁ ∪ C_foo₁ → inconsistent
  World {bar=1, foo=2}: C_bar₁ ∪ C_foo₂ → inconsistent
  ... (check all 9 combinations)
  World {bar=2, foo=3}: C_bar₂ ∪ C_foo₃ → consistent!

Total: 1 constraint generation pass, 1 solve pass
```

**Complexity:** O(3 + 3) = **O(6)** constraint sets, checked in **ONE** solve

**BUT WAIT:** Don't we still check 9 combinations?

**ANSWER:** Yes, but checking if constraints are consistent is MUCH cheaper than:
- Saving/restoring entire context
- Re-running type-checking algorithm
- Managing checkpoint stack

---

### 16.5 The Real Difference: Incremental Pruning

**This is the KEY insight that makes variational NOT backtracking:**

**Backtracking:** Must try EVERY alternative until success

**Variational:** Prune alternatives AS SOON AS POSSIBLE

```rust
fn solve_with_pruning(constraints: Vec<Constraint>) -> Result<Bounds> {
    let mut bounds = Bounds::empty();

    for constraint in constraints {
        add_constraint(&mut bounds, constraint)?;

        // IMMEDIATELY prune inconsistent worlds
        let pruned = prune_now(&mut bounds);

        if pruned.is_empty() {
            // Early exit: no worlds left!
            return Err("No consistent solution");
        }
    }

    Ok(bounds)
}
```

**Example:**

```rust
// Three overloads: +Int, +Float, +String
let result = x + y;

// After seeing x : Int
Worlds before: {+Int, +Float, +String}
Add constraint: x flows into first param of +
Prune: +Float (Int !<: Float), +String (Int !<: String)
Worlds after: {+Int}  ← SOLVED! Don't even look at y!
```

**With backtracking:**
```rust
Try +Int: success! (but had to checkpoint/restore for each)
Try +Float: would fail (but we'd still try it)
Try +String: would fail (but we'd still try it)
```

**Key:** Variational can STOP early when only one world remains!

---

### 16.6 When Variational IS Like Backtracking (Honest Assessment)

**Your concern is VALID in these cases:**

#### Case 1: All Worlds Must Be Checked

If constraints don't prune worlds until the very end:

```rust
let result = mystery_function(a, b, c);
// mystery_function has 10 overloads
// a, b, c have generic types
```

**Backtracking:** Try all 10 overloads sequentially
**Variational:** Generate constraints for all 10, check all 10 at the end

**Result:** Effectively the same work! (Though variational still avoids save/restore)

**When this happens:**
- Insufficient type information early
- Constraints don't prune until full expression is analyzed
- "Exploding" choice dimensions

---

#### Case 2: Explaining Failures

**Your point:** "Both have to explain everything we tried to the user"

**This is TRUE if ALL alternatives fail!**

```
error: No valid overload for 'foo'

Tried:
  foo(Int):    ✗ because x : String
  foo(Float):  ✗ because x : String
  foo(String): ✗ because y : Int
```

**Backtracking:** Had to try all 3 (sequentially)
**Variational:** Checked all 3 (in parallel)

**For error messages:** Must show all 3 either way!

**BUT:** Variational can show MORE detail:
- Exact constraint that failed
- When it was pruned
- Relation between failures

---

### 16.7 Honest Comparison: When Is Variational Actually Better?

**Variational wins when:**

1. ✅ **Early pruning possible**
   - Type information available incrementally
   - Constraints eliminate worlds before full analysis
   - Example: `x + y` where `x : Int` immediately selects `+Int`

2. ✅ **Many nested choices**
   - Backtracking: exponential (M × N × P)
   - Variational: additive (M + N + P) + consistency check
   - Consistency check is cheaper than full type-check with save/restore

3. ✅ **Incremental compilation**
   - Can cache constraint sets
   - Can reuse pruning results across edits
   - Backtracking requires re-trying everything

4. ✅ **IDE support**
   - Can show "still ambiguous but narrowed down" state
   - Can provide partial results
   - Backtracking is all-or-nothing

**Backtracking wins when:**

1. ✅ **Success is common and early**
   - If first alternative usually works
   - No need to generate constraints for others
   - Example: method resolution where name matches uniquely

2. ✅ **Alternatives are cheap to try**
   - If checkpointing is trivial
   - If type-checking is fast
   - Example: simple unification, no complex constraints

3. ✅ **User prefers simple errors**
   - "Tried X, failed because Y"
   - Don't want to see 10 alternatives when only 1 was close

---

### 16.8 The Honest Truth: It's a Trade-Off

**You are RIGHT to be skeptical!**

**Variational constraints are NOT magic.** They don't eliminate the fundamental problem:

> **"When there are N alternatives, you need to consider all N in the worst case."**

**What variational DOES provide:**

1. **Better compositionality**
   - Constraints compose, backtracking states don't
   - Easier to reason about interactions

2. **Monotonic progress**
   - Worlds only shrink (monotonic)
   - No "trying something then undoing it"
   - Better for debugging, better for incremental

3. **Potential for early exit**
   - Can stop when unique world found
   - Can report "still ambiguous but down to 2 options"

4. **Better error messages** (but YOU'RE RIGHT: only if designed well!)
   - Can show ALL failures at once
   - Can show relationships between failures
   - BUT: Overwhelming if 50 overloads fail

---

### 16.9 The Responsible Choice for HWML

**Your instinct: "No backtracking is the responsible thing to do"**

**I AGREE.** Here's the responsible path forward:

#### Option 1: Strict Disambiguation (No Backtracking, No Variational)

**Approach:** Force user to disambiguate at source level

```hwml
// Ambiguous: ERROR!
let result = foo(x);

// Unambiguous: explicit
let result = foo@Int(x);  // Type application
let result = (foo : Int -> Int)(x);  // Type annotation
```

**Pros:**
- ✅ No backtracking (failed parse = immediate error)
- ✅ No variational machinery
- ✅ Simple, predictable, fast
- ✅ Code is self-documenting

**Cons:**
- ❌ More annotation burden on user
- ❌ Less convenient than Haskell/Rust
- ❌ May be frustrating for obvious cases

**Examples:**
- Agda (requires ALL precedence declared)
- Coq (requires explicit tactics)

---

#### Option 2: Suspended Constraints (Minimal Backtracking)

**Approach:** Suspend when ambiguous, require resolution before continuing

```hwml
let x = foo(y);  // Suspended: waiting for type info
// ... more code that constrains x's type
x.bar();  // NOW resolve: only one foo makes sense

// If still ambiguous:
// ERROR: Ambiguous 'foo', please annotate
```

**Pros:**
- ✅ No backtracking (just suspension + single resolution)
- ✅ Better inference than strict
- ✅ Simpler than full variational

**Cons:**
- ❌ Can get "stuck" if suspension never resolves
- ❌ Errors are deferred (user sees error far from source)
- ❌ Requires fixpoint iteration (suspension loop)

**Examples:**
- OCaml with frozen constraints
- Swift (though it backtracks too much)

---

#### Option 3: Bounded Variational (Hybrid)

**Approach:** Use variational, but limit scope

```hwml
// Rule: At most 3 alternatives maintained
// Rule: At most 2 levels of nesting

let result = foo(bar(x));
// bar has 2 overloads ← OK
// foo has 3 overloads ← OK
// Total: 2 × 3 = 6 worlds ← manageable

// If more alternatives:
// ERROR: Too many overloads, please disambiguate one level
```

**Pros:**
- ✅ Gets benefits of variational where it helps
- ✅ Avoids explosion by bounding
- ✅ Predictable performance

**Cons:**
- ❌ Arbitrary limits feel wrong
- ❌ User must understand limits
- ❌ Still complex to implement

---

#### Option 4: Datalog-Style Constraint Solving (Declarative)

**Approach:** Express type checking as logic programming

```prolog
% Declare all possibilities
overload(foo, int, int).
overload(foo, string, string).

% Declare constraints
type_of(x, int).
type_of(result, T) :- overload(foo, T, T), type_of(x, T).

% Ask: What are valid instantiations?
?- type_of(result, T).
% Answer: T = int (unique!)
```

**Pros:**
- ✅ Declarative (no backtracking in code)
- ✅ Can use off-the-shelf Datalog solvers
- ✅ Well-understood semantics

**Cons:**
- ❌ Datalog has worst-case exponential
- ❌ Error messages are HARD
- ❌ Debugging is difficult

---

### 16.10 My Recommendation for HWML

**Given your concerns**, I recommend:

**Phase 1: Strict + Suspended (No Variational Yet)**

1. Start with strict disambiguation (require annotations for overloads)
2. Add suspended constraints for type-directed features (dot notation)
3. Measure: How often do users hit "ambiguity" errors?

**Phase 2: Evaluate Need**

If users constantly need annotations:
- Consider bounded variational (at most N alternatives)
- Or consider datalog-style declarative constraints

If annotations are rare:
- Strict + suspended is sufficient!
- Avoid complexity of full variational

**Phase 3: Error Message First**

Whatever you choose, design error messages FIRST:
```
error: Ambiguous overload for 'foo'

Candidates:
  1. foo : Int -> Int
  2. foo : String -> String

Context:
  Argument x has type: ???  (unknown)

Resolution:
  Add type annotation to x, or use foo@Int/foo@String
```

**Key principle:** Good errors matter more than fancy inference!

---

### 16.11 Final Answer to Your Concern

**"Are variational constraints just backtracking rephrased?"**

**Short answer:** No, but they share the same worst-case behavior.

**Long answer:**
- Backtracking: Sequential trial-and-error with save/restore
- Variational: Parallel constraint generation with pruning
- **Same worst case:** O(alternatives) work
- **Different in practice:** Variational can prune early, compose better
- **Your instinct is RIGHT:** Don't assume variational magically solves everything!

**Responsible path:**
1. Start simple (strict disambiguation)
2. Add suspension only where needed
3. Consider variational only if measured need exists
4. Always prioritize clear error messages

**Don't implement variational constraints just because they're "cool."**
Implement them if and only if:
- User studies show annotation burden is too high
- Profiling shows early pruning actually happens
- Error message design is clear and tested


---

## 17. Practical Implementation: Variational Constraints + Mixfix Parsing

### 17.1 The Key Question

**"What would it look like to implement variational constraints?"**

**"Can we interleave them with parsing to disambiguate mixfix operators?"**

**Answer:** Yes, but the architecture is non-trivial. Let me show concrete implementations.

---

### 17.2 Core Data Structures

#### 17.2.1 Choice Dimensions

```rust
/// A dimension represents a single ambiguity site
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ChoiceDim(u32);

/// A world is a selection from each choice dimension
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct World {
    selections: FxHashMap<ChoiceDim, CaseId>,
}

impl World {
    pub fn selects(&self, dim: ChoiceDim, case: CaseId) -> bool {
        self.selections.get(&dim) == Some(&case)
    }

    pub fn compatible_with(&self, other: &World) -> bool {
        for (dim, &case) in &self.selections {
            if let Some(&other_case) = other.selections.get(dim) {
                if case != other_case {
                    return false;
                }
            }
        }
        true
    }
}

/// Which case of a choice
pub type CaseId = u32;

/// Source of a choice
#[derive(Debug, Clone)]
pub enum ChoiceSource {
    /// From SPPF parse ambiguity
    ParseAmbiguity {
        location: SourceSpan,
        sppf_node: SPPFNodeId,
        description: String,
    },
    /// From overload resolution
    Overloading {
        location: SourceSpan,
        symbol: Symbol,
        candidates: Vec<DefId>,
    },
    /// From type-directed dot notation
    DotNotation {
        location: SourceSpan,
        receiver: Expr,
        field: Ident,
    },
}
```

---

#### 17.2.2 Variational Types

```rust
/// Types with choice dimensions
#[derive(Debug, Clone)]
pub enum Type {
    /// Type variable
    Var(TypeVar),

    /// Concrete type
    Con(TypeCon, Vec<Type>),

    /// Function type
    Arrow(Box<Type>, Box<Type>),

    /// Choice between types (NEW!)
    Choice {
        dimension: ChoiceDim,
        cases: Vec<(CaseId, Type)>,
    },
}

impl Type {
    /// Specialize a type to a specific world
    pub fn specialize(&self, world: &World) -> Type {
        match self {
            Type::Var(v) => Type::Var(*v),
            Type::Con(c, args) => {
                Type::Con(c.clone(), args.iter().map(|t| t.specialize(world)).collect())
            }
            Type::Arrow(a, b) => {
                Type::Arrow(
                    Box::new(a.specialize(world)),
                    Box::new(b.specialize(world))
                )
            }
            Type::Choice { dimension, cases } => {
                // Select the case for this world
                if let Some(&case_id) = world.selections.get(dimension) {
                    for (id, ty) in cases {
                        if *id == case_id {
                            return ty.specialize(world);
                        }
                    }
                    panic!("World selects non-existent case");
                } else {
                    // World doesn't constrain this dimension yet
                    Type::Choice {
                        dimension: *dimension,
                        cases: cases.iter().map(|(id, ty)| (*id, ty.specialize(world))).collect(),
                    }
                }
            }
        }
    }
}
```

---

#### 17.2.3 Constraints with Worlds

```rust
#[derive(Debug, Clone)]
pub enum Constraint {
    /// Traditional equality
    Unify(Type, Type),

    /// Subtyping (for flow-based)
    Sub {
        lower: Type,
        upper: Type,
    },

    /// Constraint that only applies in specific worlds
    InWorld {
        world_filter: WorldFilter,
        constraint: Box<Constraint>,
    },

    /// Choice constraint: one of these must hold
    Choice {
        dimension: ChoiceDim,
        cases: Vec<(CaseId, Vec<Constraint>)>,
        source: ChoiceSource,
    },

    /// Suspended constraint (orthogonal to choices)
    Suspended {
        blocked_on: Vec<TypeVar>,
        resume: Arc<dyn Fn(&Substitution) -> Constraint>,
    },
}

/// Filter to select which worlds a constraint applies to
#[derive(Debug, Clone)]
pub enum WorldFilter {
    /// Applies to all worlds
    All,

    /// Applies only if dimension selects case
    IfCase(ChoiceDim, CaseId),

    /// Applies if predicate holds
    Custom(Arc<dyn Fn(&World) -> bool>),
}
```

---

### 17.3 Constraint Generation from SPPF

**Goal:** Convert SPPF parse ambiguity into choice constraints

```rust
/// SPPF node (from GLL parser)
#[derive(Debug, Clone)]
pub enum SPPFNode {
    /// Terminal symbol
    Terminal(Token),

    /// Unique parse (no ambiguity)
    Unique {
        rule: RuleId,
        children: Vec<SPPFNodeId>,
    },

    /// Ambiguous parse (multiple alternatives)
    Ambiguous {
        alternatives: Vec<SPPFNodeId>,
    },
}

/// Elaborate SPPF to variational core expression
pub struct SPPFElaborator {
    dim_counter: u32,
    constraints: Vec<Constraint>,
    choice_sources: FxHashMap<ChoiceDim, ChoiceSource>,
}

impl SPPFElaborator {
    pub fn elaborate_sppf(&mut self, node_id: SPPFNodeId, sppf: &SPPF) -> Expr {
        let node = &sppf.nodes[node_id];

        match node {
            SPPFNode::Terminal(tok) => {
                self.elaborate_terminal(tok)
            }

            SPPFNode::Unique { rule, children } => {
                self.elaborate_unique(*rule, children, sppf)
            }

            SPPFNode::Ambiguous { alternatives } => {
                // KEY: Create choice dimension for this ambiguity
                let dim = self.fresh_dimension();

                // Elaborate each alternative
                let cases: Vec<_> = alternatives.iter().enumerate().map(|(idx, &alt_id)| {
                    let case_id = idx as CaseId;
                    let expr = self.elaborate_sppf(alt_id, sppf);
                    (case_id, expr)
                }).collect();

                // Record source
                self.choice_sources.insert(
                    dim,
                    ChoiceSource::ParseAmbiguity {
                        location: node.span(),
                        sppf_node: node_id,
                        description: format!("Ambiguous parse ({} alternatives)", alternatives.len()),
                    },
                );

                // Return choice expression
                Expr::Choice { dim, cases }
            }
        }
    }

    fn fresh_dimension(&mut self) -> ChoiceDim {
        let dim = ChoiceDim(self.dim_counter);
        self.dim_counter += 1;
        dim
    }
}
```

---

### 17.4 Type-Checking Variational Expressions

```rust
pub struct VariationalTypeChecker {
    /// Current type environment
    env: TypeEnv,

    /// Accumulated constraints
    constraints: Vec<Constraint>,

    /// Active worlds (starts with all combinations, gets pruned)
    active_worlds: WorldSet,

    /// Choice metadata
    choice_sources: FxHashMap<ChoiceDim, ChoiceSource>,
}

impl VariationalTypeChecker {
    pub fn infer(&mut self, expr: &Expr) -> Result<Type> {
        match expr {
            Expr::Var(x) => {
                Ok(self.env.lookup(x)?.clone())
            }

            Expr::Lam(x, body) => {
                let param_ty = Type::Var(self.fresh_var());
                self.env.extend(x.clone(), param_ty.clone());
                let body_ty = self.infer(body)?;
                Ok(Type::Arrow(Box::new(param_ty), Box::new(body_ty)))
            }

            Expr::App(func, arg) => {
                let func_ty = self.infer(func)?;
                let arg_ty = self.infer(arg)?;
                let result_ty = Type::Var(self.fresh_var());

                // Add constraint
                self.constraints.push(Constraint::Unify(
                    func_ty,
                    Type::Arrow(Box::new(arg_ty), Box::new(result_ty.clone()))
                ));

                Ok(result_ty)
            }

            // NEW: Handle choice expressions
            Expr::Choice { dim, cases } => {
                // Generate type for each case
                let case_types: Vec<_> = cases.iter().map(|(case_id, expr)| {
                    // Type-check in isolated context for this case
                    let case_ty = self.infer(expr)?;
                    Ok((*case_id, case_ty))
                }).collect::<Result<_>>()?;

                // Return choice type
                Ok(Type::Choice {
                    dimension: *dim,
                    cases: case_types,
                })
            }

            // Handle overloading
            Expr::Overloaded(symbol, args) => {
                let overloads = self.env.lookup_overloads(symbol)?;

                if overloads.len() == 1 {
                    // No choice needed
                    return self.infer_call(&overloads[0], args);
                }

                // Create choice dimension
                let dim = self.fresh_dimension();

                // Generate constraints for each overload
                let case_constraints: Vec<_> = overloads.iter().enumerate().map(|(idx, defn)| {
                    let case_id = idx as CaseId;

                    // Type of this overload
                    let overload_ty = defn.ty.clone();

                    // Infer argument types
                    let arg_tys: Vec<_> = args.iter().map(|a| self.infer(a)).collect::<Result<_>>()?;

                    // Generate constraint: overload_ty <: (arg_tys -> result_ty)
                    let result_ty = Type::Var(self.fresh_var());
                    let expected_ty = arg_tys.iter().rev().fold(
                        result_ty.clone(),
                        |acc, arg| Type::Arrow(Box::new(arg.clone()), Box::new(acc))
                    );

                    let constraint = Constraint::InWorld {
                        world_filter: WorldFilter::IfCase(dim, case_id),
                        constraint: Box::new(Constraint::Unify(overload_ty, expected_ty)),
                    };

                    Ok((case_id, vec![constraint], result_ty))
                }).collect::<Result<_>>()?;

                // Add choice constraint
                let case_types: Vec<_> = case_constraints.iter().map(|(id, _, ty)| (*id, ty.clone())).collect();
                let constraints: Vec<_> = case_constraints.into_iter().flat_map(|(id, cs, _)| cs).collect();

                self.constraints.push(Constraint::Choice {
                    dimension: dim,
                    cases: constraints.iter().map(|c| (0, vec![c.clone()])).collect(), // TODO: fix
                    source: ChoiceSource::Overloading {
                        location: expr.span(),
                        symbol: symbol.clone(),
                        candidates: overloads.iter().map(|d| d.id).collect(),
                    },
                });

                // Return choice type
                Ok(Type::Choice {
                    dimension: dim,
                    cases: case_types,
                })
            }
        }
    }
}
```

---

### 17.5 Constraint Solving with World Pruning

```rust
pub struct VariationalSolver {
    /// All constraints
    constraints: Vec<Constraint>,

    /// Active worlds (pruned incrementally)
    worlds: WorldSet,

    /// Bounds for each type variable (per world)
    bounds: FxHashMap<TypeVar, WorldBounds>,
}

/// Bounds that may differ per world
#[derive(Debug, Clone)]
pub struct WorldBounds {
    /// For each world, what are the bounds?
    per_world: FxHashMap<World, Bounds>,
}

#[derive(Debug, Clone)]
pub struct Bounds {
    lower: Vec<Type>,  // τ <: α
    upper: Vec<Type>,  // α <: τ
}

impl VariationalSolver {
    pub fn solve(&mut self) -> Result<Solution> {
        // Process constraints, pruning worlds as we go
        for constraint in &self.constraints {
            self.add_constraint(constraint)?;

            // IMMEDIATELY prune inconsistent worlds
            self.prune_inconsistent_worlds()?;

            if self.worlds.is_empty() {
                return Err(Error::NoValidWorlds);
            }
        }

        // Check final state
        match self.worlds.len() {
            0 => Err(Error::NoValidWorlds),
            1 => Ok(Solution::Unique(self.worlds.iter().next().unwrap().clone())),
            _ => Err(Error::StillAmbiguous(self.worlds.clone())),
        }
    }

    fn add_constraint(&mut self, c: &Constraint) -> Result<()> {
        match c {
            Constraint::Unify(t1, t2) => {
                // Add to all worlds
                for world in &self.worlds {
                    self.unify_in_world(t1, t2, world)?;
                }
            }

            Constraint::Sub { lower, upper } => {
                // Add to all worlds
                for world in &self.worlds {
                    self.add_bound_in_world(lower, upper, world)?;
                }
            }

            Constraint::InWorld { world_filter, constraint } => {
                // Add only to filtered worlds
                for world in &self.worlds {
                    if world_filter.matches(world) {
                        self.add_constraint_in_world(constraint, world)?;
                    }
                }
            }

            Constraint::Choice { dimension, cases, .. } => {
                // For each case, add constraints in worlds that select that case
                for (case_id, case_constraints) in cases {
                    for world in &self.worlds {
                        if world.selects(*dimension, *case_id) {
                            for c in case_constraints {
                                self.add_constraint_in_world(c, world)?;
                            }
                        }
                    }
                }
            }

            Constraint::Suspended { .. } => {
                // Keep for later (fixpoint iteration)
                // Not shown here for brevity
            }
        }

        Ok(())
    }

    fn prune_inconsistent_worlds(&mut self) -> Result<()> {
        let mut to_remove = Vec::new();

        for world in &self.worlds {
            if !self.is_world_consistent(world) {
                to_remove.push(world.clone());
            }
        }

        for world in to_remove {
            self.worlds.remove(&world);
        }

        Ok(())
    }

    fn is_world_consistent(&self, world: &World) -> bool {
        // Check all type variables
        for (var, world_bounds) in &self.bounds {
            if let Some(bounds) = world_bounds.per_world.get(world) {
                // Check: ∀ (τ_l ∈ lower, τ_u ∈ upper) : τ_l <: τ_u
                for lower_ty in &bounds.lower {
                    for upper_ty in &bounds.upper {
                        if !self.is_subtype(lower_ty, upper_ty, world) {
                            return false;  // Inconsistent!
                        }
                    }
                }
            }
        }

        true
    }
}
```

---

### 17.6 Interleaving with Parsing: The Architecture

**Question:** "Can we interleave variational constraints with parsing?"

**Answer:** Yes, using a **three-phase architecture**:

#### Phase 1: Parse to SPPF (Ambiguity-Preserving)

```rust
pub fn parse(input: &str) -> Result<SPPF> {
    // GLL parser produces SPPF
    // ALL parse trees represented compactly
    // Ambiguities are explicit (SPPFNode::Ambiguous)

    gll_parse(input)
}
```

**Output:** SPPF with explicit ambiguity nodes

---

#### Phase 2: Elaborate SPPF to Variational Core (Choice Introduction)

```rust
pub fn elaborate_to_variational(sppf: &SPPF) -> (Expr, Vec<ChoiceSource>) {
    let mut elaborator = SPPFElaborator::new();
    let expr = elaborator.elaborate_sppf(sppf.root, sppf);
    (expr, elaborator.choice_sources)
}
```

**Output:** Expr with `Expr::Choice` nodes where SPPF had ambiguities

---

#### Phase 3: Type-Check with Constraint Generation and Pruning

```rust
pub fn type_check_variational(expr: &Expr) -> Result<(Type, World)> {
    let mut checker = VariationalTypeChecker::new();
    let ty = checker.infer(expr)?;

    // Solve constraints
    let mut solver = VariationalSolver::new(checker.constraints, checker.active_worlds);
    let solution = solver.solve()?;

    match solution {
        Solution::Unique(world) => {
            // Specialize type to this world
            Ok((ty.specialize(&world), world))
        }
        Solution::Ambiguous(worlds) => {
            Err(Error::StillAmbiguous {
                ty,
                valid_worlds: worlds,
                choice_sources: checker.choice_sources,
            })
        }
    }
}
```

**Output:** Either unique world (success!) or ambiguity error with details

---

### 17.7 Concrete Example: Mixfix with Overloading

**Input:**
```hwml
if x < y then a + b else c * d
```

**Assumptions:**
- `if_then_else_` is mixfix
- `<`, `+`, `*` are all overloaded (Int/Float)
- Precedence of `<` vs `+` vs `*` is ambiguous

---

**Phase 1: Parse produces SPPF**

```
SPPF root:
  Ambiguous {
    alt1: if x < (y then a) + b else c * d  // BAD parse (wrong grouping)
    alt2: if (x < y) then (a + b) else (c * d)  // Intended parse
    alt3: if (x < y) then a + (b else c) * d  // Another bad parse
  }
```

---

**Phase 2: Elaborate to variational core**

```rust
Expr::Choice {
  dim: D_parse,
  cases: [
    (0, /* alt1 elaborated */),
    (1, /* alt2 elaborated */),
    (2, /* alt3 elaborated */),
  ]
}
```

**Choice source:** `ParseAmbiguity` at `if` keyword

---

**Phase 3: Type-check each alternative**

```rust
// Alt 0: Will fail (syntactic nonsense)
// Alt 1: Type-checks!
//   if (x < y) then (a + b) else (c * d)
//   Further choices for <, +, * overloads
// Alt 2: Will fail (type error or parse error)

// After type-checking all:
Worlds pruned:
  - {D_parse=0}: Pruned (parse structure invalid)
  - {D_parse=2}: Pruned (parse structure invalid)

Remaining:
  - {D_parse=1, D_less=Int, D_plus=Int, D_mult=Int}
  - {D_parse=1, D_less=Float, D_plus=Float, D_mult=Float}

// If x, y, a, b, c, d all have known types:
// Further pruning eliminates all but one world
```

---

### 17.8 Performance Considerations

#### 17.8.1 World Explosion Problem

**The challenge:** With N choice dimensions, each with M alternatives, there are potentially M^N worlds!

```rust
// 3 parse ambiguities (each with 2 alternatives)
// 4 overloads (each with 3 alternatives)
// Total worlds: 2³ × 3⁴ = 8 × 81 = 648 worlds!
```

**Mitigation strategies:**

**1. Lazy World Enumeration**

Don't enumerate all worlds upfront! Only track which dimensions exist:

```rust
pub struct WorldSet {
    dimensions: FxHashMap<ChoiceDim, Vec<CaseId>>,
}

impl WorldSet {
    /// Don't enumerate! Just track possibilities
    pub fn new() -> Self {
        WorldSet {
            dimensions: FxHashMap::default(),
        }
    }

    pub fn add_dimension(&mut self, dim: ChoiceDim, cases: Vec<CaseId>) {
        self.dimensions.insert(dim, cases);
    }

    /// Prune a specific case from a dimension
    pub fn prune_case(&mut self, dim: ChoiceDim, case: CaseId) {
        if let Some(cases) = self.dimensions.get_mut(&dim) {
            cases.retain(|&c| c != case);
        }
    }

    /// Iterate only when needed
    pub fn iter_worlds(&self) -> impl Iterator<Item = World> + '_ {
        // Cartesian product (lazy!)
        // Only materialized when actually needed
        cartesian_product(self.dimensions.iter())
    }
}
```

**2. Incremental Pruning**

Prune cases as soon as they're inconsistent:

```rust
fn prune_incrementally(&mut self, constraint: &Constraint) {
    match constraint {
        Constraint::InWorld { world_filter: WorldFilter::IfCase(dim, case), .. } => {
            // Check if this specific case is consistent
            if !self.is_case_consistent(*dim, *case) {
                self.worlds.prune_case(*dim, *case);
            }
        }
        _ => {}
    }
}
```

**3. Early Exit**

Stop as soon as unique world is found:

```rust
pub fn solve(&mut self) -> Result<Solution> {
    for constraint in &self.constraints {
        self.add_constraint(constraint)?;
        self.prune_inconsistent_worlds()?;

        // EARLY EXIT!
        if self.worlds.count_remaining_worlds() == 1 {
            return Ok(Solution::Unique(self.worlds.get_unique_world()));
        }

        if self.worlds.is_empty() {
            return Err(Error::NoValidWorlds);
        }
    }

    // ...
}
```

---

#### 17.8.2 Realistic Complexity

**Best case:** O(N + M) where N = #dimensions, M = #constraints
- Early pruning eliminates most worlds quickly
- Only one world survives after a few constraints

**Average case:** O(N × M × log W) where W = #worlds
- Some worlds survive longer
- Logarithmic because pruning is binary search-like

**Worst case:** O(W × M) where W = product of all alternatives
- All worlds survive until the end
- Must check consistency for each
- **But:** This is the same worst case as backtracking!

**In practice:** Early pruning is VERY effective for type-directed disambiguation

---

### 17.9 Complexity Comparison: Concrete Numbers

**Scenario:** 5 overloaded operators, each with 3 overloads

#### Backtracking

```
Try combinations sequentially:
  3 × 3 × 3 × 3 × 3 = 243 attempts (worst case)

Each attempt:
  - Save context: O(context_size)
  - Type-check: O(expr_size)
  - Restore context: O(context_size)

Total: O(243 × (context_size + expr_size))
```

**With early success:** O(1) if first try works
**With late success:** O(200+) tries before success

---

#### Variational

```
Generate constraints:
  5 dimensions × 3 cases = 15 constraint sets

Solve with pruning:
  Start: 3⁵ = 243 potential worlds
  After constraint 1: ~100 worlds (pruned half)
  After constraint 2: ~30 worlds
  After constraint 3: ~5 worlds
  After constraint 4: ~1 world (DONE!)

Total: O(15 + 5 × avg_worlds) ≈ O(15 + 5 × 30) = O(165)
```

**With early pruning:** O(15 + 10) = O(25) if pruning happens fast
**With late pruning:** O(15 + 5 × 200) = O(1015) same as backtracking

---

### 17.10 Implementation Complexity Assessment

**Lines of code estimate:**

```
Core data structures:        ~300 lines
  - ChoiceDim, World, etc.

SPPF elaboration:            ~400 lines
  - Convert SPPF to Expr::Choice

Variational type-checker:    ~600 lines
  - Handle Expr::Choice
  - Generate Choice constraints

Constraint solver:           ~800 lines
  - World pruning logic
  - Per-world bounds tracking

Error reporting:             ~500 lines
  - Show which worlds were pruned
  - Format error messages

Total: ~2600 lines (non-trivial but manageable)
```

**Compare to:**
- Backtracking type-checker: ~800 lines
- Strict disambiguation: ~400 lines

**Complexity ratio:** 3-6× more code than simple approaches

---

### 17.11 Recommended Implementation Strategy

**If you decide to implement variational constraints for HWML:**

#### Step 1: Minimal Prototype (Week 1-2)

```rust
// Just handle simple overloading, no SPPF
enum Constraint {
    Unify(Type, Type),
    Choice { dim: ChoiceDim, cases: Vec<(CaseId, Vec<Constraint>)> },
}

// Simple world pruning
fn solve(constraints: Vec<Constraint>) -> Result<World> {
    // Enumerate all worlds
    // Check each for consistency
    // Return unique or error
}
```

**Goal:** See if basic variational approach works

---

#### Step 2: Add SPPF Integration (Week 3-4)

```rust
// Add SPPF → Expr::Choice conversion
impl SPPFElaborator {
    fn elaborate_sppf(&mut self, node: SPPFNode) -> Expr {
        match node {
            SPPFNode::Ambiguous { alts } => {
                Expr::Choice { dim: fresh(), cases: elaborate_all(alts) }
            }
            // ...
        }
    }
}
```

**Goal:** Parse-level ambiguity → type-level resolution

---

#### Step 3: Optimize with Incremental Pruning (Week 5-6)

```rust
// Add lazy world enumeration
// Add early exit when unique world found
// Profile to find bottlenecks
```

**Goal:** Make it fast enough for real use

---

#### Step 4: Polish Error Messages (Week 7-8)

```rust
// Show which worlds were pruned and why
// Format nicely
// Add suggestions
```

**Goal:** Make it usable

---

### 17.12 Final Honest Assessment

**Question 1:** "What would it look like to implement?"

**Answer:** ~2600 lines of non-trivial but structured code. Data structures are straightforward, but solver logic requires care.

**Question 2:** "Can we interleave with parsing?"

**Answer:** Yes! Three-phase architecture:
1. Parse to SPPF (ambiguity-preserving)
2. Elaborate to variational Expr (choice introduction)
3. Type-check with pruning (disambiguation)

**Is it worth it?**

**Pros:**
- ✅ Elegant unification of parse and type ambiguity
- ✅ Can disambiguate mixfix based on types
- ✅ Better error messages (show all failures)
- ✅ No save/restore overhead

**Cons:**
- ❌ 3-6× more code than simple approaches
- ❌ Complexity in solver (world pruning is tricky)
- ❌ Potential performance issues if worlds explode
- ❌ Debugging is harder (worlds are abstract)

**Recommendation:**

1. **Start simple:** Strict disambiguation or suspended constraints
2. **Measure:** How often are annotations needed?
3. **Prototype:** If burden is high, try minimal variational prototype
4. **Evaluate:** Does early pruning actually happen in practice?
5. **Decide:** Only commit to full implementation if prototype shows benefits

**Don't build variational constraints because they're theoretically elegant.**
Build them because user studies show annotation burden is intolerable AND profiling shows early pruning is effective.

The architecture is FEASIBLE, but the EFFORT is SIGNIFICANT. Make sure the benefits justify the cost!
- Using **flow-based constraints** (matches human reasoning)
- **Deferring choices** (better inference = fewer annotations)
- **Compositional design** (scales to new features automatically)

**For HWML:** No-ambiguity is NOT necessary for good errors. In fact, embracing variational ambiguity enables BETTER errors!

**References for Section 15:**
- Rust error codes: E0282 "type annotations needed"
- Rust issues: #139168, #99882
- Elm releases: 0.9, 0.15.1, 0.16, 0.19.1
- Elm issues: #911, #1739
- GHC proposals: #232 "Ambiguous Type per-signature pragma"
- TypeScript docs: "Understanding Errors"
- Haskell docs: "Ambiguous types and the ambiguity check"





