# Parse Forest Type Disambiguation: Backtracking-Free Type-Checking

**Created:** 2026-05-06
**Type:** Deep Dive Analysis
**Research Question:** Can we separate parsing backtracking from type-checking backtracking?
**Confidence:** 0.90

---

## Executive Summary

**YES, it is possible to avoid type-checker backtracking** while allowing parsing backtracking. The key insight:

**Use a Shared Packed Parse Forest (SPPF) + Post-Parse Disambiguation Filters**

### The Architecture

```
Input → Generalized Parser → SPPF (all parses) → Constraint Generation
                                                         ↓
                                                 (no type-checking yet!)
                                                         ↓
                                            Disambiguation Filter
                                            (uses type constraints)
                                                         ↓
                                                  Single Parse Tree
                                                         ↓
                                                  Type-Check Once
                                                  (no backtracking)
```

**Key Innovation:** Parse ambiguity is **represented**, not **resolved**. Type information is used to **prune** the SPPF, not to **retry** type-checking.

---

## 1. The Core Problem

### 1.1 Traditional Type-Directed Parsing (BAD)

**Interleaved approach:**
```
1. Parse expression partially
2. Type-check to resolve ambiguity
3. If type-check fails, BACKTRACK
4. Try alternative parse
5. Type-check again
6. Repeat until success or exhaustion
```

**Problem:** Type-checker state must be rolled back on failure!
- Expensive to save/restore
- Errors are confusing (which attempt failed?)
- Not compositional

### 1.2 The SPPF Approach (GOOD)

**Separated approach:**
```
1. Parse expression (produce SPPF with all ambiguities)
2. Generate constraints for ALL possible parses (lazily)
3. Use constraint SATISFIABILITY to prune SPPF
4. Extract single parse tree
5. Type-check once (no backtracking)
```

**Advantage:** Type-checker never backtracks! It only runs on the final, disambiguated tree.

---

## 2. Shared Packed Parse Forests (SPPFs)

### 2.1 What is an SPPF?

**Definition:** A DAG (directed acyclic graph) that compactly represents all parse trees for an input.

**Key properties:**
- **Sharing:** Common subtrees stored once
- **Packing:** Ambiguous alternatives stored as "choice nodes"
- **Size:** O(n³) worst case (polynomial, not exponential!)

### 2.2 Structure

```
SPPF Node Types:
1. Symbol Node: Represents a grammar symbol (terminal/nonterminal)
2. Packed Node: Represents an alternative production
3. Intermediate Node: For binarization
```

**Example:** Parsing `a + b * c` with ambiguous precedence

```
      Expr
     /    \
   [amb]  [amb]  ← Packed nodes (choice points)
   /  \    /  \
  +    *  *    +
 / \  / \/  \ / \
a  b b  c a  b  c
```

**Compact representation:** Shared `a`, `b`, `c` nodes, only branching at ambiguity.

### 2.3 GLL/GLR Parsers

**Generalized parsers** that build SPPFs:
- **GLR (Generalized LR):** Bottom-up, Tomita's algorithm (1985)
- **GLL (Generalized LL):** Top-down, Scott & Johnstone (2010)

**Complexity:** O(n³) time and space for any CFG (even ambiguous!)

**Key advantage:** No exponential blowup from ambiguity.

---

## 3. Post-Parse Disambiguation Filters

### 3.1 What is a Disambiguation Filter?

**Definition:** A function `Filter :: SPPF → SPPF` that removes undesired parse trees.

**Types of filters:**

1. **Syntactic filters:** Priority, associativity, longest match
   - Applied during parsing or immediately after
   - Don't need semantic info

2. **Semantic filters:** Type information, scope resolution
   - Applied after SPPF is built
   - Use type constraints to prune

3. **Heuristic filters:** Statistical, ML-based
   - For cases with no definitive answer

### 3.2 Type-Directed Disambiguation Filter

**Algorithm:**

```rust
fn type_disambiguate(sppf: SPPF, expected_type: Type) -> SPPF {
    // For each packed node (ambiguity)
    for amb_node in sppf.packed_nodes() {
        let candidates = amb_node.alternatives();

        // Generate constraints for each alternative (lazily)
        let valid_alts = candidates.filter(|alt| {
            let constraints = generate_constraints(alt, expected_type);
            // Key: Check SATISFIABILITY, don't actually solve!
            constraint_solver.is_satisfiable(constraints)
        });


---

## 7. Real-World Examples

### 7.1 C++ Parsing (Google Clang Pseudo)

**Problem:** C++ grammar is highly ambiguous (e.g., `T * x` declaration vs multiplication)

**Solution (from Clang Pseudo documentation):**
> "The GLR parser produces a forest of parses, represented compactly by a DAG. A real C++ parser finds the correct parse through semantic analysis: mostly resolving names. **But we can't do that, as we don't parse the headers.**
>
> Our disambiguation phase should take the parse forest, and choose a single parse tree that is most likely."

**Their approach:**
1. Parse to SPPF (GLR)
2. Apply heuristic disambiguation filters
3. For each ambiguous node, score alternatives
4. Pick highest-scoring parse

**Note:** They don't have full type info, but the architecture is the same!

### 7.2 SDF (Syntax Definition Formalism)

**System:** Scannerless Generalized LR (SGLR) parser generator

**Features:**
- Declarative disambiguation: `left`, `right`, `prefer`, `avoid`, `reject`
- Post-parse filters on SPPF
- Semantic filters can use external info

**Example disambiguation:**
```sdf
syntax Exp ::= Exp "*" Exp {left}
            |  Exp "+" Exp {left}
            |  INT

priorities {
  Exp "*" Exp > Exp "+" Exp
}
```

**Implementation:**
1. Parse to SPPF (includes all precedences/associativities)
2. Filter SPPF based on `priorities` declaration
3. Filter based on `left`/`right` annotations
4. Result: Single parse tree

**Key:** Disambiguation is **declarative** and happens **after parsing**.

### 7.3 Lean 4 Dot Notation Resolution

**Problem:** `x.f` could mean:
- Field projection `x.f`
- Function call `f x`
- Namespaced call `X.f x` where `X = typeof(x)`

**Current approach (from Lean source):**
1. Parse `x.f` as syntax node
2. Elaborate `x` to get type `τ`
3. Try all resolution strategies:
   - If fails, **BACKTRACK** elaboration of `x`
   - Try alternative strategy

**Better approach with SPPF:**
1. Parse `x.f` (unambiguous syntax)
2. Generate constraint: `typeof(x) = τ ∧ has_member(τ, f) ∨ exists_function(f, τ → _)`
3. Solve constraint (suspends on `typeof(x)`)
4. When `x` is elaborated, constraint resumes
5. Pick valid alternative
6. **NO BACKTRACKING**

---

## 8. Handling Disjunctive Constraints

### 8.1 The Challenge

**Disjunctive constraint:** `C1 ∨ C2 ∨ ... ∨ Cn`

**Example:** Overloaded operator `+` with 3 definitions:
```
(+) : Int → Int → Int
(+) : Float → Float → Float
(+) : String → String → String

Expression: x + y
Constraint: (typeof(x) = Int ∧ typeof(y) = Int ∧ typeof(x+y) = Int)
          ∨ (typeof(x) = Float ∧ typeof(y) = Float ∧ typeof(x+y) = Float)
          ∨ (typeof(x) = String ∧ typeof(y) = String ∧ typeof(x+y) = String)
```

**Question:** How to check satisfiability of disjunction without solving?

### 8.2 Solution: Incremental Pruning

**Algorithm:**

```rust
fn check_disjunction(alts: Vec<ConstraintSet>, ctx: Context) -> SatResult {
    let mut remaining = alts;

    // Prune obviously unsatisfiable alternatives
    remaining.retain(|c| !obviously_unsat(c, ctx));

    match remaining.len() {
        0 => Unsat,                    // No alternatives left
        1 => Sat(remaining[0]),        // Unique solution!
        _ => StillAmbiguous(remaining) // Multiple valid alternatives
    }
}

fn obviously_unsat(c: ConstraintSet, ctx: Context) -> bool {
    // Fast checks that don't require full solving:
    // 1. Direct contradictions: (α = Int ∧ α = String)
    // 2. Occurs check violations: (α = List<α>)
    // 3. Known incompatibilities from context: (x : Int in ctx) ∧ (x : String in c)

    c.has_contradiction() || c.fails_occurs_check() || ctx.conflicts_with(c)
}
```

**Key optimization:** Most alternatives are eliminated quickly!

### 8.3 Variational Type Checking (Beneš 2025)

**Paper:** "Flow-Based Variational Type-Checking"

**Key idea:** Represent overloads as **choices** in a choice calculus:

```
x + y  ≈  choice {
  case Int: (+Int) x y,
  case Float: (+Float) x y,
  case String: (+String) x y
}
```

**Type-check once with choices:**
```
typeof(choice { case K1: e1, case K2: e2, ... }) =
  choice { case K1: typeof(e1), case K2: typeof(e2), ... }
```

**Propagate choices through unification:**
- Unify `choice { Int, Float }` with `Float`
- Result: Eliminate `Int` choice, keep `Float`
- NO BACKTRACKING!

**Apply to SPPF:**
- Ambiguous parse = choice point
- Generate constraints with choices
- Unification eliminates invalid choices
- Remaining choice = valid parse

---

## 9. Connection to Suspended Elaboration

### 9.1 Unified Framework

**All these techniques are instances of:**

```rust
enum Constraint {
    Unify(Type, Type),

    // SUSPENSION: Wait for more info
    Suspended {
        blocked_on: Vec<MetaVar>,
        resume: Box<dyn FnOnce(Substitution) -> Constraint>,
    },

    // DISJUNCTION: Multiple possibilities
    Choice {
        alternatives: Vec<ConstraintSet>,
        source: ChoiceSource,  // Parse ambiguity, overloading, etc.
    },
}

enum ChoiceSource {
    ParseAmbiguity(SPPFNode),      // From SPPF
    Overloading(Symbol, Vec<Def>), // From type-directed overload resolution
    DotNotation(Expr, Field),      // From universal dot notation
}
```

### 9.2 Constraint Solving with Choices

**Algorithm:**

```rust
fn solve_constraints(cs: ConstraintSet) -> Result<Substitution> {
    let mut subst = Substitution::empty();
    let mut suspended = Vec::new();
    let mut choices = Vec::new();

    for c in cs {
        match c {
            Unify(t1, t2) => {
                subst.compose(unify(t1, t2)?);
            }

            Suspended { blocked_on, resume } => {
                if blocked_on.all_known_in(&subst) {
                    // Resume immediately
                    let resumed = resume(subst.clone());
                    solve_constraint(resumed)?;
                } else {
                    // Still blocked, keep suspended
                    suspended.push(c);
                }
            }

            Choice { alternatives, source } => {
                let valid = alternatives.filter(|alt| {
                    is_satisfiable(alt.apply(&subst))
                });

                match valid.count() {
                    0 => return Err(NoValidAlternative(source)),
                    1 => solve_constraints(valid.single())?,
                    _ => choices.push(Choice { valid, source }),
                }
            }
        }
    }

    // Fixpoint: Resume suspended constraints, prune choices
    if suspended.is_empty() && choices.is_empty() {
        Ok(subst)
    } else if made_progress() {
        solve_constraints(suspended + choices)  // Recurse
    } else {
        Err(StillAmbiguous { suspended, choices })
    }
}
```

**Key insight:** Suspended constraints and choice constraints work together!
- Suspension: "Wait for type variable α"
- Choice: "Multiple parses, wait for type info to disambiguate"
- When α is unified, both resume/prune simultaneously

---

## 10. Comparison with Backtracking

### 10.1 Backtracking Type-Checking

```rust
fn typecheck_with_backtracking(expr: AmbiguousExpr) -> Result<Type> {
    for parse in expr.possible_parses() {
        // Save type-checker state
        let checkpoint = typestate.checkpoint();

        match typecheck(parse) {
            Ok(t) => return Ok(t),  // Success!
            Err(e) => {
                // BACKTRACK: Restore state
                typestate.restore(checkpoint);
                continue;  // Try next parse
            }
        }
    }

    Err("No valid parse")
}
```

**Problems:**
1. ❌ Expensive: Must save/restore entire type environment
2. ❌ Exponential: Tries all parses even if type is immediately wrong
3. ❌ Poor errors: Which attempt should we report?
4. ❌ Not compositional: Inner and outer ambiguities interact badly

### 10.2 SPPF + Constraint Pruning

```rust
fn typecheck_with_sppf(expr: AmbiguousExpr) -> Result<Type> {
    let sppf = parse_to_sppf(expr);

    // Generate constraints for ALL parses (lazily)
    let mut constraints = lazy_constraints(sppf);

    // Prune based on satisfiability
    for amb_node in sppf.ambiguities() {
        let valid = amb_node.alternatives().filter(|alt| {
            // NO TYPE-CHECKING, just satisfiability check!
            constraints.for_alternative(alt).is_satisfiable()
        });

        amb_node.keep_only(valid);
    }

    let tree = sppf.extract_unique_tree()?;

    // Type-check ONCE on unambiguous tree
    typecheck(tree)
}
```

**Advantages:**
1. ✅ Cheap: No state save/restore
2. ✅ Polynomial: Prunes early based on types
3. ✅ Good errors: Can report all valid parses if still ambiguous
4. ✅ Compositional: Inner and outer constraints compose naturally

---

## 11. HWML Implementation Roadmap

### 11.1 Phase 1: Simple Pratt + Suspended Constraints

**Goal:** Type-directed disambiguation without parse ambiguity

**Implementation:**
- Pratt parser (deterministic, no SPPF needed)
- Add `Suspended` constraint type
- Use for dot notation, overload resolution

**Example:** Dot notation `x.f`
```rust
// Parse is unambiguous: DotAccess(x, f)
// But elaboration is suspended:

fn elaborate_dot(x: Expr, f: Field) -> Constraint {
    let α = fresh_var();
    Suspended {
        blocked_on: vec![typeof(x)],
        resume: |subst| {
            let tx = subst.apply(typeof(x));
            // Now we know type, resolve field/method
            resolve_field_or_method(tx, f)
        }
    }
}
```

**Benefit:** Learn suspended constraints without parse forests.

### 11.2 Phase 2: Add Precedence DAG + Choice Constraints

**Goal:** Handle precedence ambiguity via constraints

**Implementation:**
- Replace precedence numbers with DAG
- When precedence is ambiguous, emit `Choice` constraint
- Prune based on type information

**Example:** Ambiguous precedence `a * b / c`
```rust
// If * and / are incomparable:
Choice {
    alternatives: [
        parse_as(a * (b / c)),  // Right assoc
        parse_as((a * b) / c),  // Left assoc
    ],
    source: PrecedenceAmbiguity
}

// Generate constraints for both, prune based on types
```

### 11.3 Phase 3: Full SPPF Support

**Goal:** Handle arbitrary ambiguity (mixfix, etc.)

**Implementation:**
- Integrate GLL parser (generates SPPF)
- Lazy constraint generation for SPPF nodes
- Post-parse disambiguation filter

**Libraries:**
- **Rust GLL:** `gll` crate by Goyvaerts
- **SPPF manipulation:** Custom (based on Klint & Visser)

### 11.4 Phase 4: Optimization

**Goal:** Make it fast

**Optimizations:**
1. **Memoisation:** Cache satisfiability results per SPPF node
2. **Early pruning:** Eliminate alternatives as soon as types are known
3. **Incremental:** Re-use SPPF/constraints across edits (LSP)
4. **Heuristics:** When multiple valid parses, use simplicity/style heuristics

---

## 12. Key Takeaways

### 12.1 Summary

✅ **YES, we can separate parsing backtracking from type-checking backtracking**

**The technique:**
1. Parse to SPPF (all ambiguities preserved)
2. Generate constraints for alternatives (lazily)
3. Check satisfiability to prune alternatives
4. Extract unique parse tree
5. Type-check once (no backtracking!)

### 12.2 Core Insights

1. **SPPFs are polynomial:** O(n³) even for ambiguous grammars
2. **Satisfiability ≠ Solving:** Checking if solution exists is cheaper than finding it
3. **Lazy generation:** Don't generate constraints for pruned alternatives
4. **Suspension + Choice:** Unified framework for type-directed disambiguation

### 12.3 Practical Benefits

| Aspect | Backtracking | SPPF + Constraints |
|--------|-------------|-------------------|
| **Type-checker state** | Save/restore | Never backtracks |
| **Complexity** | Exponential attempts | Polynomial pruning |
| **Error messages** | Which attempt? | All valid parses |
| **Compositionality** | Poor (nested backtracking) | Good (constraints compose) |
| **Incremental** | Hard (state diverges) | Easy (SPPF is stable) |

### 12.4 Recommended for HWML

**Start simple, add complexity incrementally:**

1. **Now:** Pratt parser + suspended constraints (for dot notation)
2. **Soon:** Precedence DAG + choice constraints (for modular precedence)
3. **Later:** GLL + SPPF (for mixfix, if needed)

**Key principle:** Parse ambiguity is **data** (SPPF), not **control flow** (backtracking).

---

## 13. References

### 13.1 Parse Forests

1. **Scott & Johnstone:** "GLL Parsing" (2010) - GLL algorithm with SPPF
2. **Tomita:** "Efficient Parsing for Natural Language" (1985) - GLR parsing
3. **Klint & Visser:** "Using Filters for Disambiguation" (SDF, 1994)
4. **van den Brand et al.:** "Disambiguation Filters for SGLR" (2002)

### 13.2 Type-Directed Disambiguation

5. **Scherer et al.:** "Frozen Inference Constraints" (ML Workshop 2021)
6. **Beneš:** "Flow-Based Variational Type-Checking" (2025)
7. **Chargueraud:** "Two-Pass Algorithm for Type Inference" (2025)

### 13.3 Constraint-Based Type Inference

8. **Pottier & Rémy:** "The Essence of ML Type Inference" (2005)
9. **Sulzmann et al.:** "Simplifying Type Inference" (1999)
10. **Odersky et al.:** "Type Inference with Constrained Types" (1999)

### 13.4 Tools & Systems

11. **SDF/Spoofax:** Scannerless parsing with disambiguation filters
12. **Clang Pseudo:** C++ GLR parser with heuristic disambiguation
13. **Lark Parser:** Python library with SPPF support
14. **ANTLR:** Can generate GLR parsers with parse forest output

---

## 14. Conclusion

**The answer to your question is a resounding YES.**

Not only is it possible to avoid type-checker backtracking while allowing parse-level backtracking, **it's the superior architecture**:

- More efficient (polynomial vs exponential)
- Better error messages (can show all valid parses)
- More compositional (constraints compose, backtracking doesn't)
- Easier to implement incrementally

The key innovations needed:
1. **SPPF representation** (GLL/GLR parsers)
2. **Lazy constraint generation** (don't elaborate all alternatives)
3. **Satisfiability checking** (prune without solving)
4. **Suspended + Choice constraints** (unified framework)

This architecture has been proven in production systems (SDF, Clang Pseudo) and is actively researched in academia (frozen constraints, variational typing).

**For HWML:** This should be the long-term architecture. Start simple (Pratt + suspension), evolve toward SPPF as needed.
            _ => amb_node.keep_alternatives(valid_alts), // Still ambiguous
        }
    }

    sppf
}
```

**Key insight:** We check if constraints **CAN** be satisfied, we don't **SOLVE** them yet!

---

## 4. Constraint Generation WITHOUT Type-Checking

### 4.1 The Separation

**Traditional:**
```rust
// INTERLEAVED: Generate + Solve
fn typecheck(expr: Expr) -> Result<Type> {
    match expr {
        App(f, x) => {
            let tf = typecheck(f)?;  // Solve recursively
            let tx = typecheck(x)?;  // Solve recursively
            unify(tf, Arrow(tx, α))?; // Solve immediately
            Ok(α)
        }
    }
}
```

**Our approach:**
```rust
// SEPARATED: Generate, then solve later
fn generate_constraints(expr: Expr, expected: Type) -> ConstraintSet {
    match expr {
        App(f, x) => {
            let α = fresh_var();
            let β = fresh_var();
            ConstraintSet::new()
                .add(generate_constraints(f, Arrow(β, α)))
                .add(generate_constraints(x, β))
                .add(Equality(expected, α))
            // NO SOLVING HERE!
        }
    }
}
```

### 4.2 Lazy Constraint Generation for SPPFs

**Key optimization:** Don't generate constraints for ALL parses upfront!

```rust
struct LazyConstraints {
    sppf: SPPF,
    cache: HashMap<NodeId, ConstraintSet>,
}

impl LazyConstraints {
    fn constraints_for(&mut self, node: NodeId) -> ConstraintSet {
        if let Some(cached) = self.cache.get(&node) {
            return cached.clone();
        }

        let constraints = match self.sppf.node(node) {
            PackedNode(alts) => {
                // Disjunction: (C1 ∨ C2 ∨ ...)
                Disjunction(alts.map(|alt| self.constraints_for(alt)))
            }
            SymbolNode(children) => {
                // Conjunction: (C1 ∧ C2 ∧ ...)
                Conjunction(children.map(|c| self.constraints_for(c)))
            }
        };

        self.cache.insert(node, constraints.clone());
        constraints
    }
}
```

---

## 5. Research Evidence

### 5.1 "Frozen Constraints" (Scherer et al., 2021)

**Paper:** "Frozen inference constraints for type-directed disambiguation" (ML Workshop 2021)

**Key idea:** "Frozen constraint" = suspension point

```ocaml
type constraint =
  | Equality of typ * typ
  | Frozen of {
      wait_on: type_var,
      resume: typ -> constraint
    }
```

**Important quote from paper:**
> "This use of frozen constraints does not try to disambiguate constructors in all possible cases... **We don't guess, we wait for** [type information]."

**Application:** OCaml variant constructor disambiguation
- Parse `K(x)` where `K` is ambiguous
- Generate frozen constraint: "When type of this expression is known, resolve K"
- NO BACKTRACKING in type inference!

### 5.2 "Disambiguation Filters for SGLR" (Klint & Visser, 1994)

**Paper:** "Using filters for the disambiguation of context-free grammars"

**Key insight:**
> "Disambiguation encompasses the whole spectrum from simple priority declarations for resolving ambiguities... to **the use of semantic (e.g., type) information for pruning the parse forest**."

**Architecture:**
```
Parser → SPPF → Syntactic Filters → Semantic Filters → Single Tree
```

**Semantic filter example:** C++ `T * x` (declaration vs multiplication)
- Parse both interpretations
- Generate constraints: "Is T a type?" vs "Is T a value?"
- Use symbol table to prune
- NO type-checker backtracking

### 5.3 "Omnidirectional Type Inference" (POPL 2024)

**Paper:** Constraints solve in any order with dynamic suspension/resumption

**Key quote:**
> "Constraints advance dynamically; those that require known type information **suspend**, and resume when other constraints supply it."

**Mechanism:**
```
match α with
  | Known(τ) => solve_immediately(τ)
  | Unknown => suspend(α, resume_when_known)
```

**Application to disambiguation:**
- Ambiguous parse creates disjunctive constraint: `(C1 ∨ C2)`
- Try to solve `C1` → suspends on unknown type `α`
- Try to solve `C2` → suspends on unknown type `α`
- Later, `α` is unified with concrete type
- Resume both: `C1` fails, `C2` succeeds
- **Prune parse alternative 1**, keep alternative 2
- NO BACKTRACKING!

---

## 6. Practical Implementation Strategy

### 6.1 Three-Phase Architecture

**Phase 1: Parse to SPPF**
```rust
fn parse(input: &str) -> SPPF {
    // Use GLL or GLR parser
    // Returns SPPF with all ambiguities
    gll_parse(grammar, input)
}
```

**Phase 2: Disambiguate with Types**
```rust
fn disambiguate(sppf: SPPF, context: TypeContext) -> ParseTree {
    let constraints = LazyConstraints::new(sppf);

    for amb_node in sppf.ambiguities() {
        let alts = amb_node.alternatives();
        let valid = alts.filter(|alt| {
            let c = constraints.for_subtree(alt);
            // Check satisfiability WITHOUT solving!
            solver.is_sat(c)
        });

        match valid.count() {
            0 => return Err("No valid parse"),
            1 => amb_node.resolve(valid.single()),
            n => /* heuristic or error */
        }
    }

    sppf.extract_tree()
}
```

**Phase 3: Type-Check Once**
```rust
fn typecheck(tree: ParseTree) -> Result<TypedAST> {
    // Traditional type-checking
    // NO BACKTRACKING (tree is unambiguous)
    elaborate(tree)
}
```

### 6.2 Satisfiability Checking

**Key question:** How to check constraint satisfiability without solving?

**Answer:** Use constraint solver's internal mechanisms:

```rust
trait ConstraintSolver {
    // SOLVE: Find substitution θ such that θ(C) is satisfied
    fn solve(&mut self, c: Constraint) -> Result<Substitution>;

    // IS_SAT: Check if SOME substitution exists (don't compute it)
    fn is_sat(&self, c: Constraint) -> bool;
}
```

**Implementation:** Most solvers support this!
- **Unification:** Occurs check, cycle detection
- **SAT/SMT:** Built-in satisfiability checking
- **Higher-order unification:** Pattern fragment decidability check

**Optimization:** Cache satisfiability results per SPPF node.

