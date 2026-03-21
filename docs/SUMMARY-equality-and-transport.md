# Summary: Equality Proofs and Transport in hwml-rust

This document provides a comprehensive overview of how equality proofs, the `transport` primitive, and dependent pattern matching work together in hwml-rust.

## Quick Reference

### Key Concepts

1. **Equality Type**: `Eq A x y` - Propositional equality between `x` and `y` of type `A`
2. **Refl Constructor**: `refl : Eq A x x` - Proof of reflexivity
3. **Transport Primitive**: `transport VALUE to MOTIVE by PROOF` - Uses equality proofs to cast values
4. **Axiom K**: All proofs of `x = x` are equal (enables simple pattern matching)
5. **Type Refinement**: Matching on `refl` tells the type checker that two types are equal

### Syntax

**New Transport Syntax** (as of this implementation):
```
transport VALUE to MOTIVE by PROOF
```

Where:
- `VALUE`: The value to transport (type: `MOTIVE(a)`)
- `MOTIVE`: A lambda describing the type family (e.g., `λ %i → Vec Unit %i`)
- `PROOF`: An equality proof `Eq A a b`
- Result type: `MOTIVE(b)`

**Old syntax** (deprecated): `transport MOTIVE PROOF VALUE`

## Documentation Files

### 1. `transport-example.md` - Complete Working Examples

**What it covers**:
- Overview of the `transport` primitive and Axiom J
- **Example 1**: Simple transport with Bit (constant motive)
- **Example 2**: Dependent pattern matching on Vec (the main use case)
  - Shows the complete elaboration pipeline
  - Demonstrates how transport solves the "stuck on complex index" problem
- **Example 3**: Actual test case from `test_check_transport`
  - Real working example with identity motive
  - Shows type casting from `A` to `B` using proof `Eq U0 A B`
- **Example 4**: Vec exhaustiveness checking
  - Why `Vec a @Zero` only requires `@VNil`
  - Contrast with `Vec a n` requiring both constructors
- **Example 5**: Pattern matching on equality proofs (type refinement)
  - Conceptual explanation of how matching `refl` refines types
  - Current implementation status
  - How it works in the core

**Key insight**: Transport nodes vanish at runtime when the proof is `refl` (zero cost abstraction)

### 2. `equality-pattern-matching-example.md` - Concrete Runnable Example

**What it covers**:
- The problem: Using equality proofs to refine types
- The solution: Pattern matching on `refl`
- Implementation status (what's done vs. in development)
- **Runnable test code** demonstrating type refinement
- How pattern matching would work in the future surface syntax
- Step-by-step explanation of type checking

**Key example**:
```rust
// Context: [A : U0, B : U0, p : Eq U0 A B, x : A]
// Goal: Cast x from type A to type B

transport x to (λ y → y) by p  // Result: x : B
```

**How to run**:
```bash
cargo test -p hwml_core test_check_transport -- --nocapture
```

## Implementation Status

### ✅ Fully Implemented (hwml-core)

1. **Core Syntax**:
   - `Eq` type constructor
   - `refl` constructor
   - `transport` primitive with new keyword syntax
   - `case` expressions

2. **Type Checking**:
   - Checking `Eq` types
   - Checking `refl` proofs
   - Synthesizing types for `transport`
   - Pattern unification with Axiom K

3. **Evaluation (NbE)**:
   - `transport ... by refl` → deletes transport (zero cost!)
   - `transport ... by neutral` → stuck neutral value
   - Case reduction on data constructors

4. **Pattern Unification**:
   - Axiom K: `refl ~ refl` always succeeds
   - Injectivity of constructors
   - Equation solving with substitutions
   - δ-reduction support (let-bound variables)

### 🚧 In Development (hwml-elab)

1. **Surface Syntax**:
   - `match p { refl => ... }` for equality proofs
   - Full dependent pattern matching syntax

2. **Elaborator**:
   - Automatic transport generation for dependent variables
   - Motive synthesis from expected types
   - Pattern matrix compilation with equality proofs

3. **Integration**:
   - End-to-end pipeline from surface syntax to core IR
   - Error messages for pattern matching failures

## Key Files in the Codebase

### Core Language (`crates/hwml-core/src/`)

- **`val.rs`**: Value representation
  - `Value::EqType` - Equality types
  - `Value::Refl` - Reflexivity proofs
  - `Value::Transport` - Transport values

- **`syn/syntax.rs`**: Syntax representation
  - `Syntax::Eq` - Equality type syntax
  - `Syntax::Refl` - Refl constructor syntax
  - `Syntax::Transport` - Transport syntax

- **`syn/parse.rs`**: Parser
  - `p_transport()` - Parses `transport VALUE to MOTIVE by PROOF`
  - `p_to()`, `p_by()` - Keyword parsers

- **`syn/print.rs`**: Printer
  - `Transport::print()` - Prints new keyword syntax

- **`check.rs`**: Type checker
  - `type_check_eq()` - Checks equality types
  - `type_check_refl()` - Checks refl proofs
  - `type_check_transport()` - Checks transport expressions
  - `type_check_case()` - Checks case expressions with exhaustiveness

- **`eval.rs`**: Evaluator (NbE)
  - `eval_transport()` - Evaluates transport (deletes when proof is refl)
  - `eval_case()` - Evaluates case expressions

- **`pattern_unify.rs`**: Pattern unification
  - `unify_pattern()` - Unifies patterns with scrutinee types
  - Axiom K implementation
  - Equation solving

- **`equal.rs`**: Conversion checking
  - `equate_eq_instances()` - Checks equality of equality proofs
  - `equate_transports()` - Checks equality of transport terms

### Elaborator (`crates/hwml-elab/src/`)

- **`elaborator.rs`**: Main elaboration logic
  - `check_match()` - Elaborates match expressions
  - `compile_matrix()` - Pattern matrix compilation
  - `parse_pattern()` - Parses surface patterns

- **`rules.rs`**: Typing rules
  - `form_eq()` - Forms equality types
  - `intro_refl()` - Introduces refl proofs
  - `elim_transport()` - Eliminates via transport
  - `form_case()` - Forms case expressions

## Testing

### Running Tests

```bash
# All hwml-core tests
cargo test -p hwml_core

# Specific transport test
cargo test -p hwml_core test_check_transport

# Equality type tests
cargo test -p hwml_core test_check_eq

# Pattern unification tests
cargo test -p hwml_core pattern_unify

# All workspace tests
cargo test --workspace
```

### Key Test Cases

1. **`test_check_transport`**: Basic transport type checking
2. **`test_check_eq_type`**: Equality type formation
3. **`test_check_refl`**: Refl constructor checking
4. **`test_vec_at_zero_only_requires_vnil`**: Exhaustiveness with concrete indices
5. **`test_vec_at_variable_requires_both_constructors`**: Exhaustiveness with variable indices
6. **`test_let_delta_reduction_in_equality`**: δ-reduction in conversion checking

## How-To Guide

### How to Use Transport in hwml-core

**Step 1: Build the context**
```rust
let db = Database::default();
let global = GlobalEnv::new();
let mut env = check::TypeCheckEnv::new(&db, &global);

// Add variables to context
let u0 = Rc::new(Value::universe(UniverseLevel::new(0)));
let a = env.push_var(u0.clone());  // A : U0
let b = env.push_var(u0.clone());  // B : U0
```

**Step 2: Create an equality proof**
```rust
// Create proof type: Eq U0 A B
let eq_ty = Rc::new(Value::eq(u0.clone(), a.clone(), b.clone()));
env.push_var(eq_ty);  // p : Eq U0 A B
```

**Step 3: Add a value to transport**
```rust
env.push_var(a.clone());  // x : A
```

**Step 4: Construct the transport expression**
```rust
// transport x to (λ y → y) by p
let transport = syn::parse::parse_syntax_at_depth(
    &db,
    "transport %0 to λ %y → %y by %1",
    4  // depth = number of variables in scope
).expect("should parse");
```

**Step 5: Type check**
```rust
let result = check::type_synth(&mut env, &transport);
assert!(result.is_ok());
// Result type is B!
```

### How to Write Equality Proofs

**Reflexivity** (most common):
```
refl : Eq A x x
```

**Using let-bindings** (for complex terms):
```
let y = (n + n);
let h : Eq Nat (n + n) y = refl;
```

**In context** (as a hypothesis):
```
// Function parameter
λ %p : Eq Nat x y → ...
```

### How to Pattern Match on Equality (Core Level)

**Step 1: Bind the proof to a variable**
```
let scrut = p;
```

**Step 2: Create a case expression**
```
scrut case {
  @refl => body
}
```

**Step 3: In the branch, types are refined**
```
// If scrut : Eq A x y
// After matching @refl, we know x = y
// All occurrences of x can be replaced with y (or vice versa)
```

### Common Patterns

**Pattern 1: Type Casting**
```
// Cast x : A to type B using proof p : Eq Type A B
transport x to (λ t → t) by p
```

**Pattern 2: Index Alignment**
```
// Cast v : Vec A (f n) to Vec A m using proof h : Eq Nat (f n) m
transport v to (λ i → Vec A i) by h
```

**Pattern 3: Dependent Return Types**
```
// Function with dependent return type that changes based on equality
λ %p : Eq Nat n m →
  p case {
    @refl => ...  // Here n = m, so types can be unified
  }
```

## Design Principles

### 1. Separation of Concerns

- **Core Language**: Simple, primitive constructs (`Eq`, `refl`, `transport`, `case`)
- **Elaborator**: Complex transformations (motive synthesis, transport insertion)
- **Evaluator**: Optimization (transport deletion, case reduction)

### 2. Zero-Cost Abstraction

Transport nodes are compile-time scaffolding:
- Type checker sees them and verifies correctness
- Evaluator deletes them when proof is `refl`
- Runtime performance is unaffected

### 3. Axiom K for Simplicity

By adopting Axiom K (all proofs of `x = x` are equal):
- Pattern unification is straightforward
- No need for proof relevance tracking
- Simpler core language and faster type checking

Trade-off: Not compatible with HoTT/Cubical Type Theory (but that's OK for hardware!)

### 4. Dependent Pattern Matching via Elaboration

- Surface syntax: User-friendly pattern matching
- Core syntax: Only match on variables
- Elaborator bridges the gap using `let`, `Eq`, and `transport`

## Future Work

### Short Term (hwml-elab)

1. Complete pattern matrix compiler for equality proofs
2. Automatic motive synthesis
3. Surface syntax for `match p { refl => ... }`
4. Better error messages for non-exhaustive patterns

### Medium Term

1. Heterogeneous equality (for more expressive proofs)
2. Proof automation (auto-generate simple equality proofs)
3. Rewrite tactics (user-directed transport insertion)

### Long Term

1. Proof irrelevance optimization (erase proofs at runtime)
2. Compile-time proof checking (verify proofs without runtime overhead)
3. Integration with SMT solvers (for complex equality reasoning)

## References

### Design Documents

- `design/pattern-matching.md` - Comprehensive guide to pattern matching compilation
  - Sections on motive-free case expressions
  - Pattern unification algorithm
  - Axiom K explanation
  - Transport primitive design

### Related Code

- `crates/hwml-core/src/test_utils.rs` - Test utilities including `VEC_PRELUDE`
- `crates/hwml-elab/src/test_utils.rs` - Elaborator test utilities

### Academic Background

- **Axiom J**: The J eliminator from Martin-Löf Type Theory
- **Axiom K**: Uniqueness of Identity Proofs (Streicher)
- **Dependent Pattern Matching**: Coquand, McBride, Norell (Agda/Epigram)
- **Transport**: Path induction in Homotopy Type Theory

## Conclusion

The equality proof and transport system in hwml-rust provides a solid foundation for dependent pattern matching:

✅ **Core language is complete** - All primitives are implemented and tested
✅ **Type checking is sound** - Pattern unification with Axiom K works correctly
✅ **Evaluation is efficient** - Transport nodes vanish at runtime
🚧 **Surface syntax is in progress** - Elaborator is being developed

The infrastructure is ready for full dependent pattern matching in the surface language!


