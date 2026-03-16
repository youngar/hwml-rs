# hwml-rust Documentation

This directory contains technical documentation for the hwml-rust implementation.

## Quick Start

**New to equality proofs and transport?** Start here:
1. Read [`SUMMARY-equality-and-transport.md`](SUMMARY-equality-and-transport.md) for an overview
2. Try the runnable example in [`equality-pattern-matching-example.md`](equality-pattern-matching-example.md)
3. Explore detailed examples in [`transport-example.md`](transport-example.md)

**Want to understand pattern matching compilation?** Read:
- [`design/pattern-matching.md`](../design/pattern-matching.md) - Comprehensive design document

## Documentation Files

### Core Concepts

#### [`SUMMARY-equality-and-transport.md`](SUMMARY-equality-and-transport.md)
**Comprehensive overview of equality proofs and transport in hwml-rust**

- Quick reference for syntax and key concepts
- Implementation status (what's done vs. in development)
- Guide to all documentation files
- Key files in the codebase
- How-to guide with practical examples
- Design principles and future work
- Testing guide

**Start here** if you want a complete picture of the system.

#### [`transport-example.md`](transport-example.md)
**Complete working examples of the transport primitive**

Contains 5 detailed examples:
1. **Simple Transport with Bit** - Basic usage with constant motive
2. **Dependent Pattern Matching on Vec** - The main use case showing full elaboration pipeline
3. **Actual Test Case** - Real code from `test_check_transport`
4. **Vec Exhaustiveness Checking** - How pattern matching determines exhaustiveness
5. **Pattern Matching on Equality Proofs** - Type refinement via matching `refl`

**Read this** to understand how transport works in practice.

#### [`equality-pattern-matching-example.md`](equality-pattern-matching-example.md)
**Concrete, runnable example of type refinement via equality proofs**

- The problem: Using equality proofs to refine types
- The solution: Pattern matching on `refl`
- **Runnable test code** you can execute today
- How pattern matching will work in the future surface syntax
- Step-by-step type checking explanation

**Run this** to see equality proofs in action:
```bash
cargo test -p hwml_core test_check_transport -- --nocapture
```

### Design Documents

#### [`design/pattern-matching.md`](../design/pattern-matching.md)
**Comprehensive guide to pattern matching compilation**

Topics covered:
- Motive-free case expressions
- Bidirectional type checking for pattern matching
- Pattern unification algorithm
- Axiom K and its role in dependent pattern matching
- Pattern matrix compilation
- The three primitives needed: `let`, `Eq`, and `transport`
- How the elaborator shields the core from complex indices

**Read this** for deep understanding of the pattern matching compilation strategy.

## Key Concepts

### Equality Type (`Eq`)

Propositional equality between two terms of the same type:
```
Eq A x y : Type
```

Where:
- `A` is the type of the elements
- `x` and `y` are the terms being equated

### Reflexivity (`refl`)

The proof that any term is equal to itself:
```
refl : Eq A x x
```

### Transport Primitive

Uses an equality proof to cast a value from one type to another:
```
transport VALUE to MOTIVE by PROOF
```

Where:
- `VALUE` has type `MOTIVE(a)`
- `MOTIVE` is a type family `λ %x → Type`
- `PROOF` is a proof `Eq A a b`
- Result has type `MOTIVE(b)`

**Key property**: When `PROOF` evaluates to `refl`, the transport vanishes (zero runtime cost).

### Axiom K

The principle that all proofs of `x = x` are equal. This enables:
- Simple pattern matching on equality proofs
- Straightforward pattern unification
- Efficient type checking

Trade-off: Not compatible with HoTT/Cubical Type Theory.

### Dependent Pattern Matching

Pattern matching where the return type depends on the scrutinee:
```
// Surface syntax (future)
match v : Vec A n {
  @VNil => ...       // Here n = 0
  @VCons x xs => ... // Here n = Succ m for some m
}
```

Compiled to core using `transport` to align types.

## Implementation Architecture

### Three-Layer Design

1. **Core Language** (`hwml-core`)
   - Simple, primitive constructs
   - `Eq`, `refl`, `transport`, `case`
   - Pattern unification with Axiom K
   - NbE evaluator

2. **Elaborator** (`hwml-elab`)
   - Transforms surface syntax to core
   - Motive synthesis
   - Automatic transport insertion
   - Pattern matrix compilation

3. **Surface Language** (`hwml-surface`)
   - User-friendly syntax
   - Pattern matching expressions
   - Type inference

### Data Flow

```
Surface Syntax
    ↓ (parse)
Surface AST
    ↓ (elaborate)
Core AST
    ↓ (type check)
Typed Core AST
    ↓ (evaluate)
Normal Form
```

## Testing

### Run All Tests
```bash
cargo test --workspace
```

### Run Core Tests
```bash
cargo test -p hwml_core
```

### Run Specific Tests
```bash
# Transport tests
cargo test -p hwml_core test_check_transport

# Equality tests
cargo test -p hwml_core test_check_eq

# Pattern unification tests
cargo test -p hwml_core pattern_unify

# Vec exhaustiveness tests
cargo test -p hwml_core test_vec_at
```

## Contributing

When adding new features related to equality proofs or pattern matching:

1. **Start with the core** - Implement primitives in `hwml-core` first
2. **Add tests** - Write comprehensive tests for the core functionality
3. **Update the elaborator** - Add elaboration rules in `hwml-elab`
4. **Document** - Update these docs with examples and explanations
5. **Test end-to-end** - Verify the full pipeline works

## Further Reading

### In This Repository

- `design/pattern-matching.md` - Pattern matching compilation strategy
- `crates/hwml-core/README.md` - Core language overview
- `crates/hwml-elab/README.md` - Elaborator overview

### Academic Papers

- **Dependently Typed Pattern Matching** (Coquand, 1992)
- **Eliminating Dependent Pattern Matching** (Goguen et al., 2006)
- **Pattern Matching Without K** (Cockx et al., 2014) - For contrast with our Axiom K approach

### Related Systems

- **Agda** - Dependent pattern matching with optional Axiom K
- **Idris** - Dependent types with pattern matching
- **Coq** - Proof assistant with dependent types (uses tactics instead of pattern matching)


