# Pattern Matching on Equality Proofs: Concrete Example

This document provides a **concrete, runnable example** of how pattern matching on equality proofs enables type refinement in hwml-rust.

## The Problem

Suppose you have:
- `n : Nat` (a natural number)
- `v : Vec Bool (n + n)` (a vector of booleans with length `n + n`)
- `p : Eq Nat (n + n) 0` (a proof that `n + n` equals `0`)

You want to write a function that returns `v` with type `Vec Bool 0`.

**Challenge**: The type of `v` is `Vec Bool (n + n)`, but you need to return `Vec Bool 0`. How do you use the proof `p` to cast the type?

## The Solution: Pattern Match on the Equality Proof

When you pattern match on `p` and match the `refl` constructor, the type checker learns that `(n + n) = 0`, allowing it to refine the type of `v`.

## Current Implementation Status

### ✅ What's Fully Implemented (hwml-core)

1. **Equality Type**: `Eq A x y` represents propositional equality
2. **Refl Constructor**: `refl : Eq A x x` proves reflexivity
3. **Transport Primitive**: `transport VALUE to MOTIVE by PROOF` uses equality proofs
4. **Pattern Unification with Axiom K**: Matching `refl` generates equality constraints
5. **Case Expressions**: Pattern matching on data constructors (including `refl`)

### 🚧 What's In Development (hwml-elab)

1. **Surface Syntax**: `match p { refl => ... }` for equality proofs
2. **Automatic Transport Generation**: Elaborator inserts transport nodes automatically
3. **Motive Synthesis**: Computing motives from expected types

## Runnable Example (hwml-core level)

You can test this concept today by manually constructing the core IR. Here's a complete test:

### Test Code

```rust
use hwml_core::*;

#[test]
fn test_equality_proof_type_refinement() {
    let db = Database::default();
    let global = GlobalEnv::new();
    let mut env = check::TypeCheckEnv::new(&db, &global);
    
    // Build context:
    // A : U0
    // B : U0  
    // p : Eq U0 A B
    // x : A
    
    let u0 = Rc::new(Value::universe(UniverseLevel::new(0)));
    
    // Push A : U0 (level 0)
    let a = env.push_var(u0.clone());
    
    // Push B : U0 (level 1)
    let b = env.push_var(u0.clone());
    
    // Push p : Eq U0 A B (level 2)
    let eq_ty = Rc::new(Value::eq(u0.clone(), a.clone(), b.clone()));
    env.push_var(eq_ty);
    
    // Push x : A (level 3)
    env.push_var(a.clone());
    
    // Construct: transport %0 to (λ %y → %y) by %1
    // %0 = x (index 0)
    // %1 = p (index 1)
    // Motive: λ %y → %y (identity function on types)
    //
    // This transports x : A to type B using proof p : Eq U0 A B
    
    let transport = syn::parse::parse_syntax_at_depth(
        &db,
        "transport %0 to λ %y → %y by %1",
        4  // depth = 4 (we have 4 variables in scope)
    ).expect("should parse");
    
    // Type check: should synthesize type B
    let result = check::type_synth(&mut env, &transport);
    assert!(result.is_ok(), "Type checking failed: {:?}", result.err());
    
    // Verify the synthesized type is B
    let synth_ty = result.unwrap();
    // B is at level 1, which is index 2 from depth 4
    // After evaluation, it should be a variable
    match synth_ty.as_ref() {
        Value::Variable(var) => {
            assert_eq!(var.level, Level::new(1), "Expected type B (level 1)");
        }
        other => panic!("Expected variable B, got {:?}", other),
    }
}
```

### What This Demonstrates

1. **Context Setup**: We build a typing context with types `A`, `B`, a proof `p : Eq U0 A B`, and a value `x : A`

2. **Transport Expression**: We construct `transport x to (λ y → y) by p`
   - **VALUE**: `x` (has type `A`)
   - **MOTIVE**: `λ y → y` (identity function - when applied to `A` gives `A`, when applied to `B` gives `B`)
   - **PROOF**: `p` (proves `A = B`)

3. **Type Synthesis**: The type checker:
   - Checks that `p : Eq U0 A B`
   - Extracts endpoints: `a = A`, `b = B`
   - Checks that `x : (λ y → y) A = A` ✓
   - Synthesizes result type: `(λ y → y) B = B` ✓

4. **Result**: We successfully cast `x` from type `A` to type `B` using the equality proof!

## How Pattern Matching Would Work (Future)

Once the elaborator is complete, you'll be able to write:

```rust
// Surface syntax (future)
foo : (A : Type) -> (B : Type) -> (p : Eq Type A B) -> (x : A) -> B
foo = λ A B p x =>
  match p {
    refl => x  // After matching refl, x : A refines to x : B
  }
```

The elaborator would compile this to:

```rust
// Core IR (what the elaborator generates)
λ %A %B %p %x =>
  let scrut = %p;
  scrut case {
    @refl => %x
  }
```

**Type checking the case branch**:
1. Scrutinee `scrut : Eq Type A B`
2. Pattern `@refl` expects `Eq Type X X` for some `X`
3. Pattern unification: `A ~ B` (generates substitution)
4. In the branch body, `A` and `B` are known to be equal
5. So `x : A` is also `x : B` ✓

## Running the Example

To run this test:

```bash
cd crates/hwml-core
cargo test test_check_transport -- --nocapture
```

This test is already in the codebase at `crates/hwml-core/src/check.rs::test_check_transport`.

## Key Takeaways

1. **Equality proofs enable type refinement**: Matching on `refl` tells the type checker that two types are equal

2. **Transport is the mechanism**: The `transport` primitive uses equality proofs to cast values between types

3. **Axiom K makes it simple**: The pattern unifier treats all proofs of `x = x` as equal, making pattern matching straightforward

4. **Zero runtime cost**: When the proof is `refl`, the evaluator deletes the transport, leaving just the original value

5. **Infrastructure is ready**: The core language fully supports this - it's just a matter of exposing it in the surface syntax!


