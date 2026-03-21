# Transport Primitive: Complete Working Example

This document demonstrates how dependent pattern matching is compiled down to use the `transport` primitive in hwml-rust.

## Overview

The `transport` primitive is the core mechanism for using equality proofs to cast values between types. It implements **Axiom J** (also called the J eliminator or path induction) from type theory.

**New Syntax**: `transport VALUE to MOTIVE by PROOF`

Where:
- **VALUE**: The value to transport (has type `MOTIVE(a)`)
- **MOTIVE**: A lambda describing the type family (e.g., `λ %i → Vec Unit %i`)
- **PROOF**: An equality proof showing `a = b` (usually `refl`)

The entire expression has type `MOTIVE(b)`.

## Example 1: Simple Transport with Nat Equality

### Surface-Level Concept

Suppose we have:
- A proof `h : Eq Nat 0 0` (which is just `refl`)
- A value `x : Bit` 
- A type family `P = λ %n → Bit` (constant family - doesn't actually depend on the Nat)

We can transport `x` along the proof `h`:

### Core IR Syntax

```
transport 0 to λ %x → Bit by refl
```

### Explanation

- **VALUE**: `0` (a bit value)
- **MOTIVE**: `λ %x → Bit` (the type family - in this case constant)
- **PROOF**: `refl` (proof that `0 = 0`)

**Type checking**:
1. Check that `refl` has type `Eq Nat 0 0` ✓
2. Check that `0` has type `(λ %x → Bit) 0` = `Bit` ✓
3. Synthesize result type: `(λ %x → Bit) 0` = `Bit` ✓

**Evaluation**: Since the proof is `refl`, the transport **vanishes** and just returns `0`.

This is tested in `crates/hwml-core/src/check.rs::test_check_transport`.

## Example 2: Dependent Pattern Matching on Vec (The Real Use Case)

This is where `transport` becomes essential for dependent types.

### Surface Syntax (Hypothetical)

```rust
// User writes:
fn head<A>(n : Nat, v : Vec A (succ n)) -> A {
    match v {
        vcons(x, xs) => x
    }
}
```

### The Problem

The type `Vec A (succ n)` has a **complex index** `(succ n)`. The core pattern matcher can only match on **variables**, not applications like `succ n`.

### The Elaboration Strategy

The elaborator transforms this into core IR using the following steps:

**Step 1: Bind the scrutinee to a variable**
```
let scrut = v;
```

**Step 2: Bind the index to a variable**  
```
let y = succ n;
```

**Step 3: Generate an equality proof**
```
let h : Eq Nat (succ n) y = refl;
```

**Step 4: Transport the vector**
```
let v_cast = transport v to (λ %i → Vec A %i) by h;
```

Now `v_cast` has type `Vec A y` where `y` is a **variable**, not an application!

**Step 5: Pattern match on the variable**
```
y case {
    @VNil => ...        // Impossible! y = succ n, can't be Zero
    @VCons %n' %x %xs => x
}
```

### Core IR Output (Simplified)

```
let scrut = v;
let y = succ n;
let h : Eq Nat (succ n) y = refl;
let v_cast = transport scrut to λ %i → Vec A %i by h;
y case {
    @VCons %n' %x %xs => x
}
```

### Detailed Explanation

1. **The Motive**: `λ %i → Vec A %i`
   - This is a type family that takes a Nat index and returns the type `Vec A` at that index
   - When applied to `succ n`, it gives `Vec A (succ n)` (the original type of `v`)
   - When applied to `y`, it gives `Vec A y` (the transported type)

2. **The Proof**: `h : Eq Nat (succ n) y = refl`
   - This proves that `succ n` and `y` are equal
   - Since `y` is defined as `succ n`, this is definitionally `refl`

3. **The Value**: `scrut` (which is `v`)
   - Has type `Vec A (succ n)` originally
   - After transport, has type `Vec A y`

4. **Why This Works**:
   - The pattern unifier can now match `y` (a variable) against `@VCons`
   - It generates the substitution `[y ↦ succ n']` where `n'` is the predecessor
   - The type refines correctly: `Vec A y` becomes `Vec A (succ n')`

5. **Runtime Performance**:
   - The proof `h` evaluates to `refl`
   - When the evaluator sees `transport ... by refl`, it **deletes the transport**
   - The result is just the original value `v` - zero runtime cost!

## Example 3: Actual Test Case from hwml-core

Here's a real working example from the test suite that demonstrates transport in action.

### Test Setup (from `crates/hwml-core/src/check.rs`)

```rust
// Context: [A : U0, B : U0, h : Eq U0 A B, x : A]
// Term: transport %0 to λ %y → %y by %1
// Expected type: B
```

### Breaking Down the Context

The test builds this environment:
1. `A : U0` - A is a type (universe level 0)
2. `B : U0` - B is a type
3. `h : Eq U0 A B` - h is a proof that A and B are equal types
4. `x : A` - x is a value of type A

Variables in de Bruijn indices (from most recent to oldest):
- `%0` = `x` (the value)
- `%1` = `h` (the proof)
- `%2` = `B` (the target type)
- `%3` = `A` (the source type)

### The Transport Expression

```
transport %0 to λ %y → %y by %1
```

**Parsing this**:
- **VALUE**: `%0` (which is `x : A`)
- **MOTIVE**: `λ %y → %y` (the identity function on types)
- **PROOF**: `%1` (which is `h : Eq U0 A B`)

### Type Checking Steps

1. **Check the proof**: `%1` has type `Eq U0 A B` ✓
   - This tells us the proof connects `A` and `B`

2. **Evaluate the proof to WHNF** to extract endpoints:
   - Type is `Eq U0 A B`
   - So `a = A` and `b = B`

3. **Check the motive**: `λ %y → %y` should have type `U0 → U0` ✓
   - It's a function from types to types

4. **Apply motive to `a`**: `(λ %y → %y) A = A`
   - This is the expected type of the value

5. **Check the value**: `%0` (which is `x`) has type `A` ✓

6. **Apply motive to `b`**: `(λ %y → %y) B = B`
   - This is the synthesized result type ✓

**Result**: The transport expression has type `B`, successfully transporting a value of type `A` to type `B` using the equality proof!

### Why the Identity Motive?

The motive `λ %y → %y` is the identity function. This means:
- When applied to `A`, it returns `A`
- When applied to `B`, it returns `B`

This is the simplest possible transport: "cast a value from type A to type B using a proof that A = B".

More complex motives (like `λ %i → Vec Unit %i`) allow transporting values through **type families** that depend on indices.

## Example 4: Vec Pattern Matching Test

From `crates/hwml-core/src/check.rs::test_vec_at_zero_only_requires_vnil`:

### Context

```
a : Type
v : Vec a @Zero
```

### Pattern Match

```
v case { @VNil => [@Zero] }
```

### Why This is Exhaustive

The type `Vec a @Zero` can **only** be constructed with `@VNil`:
- `@VNil : Vec a @Zero` ✓
- `@VCons : Vec a (@Succ n)` ✗ (requires non-zero index)

The pattern unifier sees:
- Scrutinee type: `Vec a @Zero`
- Pattern: `@VNil` expects `Vec a @Zero`
- Unification: `@Zero ~ @Zero` ✓

Since `@VCons` requires `@Succ n` as the index, it's **impossible** when the index is `@Zero`. The checker correctly determines this match is exhaustive with only the `@VNil` branch.

### Contrast: Variable Index

From `test_vec_at_variable_requires_both_constructors`:

```
a : Type
n : Nat
v : Vec a n
```

Pattern match:
```
v case { @VNil => [@Zero] }  // Missing @VCons!
```

This is **non-exhaustive** because `n` is a variable - it could be either:
- `@Zero` (making `@VNil` possible)
- `@Succ m` (making `@VCons` possible)

The checker correctly reports: `NonExhaustiveMatch { missing: ["VCons"] }`

## Summary: The Transport Workflow

1. **Elaborator** generates:
   - Let-bindings for complex scrutinees
   - Equality proofs (usually `refl`)
   - Transport expressions to align types

2. **Type Checker** verifies:
   - Proof has the right equality type
   - Value has the source type
   - Result has the target type

3. **Evaluator** optimizes:
   - `transport ... by refl` → just return the value
   - `transport ... by neutral` → stuck (becomes a neutral value)

4. **Pattern Matcher** benefits:
   - Only matches on variables (simple!)
   - Types are aligned via transport
   - Dependent types work correctly

This separation of concerns makes the core language simple while supporting powerful dependent pattern matching at the surface level.

## Example 5: Pattern Matching on Equality Proofs (Type Refinement)

This is the most powerful use of equality proofs: **matching on an equality proof refines types**.

### The Concept

When you pattern match on a proof `p : Eq A x y` and match the `refl` constructor, you learn that `x` and `y` are **definitionally equal**. This allows the type checker to refine types that depend on `x` to use `y` instead (or vice versa).

### Surface Syntax Example (Hypothetical)

```rust
// Function that uses an equality proof to refine a type
foo : (n : Nat) -> (v : Vec Bool (n + n)) -> (p : Eq Nat (n + n) 0) -> Vec Bool 0
foo = λ n v p =>
  match p {
    refl => v  // After matching refl, we know (n + n) = 0, so v : Vec Bool 0
  }
```

**What's happening**:
1. We have `v : Vec Bool (n + n)` (vector with length `n + n`)
2. We have `p : Eq Nat (n + n) 0` (proof that `n + n` equals `0`)
3. When we match `p` against `refl`, the pattern unifier learns `(n + n) ~ 0`
4. The type of `v` is refined from `Vec Bool (n + n)` to `Vec Bool 0`
5. We can return `v` directly as it now has the correct type!

### Current State in hwml-rust

**Status**: The infrastructure is in place, but full surface-level pattern matching on equality is still being developed.

**What's Implemented**:
- ✅ Core `Eq` type and `refl` constructor
- ✅ `transport` primitive for using equality proofs
- ✅ Pattern unification with Axiom K (see `crates/hwml-core/src/pattern_unify.rs`)
- ✅ Case expressions on data constructors
- ✅ Elaborator infrastructure for match expressions (`crates/hwml-elab/src/elaborator.rs`)

**What's Being Developed**:
- 🚧 Full pattern matching on `Eq` type in the elaborator
- 🚧 Automatic generation of transport nodes when matching on equality proofs
- 🚧 Surface syntax for dependent pattern matching

### How It Works in the Core (Manual Construction)

You can manually construct the core IR to demonstrate the concept. Here's what the elaborator would generate:

#### Core IR (Conceptual)

```
λ %n %v %p =>
  let scrut = %p;
  let y = (n + n);
  let h : Eq Nat (n + n) y = refl;
  let v_cast = transport %v to (λ %i → Vec Bool %i) by %h;
  scrut case {
    @refl => v_cast
  }
```

**Step-by-step**:
1. **Bind the scrutinee**: `scrut = p`
2. **Bind the complex index**: `y = (n + n)` (make it a variable)
3. **Generate proof**: `h : Eq Nat (n + n) y = refl`
4. **Transport the vector**: Cast `v` from `Vec Bool (n + n)` to `Vec Bool y`
5. **Match on refl**: When we match `scrut` against `@refl`, the pattern unifier sees:
   - `scrut : Eq Nat (n + n) 0`
   - Pattern `@refl` expects `Eq Nat x x` for some `x`
   - Unification: `(n + n) ~ 0` and `0 ~ 0`
   - Solution: `[(n + n) ↦ 0]`
6. **Type refinement**: The type of `v_cast` refines from `Vec Bool y` to `Vec Bool 0`

### Working Example: Simpler Case

Let's show a simpler example that you can actually test in hwml-core today:

#### Core Syntax Test

```rust
// Context: [A : U0, B : U0, p : Eq U0 A B, x : A]
// Goal: Extract x as type B by matching on the equality proof

// Manual construction (what the elaborator would generate):
p case {
  @refl => x  // After matching refl, x : A refines to x : B
}
```

**Type checking**:
1. `p : Eq U0 A B` (proof that types A and B are equal)
2. Pattern `@refl` expects `Eq U0 X X` for some `X`
3. Unification: `A ~ B` (Axiom K: all proofs of equality are equal)
4. After matching, in the branch body, we know `A = B` definitionally
5. So `x : A` is also `x : B`

### The Key Insight: Axiom K

The pattern unifier implements **Axiom K** (Uniqueness of Identity Proofs):

<augment_code_snippet path="crates/hwml-core/src/pattern_unify.rs" mode="EXCERPT">
````rust
// Rule: Axiom K - all Refl proofs are equal at EqType
(Value::Refl(_), Value::Refl(_), Value::EqType(_)) => {
    // refl ~ refl  is always true (Axiom K)
    // Delete this equation
}
````
</augment_code_snippet>

This means:
- When matching `refl` against a proof of `Eq A x y`, the unifier generates `x ~ y`
- This equation is solved, binding variables or checking definitional equality
- The type refinement happens automatically through the substitution

### Testing Pattern Matching on Equality

You can test this in `hwml-core` by constructing case expressions manually:

```rust
// From crates/hwml-core/src/check.rs::test_check_transport
let db = Database::default();
let global = GlobalEnv::new();
let mut env = make_env(&db, &global);

// Build context: [A : U0, B : U0, h : Eq U0 A B, x : A]
let u0 = Rc::new(Value::universe(UniverseLevel::new(0)));
let a = env.push_var(u0.clone());
let b = env.push_var(u0.clone());
let eq_ty = Rc::new(Value::eq(u0.clone(), a.clone(), b.clone()));
env.push_var(eq_ty);
env.push_var(a.clone());

// Use transport to cast x : A to type B using proof h
let transport = parse_syntax_at_depth(
    &db,
    "transport %0 to λ %y → %y by %1",
    4
).expect("should parse");

// Type check: should synthesize type B
let result = type_synth(&mut env, &transport);
assert!(result.is_ok());
```

### Next Steps for Full Implementation

To fully support pattern matching on equality proofs in the surface language:

1. **Elaborator Enhancement**: Detect when matching on `Eq` type
2. **Transport Generation**: Automatically insert `transport` nodes for dependent variables
3. **Motive Synthesis**: Compute the motive from the expected type
4. **Surface Syntax**: Support `match p { refl => ... }` syntax

The core infrastructure is ready - it's just a matter of connecting the pieces in the elaborator!


