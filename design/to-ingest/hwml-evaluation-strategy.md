# HWML Evaluation Strategy

## Overview

This document describes the evaluation strategy for HWML, a Two-Level Type Theory (2LTT) for hardware generation. Our system has two distinct levels:

1. **Meta-level**: Full dependent type theory with closures, beta-reduction, and normalization
2. **HardwareUniverse-level (Object-level)**: Uninterpreted syntax trees representing circuit descriptions

## Implementation Status

### ✅ Completed

#### Step 1: val.rs - HardwareUniverse Values
- Added hardware values to semantic domain
  - `Type` - The universe of hardware types
  - `HArrow` - HardwareUniverse arrow type values
  - `Value::Type`, `Value::Bit`, `Value::HArrow`, `Value::Lift`, `Value::Quote`
  - Helper constructors: `HardwareUniverse()`, `bit()`, `harrow()`, `lift()`, `quote()`

#### Step 2: syn/basic.rs - HardwareUniverse Syntax (Already Existed!)
- HardwareUniverse syntax already defined in codebase
  - `Syntax` enum - HardwareUniverse term syntax (equivalent to our planned `HWTerm`)
  - `Lift`, `Quote`, `HArrow`, `Bit` - Staging constructs
  - HardwareUniverse primitives: `Zero`, `One`, `Xor`, `And`, `Or`, `Not`, `Splice`
  - `HCheck`, `Module`, `HApplication` - HardwareUniverse term constructs

#### Step 3: eval.rs - HardwareUniverse Evaluation
- Implemented evaluation for all hardware constructs
  - `eval_bit()` - Evaluates Bit type to `Value::Bit`
  - `eval_harrow()` - Evaluates hardware arrow types
  - `eval_lift()` - Evaluates lifted hardware types
  - `eval_quote()` - Evaluates quoted hardware terms
  - `eval_hsyntax()` - **KEY FUNCTION**: Reconstructs hardware syntax without reduction
  - `eval_hsyntax_splice_app()` - Handles splice application (the bridge!)
- Added `Error::BadSplice` for splice errors

#### Step 4: quote.rs - HardwareUniverse Quotation
- Implemented quotation for all hardware constructs
  - `quote_hwtype()` - Quotes hardware types (Bit, HArrow) back to syntax
  - `quote_lift_instance()` - Quotes instances of lifted types (^ht)
  - Updated `quote()` to handle `Type` and `Lift` types
  - Updated `quote_type()` to handle `Lift` as a valid meta-level type
- HardwareUniverse terms (Syntax) are quoted directly without reduction

#### Step 5: equal.rs - HardwareUniverse Equality
- Implemented equality checking for hardware types
  - `Type::is_convertible()` - All Type instances are equal
  - `HArrow::is_convertible()` - Structural equality for hardware arrows
  - `is_hwtype_convertible()` - Equality for hardware types (Bit, HArrow, neutrals)
  - `is_lift_instance_convertible()` - Equality for quoted hardware terms
- Updated `Normal::is_convertible()` to handle Type and Lift types
- Updated `is_type_convertible()` to handle Lift as a meta-level type
- HardwareUniverse terms use **structural equality** (Syntax derives Eq)

#### Step 6: check.rs - HardwareUniverse Type Checking
- Implemented type checking for hardware constructs
  - `type_synth_lift()` - Synthesize type for ^ht (returns Type)
  - `type_check_bit()` - Check Bit : Type
  - `type_check_harrow()` - Check (a -> b) : Type
  - `type_check_quote()` - Check 'circuit : ^ht
  - `check_hwtype()` - Validate hardware types (Bit, HArrow, neutrals)
  - `check_hsyntax()` - Placeholder for hardware term checking (TODO)
- Updated `type_synth()` to handle Lift
- Updated `type_check()` to handle Bit, HArrow, Quote
- Updated `check_type()` to recognize Lift as a valid type

### ✅ Implementation Complete!

All core infrastructure for hardware types in HWML has been successfully implemented:
1. ✅ Semantic values (val.rs)
2. ✅ Syntax (syn/basic.rs - already existed)
3. ✅ Evaluation (eval.rs)
4. ✅ Quotation (quote.rs)
5. ✅ Equality (equal.rs)
6. ✅ Type checking (check.rs)

The codebase compiles successfully with only warnings (no errors)!

### 🔄 Future Work
- Implement full hardware term type checking in `check_hsyntax()`
- Add hardware-specific optimizations
- Extend with more hardware primitives

## Core Principle

**HardwareUniverse terms are SYNTAX TREES, not semantic values. They are reconstructed during evaluation, not reduced.**

## Type System Architecture

### Universes

```
Type : Type₁                    (Meta-universe)
Type : Type               (HardwareUniverse type universe, lives in meta-level)
```

### HardwareUniverse Types (Meta-level terms)

HardwareUniverse types are **meta-level terms** of type `Type`:

```
Bit : Type                (The bit type)
(a -> b) : Type           (HardwareUniverse arrow, where a, b : Type)
```

### Lifted Types (Meta-level types)

The `Lift` operator bridges hardware types to meta-level types:

```
^ht : Type                      (where ht : Type)
```

`^ht` is the type of quoted hardware terms of type `ht`.

### Staging Constructs

```
Quote:  'circuit : ^ht          (Brings hardware term to meta-level)
Splice: ~tm : HWTerm ht         (Brings meta term to hardware-level, where tm : ^ht)
```

## Evaluation Strategy

### Meta-Level Evaluation (Standard NbE)

Meta-level terms evaluate to semantic values with closures:

```rust
eval(λx. body) → Value::Lambda(Closure { env, body })
eval((λx. body) arg) → eval(body[x := arg])  // Beta-reduction
```

**Key characteristics:**
- Functions become closures
- Beta-reduction happens
- Eta-expansion for conversion checking
- Full normalization

### HardwareUniverse-Level Evaluation (Syntax Reconstruction)

HardwareUniverse terms evaluate by **reconstructing syntax**, NOT reducing:

```rust
eval_hwterm(λx. body) → HWTerm::HLam(eval_hwterm(body))  // Reconstruct, no closure!
eval_hwterm(f arg) → HWTerm::HApp(eval_hwterm(f), eval_hwterm(arg))  // No beta-reduction!
```

**Key characteristics:**
- Lambdas remain as syntax (NOT closures)
- Applications remain as syntax (NO beta-reduction)
- Primitives remain as syntax
- Variables remain as syntax (neutrals)
- Only Splice performs reduction (by evaluating meta terms)

### Evaluation Rules

#### Meta-Level Constructs

```
eval(Bit) → Value::Bit
eval(a -> b) → Value::HArrow(eval(a), eval(b))
eval(^ht) → Value::Lift(eval(ht))
eval('circuit) → Value::Quote(eval_hwterm(circuit))
```

#### HardwareUniverse-Level Constructs

```
eval_hwterm(0) → HWTerm::Zero
eval_hwterm(1) → HWTerm::One
eval_hwterm(and) → HWTerm::And
eval_hwterm(x) → HWTerm::HVariable(x)                    // Variable (neutral)
eval_hwterm(λx. body) → HWTerm::HLam(eval_hwterm(body))  // Reconstruct!
eval_hwterm(f arg) → HWTerm::HApp(eval_hwterm(f), eval_hwterm(arg))  // Reconstruct!
```

#### Splice (The Bridge)

Splice is the **only** place where meta-level evaluation affects hardware-level:

```
eval_hwterm(~tm) → 
  let meta_val = eval(tm) in
  match meta_val with
  | Value::Quote(hw_term) → hw_term
  | _ → error
```

**Example:**
```
meta_circuit : ^Bit = '(and 0 1)
eval_hwterm(~meta_circuit) → HWTerm::HApp(HWTerm::HApp(HWTerm::And, HWTerm::Zero), HWTerm::One)
```

## Conversion Checking Strategy

Based on `object-language-conversion.md`, we use different strategies for each level:

### Meta-Level Conversion (Smart)

- Beta-reduction aware
- Eta-expansion for functions
- Full normalization
- Compares semantic values

```rust
conv(Value::Lambda(f1), Value::Lambda(f2)) → 
  let x = fresh_var() in
  conv(f1.apply(x), f2.apply(x))  // Eta-expansion
```

### HardwareUniverse-Level Conversion (Structural)

- Structural equality only
- No beta-reduction
- No eta-expansion
- Compares syntax trees

```rust
conv(HWTerm::And, HWTerm::And) → true
conv(HWTerm::HApp(f1, a1), HWTerm::HApp(f2, a2)) → 
  conv(f1, f2) && conv(a1, a2)
conv(HWTerm::HVariable(i), HWTerm::HVariable(j)) → i == j
```

### Stuck Splices (The Bridge)

When hardware terms contain stuck meta-variables (neutrals), we need to handle splices:

```rust
conv(HWTerm::Splice(tm1), HWTerm::Splice(tm2)) → 
  // Evaluate meta terms and compare
  let v1 = eval(tm1)
  let v2 = eval(tm2)
  conv(v1, v2)  // Use meta-level conversion!
```

## Type Checking Strategy

### HardwareUniverse Type Checking

HardwareUniverse terms are type-checked against hardware types:

```
Γ ⊢ 0 : HWTerm Bit
Γ ⊢ 1 : HWTerm Bit
Γ ⊢ and : HWTerm (Bit -> Bit -> Bit)
```

### Staging Type Rules

```
Γ ⊢ ht : Type
─────────────────────
Γ ⊢ ^ht : Type

Γ ⊢ circuit : HWTerm ht    Γ ⊢ ht : Type
───────────────────────────────────────────────
Γ ⊢ 'circuit : ^ht

Γ ⊢ tm : ^ht    Γ ⊢ ht : Type
────────────────────────────────────
Γ ⊢ ~tm : HWTerm ht
```

## Summary Table

| Aspect | Meta-Level | HardwareUniverse-Level |
|--------|-----------|----------------|
| **Representation** | Closures / Semantic Values | Syntax Trees (ASTs) |
| **Variable Binding** | Closures or HOAS | De Bruijn indices |
| **Evaluation** | Reduces to Normal Form | Reconstructs Syntax Tree |
| **Application** | Beta-reduction | Creates App AST node |
| **Conversion** | Beta-eta equality | Structural equality |
| **Purpose** | Generate hardware | Describe hardware |

## Key Design Decisions

1. **No Value enum**: HardwareUniverse terms stay as `HWTerm` (syntax), not semantic values
2. **Reconstruction not reduction**: `eval_hwterm` rebuilds syntax trees
3. **Splice is the bridge**: Only place where meta affects hardware
4. **Separate conversion**: Different equality for meta vs hardware
5. **Intrinsic typing**: HardwareUniverse terms are well-typed by construction (future goal)

## References

- `Staged-nbe.md` - Staged NbE approach
- Other design documents in this directory

