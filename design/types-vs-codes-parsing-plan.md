# Types vs Codes: Separate Parsing & Printing Implementation Plan

## Motivation

Currently, types and codes share syntax, which makes the core IR confusing:
- `U0` could be a type OR a code depending on context
- Pi types and pi codes look the same
- No visual distinction between type-level and term-level

**New Design**: Types and codes have DISTINCT syntax:
- **Types** use `CapitalCase` and fancy syntax: `Pi`, `Universe(0)`, `A => B`
- **Codes** use `lowercase` and explicit forms: `universe(0)`, `pi(...)`, `harrow(...)`

## Complete Inventory of Types and Codes

### 1. Universe System

| Level | Type (syn::Ty / val::Ty) | Code (Syntax / Value) | Example Syntax |
|-------|--------------------------|----------------------|----------------|
| **Meta** | `UniverseType` (syn::Ty) | N/A | `Universe` |
| **Meta** | `Universe(n)` (val::Ty only) | - | - |
| **Type** | `El(UniverseCode(n))` (syn::Ty) | - | `Type(U0)`, `Type(U1)` |
| **Code** | - | `UniverseCode(n)` | `U0`, `U1` or `universe(0)`, `universe(1)` |
| **Signal Meta** | `SignalUniverseType` | N/A | `SignalUniverse` |
| **Signal Code** | - | `signal_universe` | `signal_universe` |
| **Module Meta** | `ModuleUniverseType` | N/A | `ModuleUniverse` |
| **Module Code** | - | `module_universe` | `module_universe` |

### 2. Function Types

| Type (syn::Ty / val::Ty) | Code (Syntax / Value) | Current Syntax |
|---------------------------|----------------------|----------------|
| `Pi(A, icit, B)` | `pi(A, icit, B)` | `∀(%x : A) -> B` or `Pi ...` |
| `HArrow(A, B)` | `harrow(A, B)` | `A -> B` (in terms) |

### 3. El Decoders

| Type Form | Code Form | Current Syntax |
|-----------|-----------|----------------|
| `El(code)` | any type code | implicit or `El(...)` |
| `SignalEl(code)` | signal code | `SignalEl(...)` |
| `ModuleEl(code)` | module code | `ModuleEl(...)` |

### 4. Primitive Types

| Type (val::Ty) | Code (Syntax/Value) | Current Syntax |
|----------------|---------------------|----------------|
| `BitType` | `bit` | `Bit` |
| `LiftType(n, ty)` | `lift(n, code)` | (implicit) |

### 5. User-Defined Types

| Type (syn::Ty / val::Ty) | Code (Syntax/Value) | New Syntax |
|--------------------------|---------------------|------------|
| `TyConstructorTy(name, args)` (syn::Ty) | `#[@Name args...]` | `![@Name args...]` (type) vs `#[@Name args...]` (code) |
| `TyConstructor(name, args)` (val::Ty) | `TypeConstructor(name, args)` (Value) | - (semantic only) |
| - | `[@Name args...]` (dcon) | `[@Name args...]` (unchanged) |

### 6. Neutral Types

| Type (val::Ty) | Code (Value) | Current Syntax |
|----------------|--------------|----------------|
| `RigidTy(var, spine, ty)` | `rigid(var, spine)` | (internal) |
| `FlexTy(meta, spine, ty)` | `flex(meta, spine)` | `?[id args...]` |



## Proposed New Syntax

### Type-Level Syntax (CapitalCase, clean)

```
// Meta-level classifiers (types of type codes)
Universe                          // Type of universe codes (U0 : Universe)
SignalUniverse                    // Type of signal universe code
ModuleUniverse                    // Type of module universe code

// Decoded types from codes (using Type wrapper)
Type(U0), Type(U1)                // Decoded universe types (was El(U0))
Type(bit)                         // Decoded Bit type
(%x : A) -> B                     // Pi type (native or decoded from pi code)
A => B                            // HArrow type (native or decoded from harrow code)
Type(lift(2, code))               // Decoded lift type
![@Vec A n]                       // Type constructor TYPE (native syn::Ty form)

// El wrappers (explicit bridges from codes to types)
Type(code)                        // was El(code)
Signal(code)                      // was SignalEl(code)
Module(code)                      // was ModuleEl(code)
```

### Code-Level Syntax (lowercase, explicit)

```
// Type codes (terms that represent types)
U0, U1, U2, ...                   // Universe codes (fancy U)
universe(0), universe(1), ...     // Alternative universe code syntax
bit
pi(%x : a, b)                     // Pi code with explicit syntax (args are codes)
harrow(a, b)                      // HArrow code (args are codes)
lift(2, inner_code)

// Type constructor applications (these are CODES in syntax, but evaluate to values)
#[@Vec A n]                       // Type constructor CODE (term that evaluates to type)
[@Cons x xs]                      // Data constructor (regular term)

// Note: Type constructor TYPES use ! instead of #:
//   ![@Vec A n]                  // Type constructor TYPE (syn::Ty form)

// Hardware codes
signal_universe
module_universe

// Regular terms (already lowercase/symbolic)
lambda %x -> body
%x
@constant
$primitive
```


## New Token Design

### Add New Tokens for Types

```rust
// Type-level meta-classifiers (CapitalCase, no parens)
#[token("Universe", priority = 6)]
UniverseMetaType,   // Was UniverseType - classifies universe codes

#[token("SignalUniverse", priority = 6)]
SignalUniverseMetaType,   // Was SignalUniverseType

#[token("ModuleUniverse", priority = 6)]
ModuleUniverseMetaType,   // Was ModuleUniverseType

// Type wrapper tokens
#[token("Type", priority = 6)]
TypeWrapper,    // Was El - cleaner: Type(code)

#[token("Signal", priority = 6)]
SignalWrapper,  // Was SignalEl - cleaner: Signal(code)

#[token("Module", priority = 6)]
ModuleWrapper,  // Was ModuleEl - cleaner: Module(code)

// Note: Pi types use fancy syntax (%x : A) -> B, no special token needed
// Note: HArrow uses => which already exists
```

### Add New Tokens for Codes

```rust
// Code-level (lowercase)
#[token("universe", priority = 5)]
UniverseCodeToken,

#[token("pi", priority = 5)]
PiCodeToken,

#[token("bit", priority = 5)]
BitCodeToken,

#[token("lift", priority = 5)]
LiftCodeToken,

#[token("harrow", priority = 5)]
HArrowCodeToken,

#[token("signal_universe", priority = 5)]
SignalUniverseCodeToken,

#[token("module_universe", priority = 5)]
ModuleUniverseCodeToken,
```

### Deprecate/Repurpose Ambiguous Tokens

```rust
// Current tokens that are ambiguous:
Token::Bit              // REMOVE or rename - ambiguous between BitType and bit code
Token::HardwareUniverse // REMOVE - unclear what domain
Token::SignalUniverse   // REMOVE - ambiguous
Token::ModuleUniverse   // REMOVE - ambiguous
Token::Universe(n)      // KEEP for backward compat, but prefer universe(n) for codes
```


## Key Architectural Addition: Type Constructor Types in syn::Ty

### Current Limitation
Currently, `syn::Ty` lacks a native representation for type constructor applications. When parsing `tcon @Vec (%A : U0) : (#n : @Nat) -> U0`, the result type `U0` and parameter types are stored as codes wrapped in `El(...)`.

### New Design: TyConstructorTy Variant

Add `TyConstructorTy` to `syn::Ty`:

```rust
pub enum Ty<'db> {
    // ... existing variants ...

    /// Type constructor application at type level
    /// Printed as ![@Name arg1 arg2 ...]
    /// Distinguished from code form #[@Name arg1 arg2 ...]
    TyConstructorTy(Constant<'db>, Vec<RcTy<'db>>),
}
```

### Syntax Distinction

| Context | Syntax | Meaning |
|---------|--------|---------|
| **Type** | `![@Vec A n]` | Type constructor TYPE (syn::Ty::TyConstructorTy) |
| **Code** | `#[@Vec A n]` | Type constructor CODE (Syntax::TypeConstructor) |

### Why We Need This

1. **Telescopes need types**: Parameter lists store `RcTy`, not `RcSyntax`
2. **Avoid wrapping**: Instead of `El(#[@Vec A n])`, use native `![@Vec A n]`
3. **Type-level recursion**: Type arguments are `RcTy`, allowing nested type constructors
4. **Cleaner printing**: `![@Vec A n]` is clearer than `Type(#[@Vec A n])`

### Translation During Parsing

```rust
// When parsing type constructor result types:
parse("![@Vec A n]") -> syn::Ty::TyConstructorTy("Vec", [A, n])

// Code form remains:
parse("#[@Vec A n]") -> Syntax::TypeConstructor("Vec", [a_code, n_code])
```

### Evaluation and Decoding

```rust
// Evaluating syn::Ty::TyConstructorTy:
eval_ty(TyConstructorTy(name, args)) -> val::Ty::TyConstructor(name, eval_args)

// Decoding from type constructor code:
decode_type_code(TypeConstructor(name, args)) -> val::Ty::TyConstructor(name, decoded_args)

// Both paths produce the same semantic type!
```

## Implementation Strategy

### Phase 0: Add TyConstructorTy to syn::Ty (NEW)

**This must come BEFORE Phase 1** since the printer changes depend on having this variant.

1. **Add TyConstructorTy variant** to `syn::Ty` enum in `syn/ty.rs`
2. **Add constructor helpers** (`ty_constructor_ty`, `ty_constructor_ty_rc`)
3. **Update eval_ty** to handle `TyConstructorTy` -> `val::Ty::TyConstructor`
4. **Update check_ty** to type-check `TyConstructorTy` against `Universe`
5. **Update ty_to_term_code** to convert `TyConstructorTy` -> `Syntax::TypeConstructor`
   - This translation will be removed in Phase 2, but needed for backward compat
6. **Add parsing for `![@...]` syntax** to create `TyConstructorTy`
7. **Add printing for `TyConstructorTy`** as `![@Name args...]`

### Phase 1: Add New Tokens & Dual Parsing (Backward Compatible)

1. **Add new lowercase tokens** for codes without breaking existing syntax
   - Add `universe(n)`, `bit`, `pi(...)`, `harrow(...)`, etc.
   - Keep existing `U0`, `Bit`, etc. working

2. **Add new CapitalCase tokens** for decoded types
   - Add `Universe(n)`, `BitType`, `Pi(...)`, etc.
   - These are NEW, so no conflicts

3. **Update printers** to use new syntax
   - Print codes with lowercase: `universe(0)`, `bit`
   - Print types with CapitalCase: `Universe(0)`, `BitType`
   - Keep `El(...)` wrappers visible for clarity

### Phase 2: Update Parser Logic

4. **Separate `p_type` and `p_code` functions**
   ```rust
   fn p_type() -> syn::RcTy {
       match peek_token() {
           Token::UniverseType => ...,     // Meta-level
           Token::UniverseTypeToken => ..., // Universe(n) decoded type
           Token::PiType => ...,            // Pi(...) native type
           Token::El => { p_term(); wrap_in_el(...) },
           _ => error!("Expected type")
       }
   }

   fn p_code() -> RcSyntax {
       match peek_token() {
           Token::UniverseCodeToken => ..., // universe(n)
           Token::PiCodeToken => ...,       // pi(...)
           Token::BitCodeToken => ...,      // bit
           _ => p_term()  // fallback to regular term parsing
       }
   }
   ```

5. **Update `p_term` to NOT implicitly parse types**
   - Terms can reference codes, but not unwrapped types
   - `U0` should parse as `universe(0)` code, not as type

### Phase 3: Update Type Checking & Evaluation

6. **Update `check_ty` to expect syn::Ty forms**
   - Accept `Pi(...)`, `Universe(...)`, etc.
   - Accept `El(code)` where code is a term

7. **Update `decode_type_code` in eval.rs**
   - Map `universe(0)` → `Universe(0)` (val::Ty)
   - Map `bit` → `BitType` (val::Ty)
   - Map `pi(...)` → `Pi(...)` (val::Ty)

### Phase 4: Update Tests & Examples

8. **Migrate test syntax**
   - Update `.core` test files to use new syntax
   - Update inline test strings
   - Verify snapshots update correctly


## Detailed Syntax Specification

### Type Syntax (syn::Ty / val::Ty)

```ebnf
Type ::=
  // Meta-level classifiers (types of universes)
  | "Universe"                                   // Type of universe codes
  | "SignalUniverse"                             // Type of signal universe code
  | "ModuleUniverse"                             // Type of module universe code

  // Native types (Pi, HArrow)
  | "(" Variable ":" Type ")" "->" Type          // (%x : A) -> B (Pi type)
  | Type "=>" Type                               // A => B (HArrow)

  // Decoded types from codes (using Type wrapper)
  | "Type" "(" Code ")"                          // Type(universe(0)), Type(bit)
  | "Signal" "(" Code ")"                        // Signal(code)
  | "Module" "(" Code ")"                        // Module(code)

  // Type constructor types (native syn::Ty form)
  | "!" "[" "@" Constant Type ... "]"            // ![@Vec A n] (type constructor TYPE)
```

### Code Syntax (Syntax / Value)

```ebnf
Code ::=
  // Type codes
  | "U" Number                                   // U0, U1, U2, ... (fancy U - primary syntax)
  | "universe" "(" Number ")"                    // universe(0), universe(1), ... (alternative)
  | "bit"                                        // bit code
  | "pi" "(" Variable ":" Code "," Code ")"      // pi(%x : a, b) - pure code form
  | "harrow" "(" Code "," Code ")"               // harrow(a, b)
  | "lift" "(" Number "," Code ")"               // lift(2, inner)
  | "signal_universe"                            // Signal universe code
  | "module_universe"                            // Module universe code

  // Type constructor application (code form)
  | "#[" "@" Constant Term ... "]"               // #[@Vec A n]

  // Regular terms
  | "lambda" Variable "->" Code
  | Variable                                     // %x
  | Term
```

## Key Design Decisions

### 1. **Pi Type vs pi Code Distinction**

- **`(%x : A) -> B`** = TYPE (syn::Ty or val::Ty::Pi)
  - Used in type positions
  - Native type former
  - Clean syntax without keyword
  - Arguments are TYPES

- **`pi(%x : a, b)`** = CODE (Syntax::PiCode or Value::PiCode)
  - Used in term positions (pure code form)
  - First-class term that can be manipulated
  - Evaluates to PiCode value, which decodes to Pi type
  - Explicit keyword distinguishes from type-level Pi
  - Arguments are CODES (note: `a` and `b` are code variables, not types)

### 2. **HArrow Syntax Choice**

**Option A** (Recommended): Use `=>` for types, `harrow(...)` for codes
```
Type:  A => B
Code:  harrow(A, B)
```

**Option B**: Use different arrows
```
Type:  A ⇒ B      (double arrow)
Code:  A → B      (single arrow in code context)
```

**Decision**: Go with Option A - clearer distinction

### 3. **Universe Syntax - Three Levels**

**Meta-level (type of universe codes):**
```
Universe              // syn::Ty::UniverseType, val::Ty::UniverseType
                      // U0 : Universe
```

**Type-level (decoded universe type):**
```
Type(U0)              // syn::Ty::El(UniverseCode(0)) → val::Ty::Universe(0)
Type(U1)              // syn::Ty::El(UniverseCode(1)) → val::Ty::Universe(1)
```

**Code-level (universe codes - terms):**
```
U0, U1, U2, ...       // Syntax::UniverseCode(0), UniverseCode(1), ... (fancy U)
universe(0), ...      // Alternative lowercase syntax (new)
```

**Key Distinction:**
- `Universe` = meta-type (what U0's type is)
- `Type(U0)` = decoded type (a universe as a type)
- `U0` = code (a term that represents a universe)

### 4. **Backward Compatibility**

During migration:
- Accept both `U0` and `universe(0)` in parser
- Always print as `universe(0)`
- Eventually deprecate `U0`


## Example Transformations

### Before (Current Ambiguous Syntax)

```rust
// Ambiguous - is this a type or a code?
U0                    // Universe code? Or type?
Bit                   // Bit code? Or type?
@Vec A n              // Type constructor code? Or type?

// Type annotation - ambiguous
x : U0                // Does x have type "the universe" or type "some type in U0"?

// Pi type or Pi code? Unclear
∀(%x : U0) -> U0
```

### After (Clear Distinction)

```rust
// TYPES (CapitalCase, clean syntax)
Universe                  // Meta-level classifier: U0 : Universe
Type(U0)                  // Decoded universe type (type of types)
Type(bit)                 // Decoded Bit type
![@Vec A n]              // Type constructor TYPE (native syn::Ty form)
(%x : Type(U0)) -> Type(U0)   // Native Pi type

// CODES (lowercase/fancy, explicit)
U0, U1                    // Universe codes (fancy U)
bit                       // Bit code
#[@Vec A n]              // Type constructor code
pi(%x : U0, U0)          // Pi code (pure code form)

// Type annotations now explicit
x : Type(U0)              // x has type "Type(U0)" (a type in universe 0)
f : (%A : Universe) -> Type(A)   // f takes a universe code, returns a type

// In telescopes (using native type constructor types)
tcon @Vec (%A : Universe) : (%n : ![@Nat]) -> Universe
dcon @Cons (%x : A) : ![@List A]

// Pure code form (everything is a code)
tcon @Vec (%A : U0) : (%n : Type(#[@Nat])) -> U0
dcon @Cons (%x : %A) : Type(#[@List %A])
```

## Files Requiring Changes

### 1. Lexer/Parser (`syn/parse.rs`)
- Add new tokens
- Implement `p_type` to parse Type syntax
- Implement `p_code` to parse Code syntax
- Update `p_term` to delegate to `p_code` for type codes
- Update telescope parsing to expect types

### 2. Printer (`syn/print.rs`)
- Print `syn::Ty` using Type syntax
- Print `Syntax` codes using Code syntax
- Print `val::Ty` using Type syntax
- Print `Value` codes using Code syntax

### 3. Type Checker (`check.rs`)
- Update to work with explicit `syn::Ty` forms
- Handle both `El(code)` and native `Pi`, `Universe`, etc.

### 4. Evaluator (`eval.rs`)
- Update `decode_type_code` to handle lowercase codes
- Decode `universe(0)` → `Universe(0)` (val::Ty)
- Decode `pi(...)` → `Pi(...)` (val::Ty)
- Decode `bit` → `BitType` (val::Ty)

### 5. Quotation (`quote.rs`)
- Update `type_quote` to produce Type syntax
- Update `quote` to produce Code syntax for type codes

### 6. Tests
- Update all test strings
- Update snapshot expectations
- Verify type constructor declarations

## Open Questions

1. **Should we have sugar for common types?**
   - `Nat` as shorthand for `![@Nat]`?
   - `Vec<A, n>` as shorthand for `![@Vec A n]`?
   - Decision: Start without sugar, add later if needed

2. **What about implicit Type(...) wrapper?**
   - Should we still allow implicit `Type(...)` wrapping in type positions?
   - Or require explicit `Type(...)` everywhere?
   - Decision: Require explicit `Type(...)` - makes Tarski bridge visible

3. **Pi sugar for non-dependent functions?**
   - `A -> B` as sugar for `(%_ : A) -> B`?
   - Or require full Pi syntax?
   - Decision: Allow `A -> B` sugar for readability

4. **Type constructor in Type wrapper?**
   - Should `Type(#[@Vec A n])` decode to `TyConstructor` or error?
   - Decision: YES - for backward compatibility during migration
   - Eventually prefer native `![@Vec A n]` form