# Implementation Plan: syn::Ty - Syntax-Level Types Following Tarski Universes

## Executive Summary

This plan adds `syn::Ty` to the hwml-core crate, creating a syntax-level type representation that mirrors the semantic `val::Ty`. This follows the Tarski universe pattern where:

1. **syn::Ty** - Syntax-level types (unevaluated, in source code)
2. **val::Ty** - Semantic types (evaluated, what the typechecker operates on)  
3. **val::Value** - Type codes (terms that represent types)

The key insight: Just as `val::Ty::El(Value)` decodes type codes into semantic types, we need syntax-level types to express types before evaluation.

## Current Architecture Analysis

### Three-Layer Type System

The codebase currently implements a sophisticated type system with three distinct representations:

#### Layer 1: Syntax (syn::Syntax)
- **Location**: `crates/hwml-core/src/syn/syntax.rs`
- **Purpose**: Unevaluated terms and type codes from source
- **Key types**:
  - `Syntax::UniverseCode(usize)` - Type universe at level n
  - `Syntax::PiCode(source, icit, target)` - Dependent function type code
  - `Syntax::LiftCode(shift, inner)` - Universe lifting
  - `Syntax::BitCode` - Hardware Bit type code
  - `Syntax::Check(Check)` - Type annotation (currently holds `RcSyntax`)

#### Layer 2: Semantic Values (val::Value)
- **Location**: `crates/hwml-core/src/val/value.rs`
- **Purpose**: Evaluated type codes (values that represent types)
- **Key types**:
  - `Value::UniverseCode(usize)` - Evaluated universe
  - `Value::PiCode(dom, icit, cod)` - Evaluated dependent function type
  - `Value::LiftCode(shift, inner)` - Evaluated universe lifting
  - `Value::BitCode` - Evaluated Bit type

#### Layer 3: Semantic Types (val::Ty)
- **Location**: `crates/hwml-core/src/val/ty.rs`
- **Purpose**: What the typechecker/unifier operates on
- **Key types**:
  - `Ty::UniverseType` - The type of universe codes
  - `Ty::Pi(source, target)` - Dependent function type (no universe levels)
  - `Ty::El(code)` - Decode a type code (Value) into a type
  - `Ty::SignalUniverseType`, `Ty::ModuleUniverseType` - Hardware universe types
  - `Ty::SignalEl(code)`, `Ty::ModuleEl(code)` - Hardware type decoders

### Current Check Node Structure

```rust
// Currently in syn/syntax.rs:724-734
pub struct Check<'db> {
    pub ty: RcSyntax<'db>,    // ← Problem: should be RcTy<'db>
    pub term: RcSyntax<'db>,
}
```

The `Check` node currently holds a `RcSyntax` for the type, but semantically this should be a `syn::Ty` - a syntax-level type expression.

## Design: syn::Ty

### Core Structure

Following the pattern of `val::Ty`, we need `syn::Ty` to represent unevaluated types:

```rust
// In crates/hwml-core/src/syn/ty.rs (NEW FILE)

pub type RcTy<'db> = Rc<Ty<'db>>;
pub type BindingTy<'db> = Binding<'db, RcTy<'db>>;

/// Syntax-level types (unevaluated type expressions)
/// 
/// This mirrors val::Ty but at the syntax level. Like val::Ty, this
/// follows the Tarski universe pattern with El decoders.
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub enum Ty<'db> {
    // ========== Universe Types (The Classifiers) ==========
    /// The type of Type 0, Type 1, Type 2, ...
    UniverseType,
    
    /// The type of Signal (hardware signal universe)
    SignalUniverseType,
    
    /// The type of Module (hardware module universe)
    ModuleUniverseType,
    
    // ========== Top-Level Type Formers ==========
    /// Dependent function type: (x : A) -> B
    /// Domain is a type, codomain is a binding over a type
    Pi(RcTy<'db>, BindingTy<'db>),
    
    /// Hardware arrow type: Signal => Module
    /// Non-dependent arrow at hardware level
    HArrow(RcTy<'db>, RcTy<'db>),
    
    // ========== The Tarski Bridge ==========
    /// El(code): Decode a type code (term) into a type
    /// 
    /// This is the key to the Tarski universe approach.
    /// Examples:
    /// - El(UniverseCode(0)) is the type of small types
    /// - El(PiCode(A, B)) is a dependent function type
    /// - El(TypeConstructor(Nat, [])) is the Nat type
    El(RcSyntax<'db>),
    
    /// SignalEl(code): Decode a signal type code
    SignalEl(RcSyntax<'db>),
    
    /// ModuleEl(code): Decode a module type code
    ModuleEl(RcSyntax<'db>),
}
```

### Parallel with val::Ty

| Concept | syn::Ty | val::Ty |
|---------|---------|---------|
| Universe classifier | `Ty::UniverseType` | `Ty::UniverseType` |
| Pi type | `Ty::Pi(dom, cod_binding)` | `Ty::Pi(dom, cod_closure)` |
| Type decoder | `Ty::El(RcSyntax)` | `Ty::El(RcValue)` |
| Hardware arrows | `Ty::HArrow(src, tgt)` | `Ty::HArrow(src, tgt)` |
| Signal universe | `Ty::SignalUniverseType` | `Ty::SignalUniverseType` |
| Module universe | `Ty::ModuleUniverseType` | `Ty::ModuleUniverseType` |

The key difference: `syn::Ty` uses `Binding<RcTy>` (De Bruijn syntax) while `val::Ty` uses `TyClosure` (environment-based closure).

## Implementation Tasks

### Task 1: Create syn::Ty Module

**File**: `crates/hwml-core/src/syn/ty.rs` (NEW)

1. Define `Ty<'db>` enum with variants matching `val::Ty` structure
2. Define `RcTy<'db>` and `BindingTy<'db>` type aliases
3. Implement constructor methods following `val::Ty` pattern:
   - `universe_type()`, `universe_type_rc()`
   - `signal_universe_type()`, `signal_universe_type_rc()`
   - `module_universe_type()`, `module_universe_type_rc()`
   - `pi()`, `pi_rc()`
   - `harrow()`, `harrow_rc()`
   - `el()`, `el_rc()`
   - `signal_el()`, `signal_el_rc()`
   - `module_el()`, `module_el_rc()`

**Rationale**: Following the exact pattern of `val::Ty` ensures consistency and makes the relationship between syntax and semantic types clear.

### Task 2: Update Check Node

**File**: `crates/hwml-core/src/syn/syntax.rs`

**Change** (lines 724-734):
```rust
// BEFORE
pub struct Check<'db> {
    pub ty: RcSyntax<'db>,
    pub term: RcSyntax<'db>,
}

// AFTER
pub struct Check<'db> {
    pub ty: RcTy<'db>,      // ← Now holds a type!
    pub term: RcSyntax<'db>,
}
```

**Constructor update**:
```rust
// Update Check::new signature
pub fn new(ty: RcTy<'db>, term: RcSyntax<'db>) -> Check<'db> {
    Check { ty, term }
}

// Update Syntax helper methods
pub fn check(ty: RcTy<'db>, term: RcSyntax<'db>) -> Syntax<'db> {
    Syntax::Check(Check::new(ty, term))
}

pub fn check_rc(ty: RcTy<'db>, term: RcSyntax<'db>) -> RcSyntax<'db> {
    Rc::new(Syntax::check(ty, term))
}
```

### Task 3: Evaluation - Eval syn::Ty to val::Ty

**File**: `crates/hwml-core/src/eval.rs` (NEW SECTION)

Add type evaluation function:

```rust
/// Evaluate a syntax-level type to a semantic type
pub fn eval_ty<'db, 'g>(
    env: &mut Environment<'db, 'g>,
    ty: &syn::Ty<'db>,
) -> Result<RcTy<'db>, Error<'db>> {
    match ty {
        // Universe types evaluate to themselves
        syn::Ty::UniverseType => Ok(val::Ty::universe_type_rc()),
        syn::Ty::SignalUniverseType => Ok(val::Ty::signal_universe_type_rc()),
        syn::Ty::ModuleUniverseType => Ok(val::Ty::module_universe_type_rc()),

        // Pi type: evaluate domain, extend context, evaluate codomain
        syn::Ty::Pi(source, target) => {
            let source_ty = eval_ty(env, source)?;

            // Create a fresh variable for the extended context
            let var_ty = eval(env, &target.body)?; // Evaluate type of binding
            env.local.push(var_ty.clone());

            // Evaluate the codomain type
            let target_ty = eval_ty(env, &target.term())?;

            // Create a TyClosure
            let closure = val::TyClosure::new(env.local.clone(), target_ty);

            env.local.pop();

            Ok(val::Ty::pi_rc(source_ty, closure))
        }

        // Hardware arrow: evaluate both sides
        syn::Ty::HArrow(source, target) => {
            let source_ty = eval_ty(env, source)?;
            let target_ty = eval_ty(env, target)?;
            Ok(val::Ty::harrow_rc(source_ty, target_ty))
        }

        // El decoders: evaluate the code and wrap in El
        syn::Ty::El(code) => {
            let code_val = eval(env, code)?;
            Ok(val::Ty::el_rc(code_val))
        }

        syn::Ty::SignalEl(code) => {
            let code_val = eval(env, code)?;
            Ok(val::Ty::signal_el_rc(code_val))
        }

        syn::Ty::ModuleEl(code) => {
            let code_val = eval(env, code)?;
            Ok(val::Ty::module_el_rc(code_val))
        }
    }
}
```

**Update eval_check**:
```rust
fn eval_check<'db, 'g>(
    env: &mut Environment<'db, 'g>,
    chk: &syn::Check<'db>,
) -> Result<RcValue<'db>, Error<'db>> {
    // Just evaluate the term - the type is already a syn::Ty
    eval(env, &chk.term)
}
```

### Task 4: Quotation - Quote val::Ty to syn::Ty

**File**: `crates/hwml-core/src/quote.rs` (NEW SECTION)

Add type quotation function:

```rust
/// Quote a semantic type back to syntax
pub fn quote_ty<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    depth: usize,
    ty: &val::Ty<'db>,
) -> Result<'db, syn::RcTy<'db>> {
    match ty {
        // Universe types quote to themselves
        val::Ty::UniverseType => Ok(syn::Ty::universe_type_rc()),
        val::Ty::SignalUniverseType => Ok(syn::Ty::signal_universe_type_rc()),
        val::Ty::ModuleUniverseType => Ok(syn::Ty::module_universe_type_rc()),

        // Pi type: quote domain, extend context, quote codomain
        val::Ty::Pi(source, target) => {
            let source_syn = quote_ty(db, global, depth, source)?;

            // Create a fresh variable at this depth
            let var = val::Value::variable_rc(
                Level(depth),
                val::Ty::el_rc(val::Value::UniverseCode(0).into())
            );

            // Apply closure to get codomain type
            let mut extended_local = target.local.clone();
            extended_local.push(var);

            // Quote the codomain
            let target_syn = quote_ty(db, global, depth + 1, &target.body)?;

            // Create binding
            let binding = Binding::anonymous(db, target_syn);

            Ok(syn::Ty::pi_rc(source_syn, binding))
        }

        // Hardware arrow
        val::Ty::HArrow(source, target) => {
            let source_syn = quote_ty(db, global, depth, source)?;
            let target_syn = quote_ty(db, global, depth, target)?;
            Ok(syn::Ty::harrow_rc(source_syn, target_syn))
        }

        // El decoders: quote the code
        val::Ty::El(code) => {
            let code_syn = type_quote(db, global, depth, code)?;
            Ok(syn::Ty::el_rc(code_syn))
        }

        val::Ty::SignalEl(code) => {
            let code_syn = type_quote(db, global, depth, code)?;
            Ok(syn::Ty::signal_el_rc(code_syn))
        }

        val::Ty::ModuleEl(code) => {
            let code_syn = type_quote(db, global, depth, code)?;
            Ok(syn::Ty::module_el_rc(code_syn))
        }
    }
}
```

### Task 5: Printing syn::Ty

**File**: `crates/hwml-core/src/syn/print.rs`

Implement `Print` trait for `syn::Ty`:

```rust
impl<'db> Print for syn::Ty<'db> {
    fn print<R: Render>(
        &self,
        db: &dyn salsa::Database,
        st: State,
        ns: &mut NameStack,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        match self {
            syn::Ty::UniverseType => p.text("UniverseType"),
            syn::Ty::SignalUniverseType => p.text("SignalUniverseType"),
            syn::Ty::ModuleUniverseType => p.text("ModuleUniverseType"),

            syn::Ty::Pi(source, target) => {
                // Print as: (name : source) → target
                p.text("(")?;
                // Push binder name
                ns.push_fresh(target.name.to_string(db));
                p.text_owned(format!("%{} : ", ns.get(ns.len() - 1).unwrap()))?;
                source.print(db, st, ns, p)?;
                p.text(") → ")?;
                target.term().print(db, st.inc_depth(), ns, p)?;
                ns.pop();
                Ok(())
            }

            syn::Ty::HArrow(source, target) => {
                source.print(db, st, ns, p)?;
                p.text(" ⇒ ")?;
                target.print(db, st, ns, p)
            }

            syn::Ty::El(code) => {
                p.text("El(")?;
                code.print(db, st, ns, p)?;
                p.text(")")
            }

            syn::Ty::SignalEl(code) => {
                p.text("SignalEl(")?;
                code.print(db, st, ns, p)?;
                p.text(")")
            }

            syn::Ty::ModuleEl(code) => {
                p.text("ModuleEl(")?;
                code.print(db, st, ns, p)?;
                p.text(")")
            }
        }
    }
}

impl<'db> Print for syn::RcTy<'db> {
    fn print<R: Render>(
        &self,
        db: &dyn salsa::Database,
        st: State,
        ns: &mut NameStack,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        self.as_ref().print(db, st, ns, p)
    }
}

impl<'db> Print for syn::BindingTy<'db> {
    fn print<R: Render>(
        &self,
        db: &dyn salsa::Database,
        st: State,
        ns: &mut NameStack,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        ns.push_fresh(self.name.to_string(db));
        let result = self.term().print(db, st.inc_depth(), ns, p);
        ns.pop();
        result
    }
}
```

### Task 6: Parsing syn::Ty

**File**: `crates/hwml-core/src/syn/parse.rs`

Add parsing support for type expressions:

```rust
/// Parse a type expression
/// Types can be:
/// - UniverseType, SignalUniverseType, ModuleUniverseType
/// - (x : A) → B  (Pi type)
/// - A ⇒ B  (HArrow)
/// - El(code), SignalEl(code), ModuleEl(code)
fn p_type<'db>(state: &mut State<'_, 'db>) -> ParseResult<syn::RcTy<'db>> {
    // Try to parse universe types first
    if let Some(Token::UniverseType) = state.peek_token() {
        state.advance();
        return Ok(syn::Ty::universe_type_rc());
    }

    if let Some(Token::SignalUniverseType) = state.peek_token() {
        state.advance();
        return Ok(syn::Ty::signal_universe_type_rc());
    }

    if let Some(Token::ModuleUniverseType) = state.peek_token() {
        state.advance();
        return Ok(syn::Ty::module_universe_type_rc());
    }

    // Try El decoders
    if let Some(Token::El) = state.peek_token() {
        state.advance();
        expect_token(state, Token::LParen)?;
        let code = p_term(state)?;
        expect_token(state, Token::RParen)?;
        return Ok(syn::Ty::el_rc(code));
    }

    if let Some(Token::SignalEl) = state.peek_token() {
        state.advance();
        expect_token(state, Token::LParen)?;
        let code = p_term(state)?;
        expect_token(state, Token::RParen)?;
        return Ok(syn::Ty::signal_el_rc(code));
    }

    if let Some(Token::ModuleEl) = state.peek_token() {
        state.advance();
        expect_token(state, Token::LParen)?;
        let code = p_term(state)?;
        expect_token(state, Token::RParen)?;
        return Ok(syn::Ty::module_el_rc(code));
    }

    // Try Pi type: (x : A) → B
    if let Some(Token::LParen) = state.peek_token() {
        // Could be Pi type or parenthesized type
        return p_pi_or_paren_type(state);
    }

    // Otherwise, try to parse as El of a term
    let code = p_term(state)?;
    Ok(syn::Ty::el_rc(code))
}

/// Parse either a Pi type (x : A) → B or a parenthesized type
fn p_pi_or_paren_type<'db>(state: &mut State<'_, 'db>) -> ParseResult<syn::RcTy<'db>> {
    let checkpoint = state.position();

    expect_token(state, Token::LParen)?;

    // Try to parse as Pi: (name : type) → ...
    if let Ok(name) = p_binder_name(state) {
        if let Some(Token::Colon) = state.peek_token() {
            state.advance();
            let source = p_type(state)?;
            expect_token(state, Token::RParen)?;
            expect_token(state, Token::Arrow)?;
            let target = p_type(state)?;

            let binding = Binding::new(name, target);
            return Ok(syn::Ty::pi_rc(source, binding));
        }
    }

    // Not a Pi type, try as parenthesized type
    state.reset_to(checkpoint);
    expect_token(state, Token::LParen)?;
    let ty = p_type(state)?;
    expect_token(state, Token::RParen)?;
    Ok(ty)
}
```

**Update p_check to use p_type**:
```rust
fn p_check<'db>(state: &mut State<'_, 'db>) -> ParseResult<RcSyntax<'db>> {
    let term = p_term_app(state)?;

    if let Some(Token::Colon) = state.peek_token() {
        state.advance();
        let ty = p_type(state)?;  // ← Now parses syn::Ty
        Ok(Syntax::check_rc(ty, term))
    } else {
        Ok(term)
    }
}
```

### Task 7: Typechecking Updates

**File**: `crates/hwml-core/src/check.rs`

Update `type_synth_check` to work with `syn::Ty`:

```rust
pub fn type_synth_check<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    check: &syn::Check<'db>,
) -> Result<RcValue<'db>, Error<'db>> {
    // Evaluate the syn::Ty to get a val::Ty
    let sem_ty = eval_ty(env, &check.ty)?;

    // Convert val::Ty to val::Value (type code) for typechecking
    // Most of the time this will be Ty::El(code), so extract the code
    let ty_code = match sem_ty.as_ref() {
        val::Ty::El(code) => code.clone(),
        val::Ty::UniverseType => Value::UniverseCode(0).into(), // Default universe
        val::Ty::SignalUniverseType => Value::signal_universe_rc(),
        val::Ty::ModuleUniverseType => Value::module_universe_rc(),
        // For Pi and other complex types, we need to convert to a type code
        _ => {
            // This is a placeholder - in practice we'd need a ty_to_code function
            return Err(Error::BadCheck {
                tm: Syntax::check_rc(check.ty.clone(), check.term.clone()),
                ty_got: Value::UniverseCode(0).into(),
                ty_exp: Value::UniverseCode(0).into(),
            });
        }
    };

    // Typecheck the term against the type code
    type_check(env, &check.term, &ty_code)?;
    Ok(ty_code)
}
```

**Note**: The above shows we need a helper to convert `val::Ty` back to `val::Value` (type codes). This is the inverse of the El decoder.

### Task 8: Module System Integration

**File**: `crates/hwml-core/src/syn/mod.rs`

Add export for the new ty module:

```rust
pub mod declaration;
pub mod parse;
pub mod print;
pub mod syntax;
pub mod telescope;
pub mod ty;  // ← NEW

pub use declaration::*;
pub use parse::*;
pub use print::*;
pub use syntax::*;
pub use telescope::*;
pub use ty::*;  // ← NEW
```

**File**: `crates/hwml-core/src/lib.rs`

Update re-exports:

```rust
pub use syn::{
    parse_module, BindingSyntax, DynBindingSyntax,
    RcSyntax, Syntax,
    RcTy as SynRcTy, Ty as SynTy,  // ← NEW type exports
};
```

### Task 9: Test Updates

All existing tests that create `Check` nodes will need updates:

**Pattern to find**:
```rust
Syntax::check_rc(
    Syntax::UniverseCode(0).into(),  // Old: RcSyntax
    term
)
```

**Replace with**:
```rust
Syntax::check_rc(
    syn::Ty::el_rc(Syntax::UniverseCode(0).into()),  // New: RcTy wrapping El
    term
)
```

**Files to update**:
- `crates/hwml-core/src/syn/parse.rs` - Test cases
- `crates/hwml-core/src/eval.rs` - Test cases
- `crates/hwml-core/src/check.rs` - Test cases
- `crates/hwml-elab/src/elab/expr.rs` - Elaborator code generation

### Task 10: Helper Functions

Add convenience functions for common patterns:

**File**: `crates/hwml-core/src/syn/ty.rs`

```rust
impl<'db> Ty<'db> {
    /// Create El(UniverseCode(n)) - the most common type
    pub fn universe(level: usize) -> syn::RcTy<'db> {
        syn::Ty::el_rc(Syntax::UniverseCode(level).into())
    }

    /// Create El(PiCode(...)) - dependent function type as El
    pub fn pi_code(
        source: RcSyntax<'db>,
        icit: Icit,
        target: BindingSyntax<'db>,
    ) -> syn::RcTy<'db> {
        syn::Ty::el_rc(Syntax::PiCode(source, icit, target).into())
    }

    /// Create El(BitCode) - Bit type
    pub fn bit() -> syn::RcTy<'db> {
        syn::Ty::el_rc(Syntax::BitCode.into())
    }
}
```

## Conversion Between Representations

### Key Insight: The El Relationship

The relationship between the three layers:

1. **Syntax type codes** (`Syntax::UniverseCode`, `Syntax::PiCode`, etc.)
   - These are TERMS in the syntax
   - They can be evaluated to values

2. **Value type codes** (`Value::UniverseCode`, `Value::PiCode`, etc.)
   - These are TERMS in the semantic domain
   - They represent types as data

3. **Semantic types** (`val::Ty::El(code)`)
   - These are TYPES that the typechecker uses
   - `El` decodes a type code (value) into a type

4. **Syntax types** (`syn::Ty::El(code)`)
   - These are TYPES in the syntax
   - `El` decodes a type code (syntax) into a type

### Flow Diagram

```
Source Code:  "𝒰0"
    ↓ Parse
syn::Syntax:  UniverseCode(0)           [term]
    ↓ Wrap in El
syn::Ty:      El(UniverseCode(0))       [type]
    ↓ Evaluate type
val::Ty:      El(Value::UniverseCode(0)) [type]
    ↓ Use in typechecking

Source Code:  "(x : Nat) → Vec A x"
    ↓ Parse
syn::Syntax:  PiCode(Nat, ...)          [term]
    ↓ Wrap in El
syn::Ty:      El(PiCode(Nat, ...))      [type]
    ↓ Evaluate type
val::Ty:      El(Value::PiCode(...))    [type]
    ↓ Use in typechecking
```

### The Two Universes

There are actually TWO parallel type systems:

1. **Meta-level types** (types of types)
   - `syn::Ty::UniverseType` / `val::Ty::UniverseType`
   - The TYPE of `UniverseCode(0)`
   - Not wrapped in El

2. **Object-level types** (types of terms)
   - `syn::Ty::El(code)` / `val::Ty::El(code)`
   - Types constructed from type codes
   - Wrapped in El

## Migration Strategy

### Phase 1: Add syn::Ty module (non-breaking)
1. Create `syn/ty.rs` with full implementation
2. Add exports to `syn/mod.rs`
3. Add helper functions
4. Add printing support
5. Add parsing support (new keywords/syntax)

### Phase 2: Add evaluation/quotation (non-breaking)
1. Add `eval_ty` to `eval.rs`
2. Add `quote_ty` to `quote.rs`
3. Add tests for round-tripping

### Phase 3: Update Check node (BREAKING)
1. Change `Check::ty` from `RcSyntax` to `RcTy`
2. Update all constructor calls
3. Update typechecker
4. Update tests
5. Update elaborator

### Phase 4: Conversion helpers
1. Add `ty_to_code` and `code_to_ty` converters
2. Add convenience constructors
3. Document usage patterns

## Testing Strategy

### Unit Tests

1. **Round-trip tests** (syn::Ty → val::Ty → syn::Ty)
   ```rust
   #[test]
   fn test_type_roundtrip_universe() {
       let syn_ty = syn::Ty::universe_type_rc();
       let val_ty = eval_ty(&env, &syn_ty)?;
       let back = quote_ty(db, &global, 0, &val_ty)?;
       assert_eq!(*syn_ty, *back);
   }
   ```

2. **Printing tests**
   ```rust
   #[test]
   fn test_print_pi_type() {
       let ty = syn::Ty::pi_rc(...);
       assert_eq!(print_type_to_string(db, &ty), "(x : Nat) → Vec A x");
   }
   ```

3. **Parsing tests**
   ```rust
   #[test]
   fn test_parse_el_type() {
       let ty = parse_type(db, "El(𝒰0)");
       assert!(matches!(ty.as_ref(), syn::Ty::El(_)));
   }
   ```

4. **Check node tests**
   ```rust
   #[test]
   fn test_check_with_type() {
       let ty = syn::Ty::el_rc(Syntax::UniverseCode(0).into());
       let term = Syntax::lambda_rc(...);
       let check = Syntax::check_rc(ty, term);
       // Test evaluation and typechecking
   }
   ```

## Documentation

Key documentation to add:

1. **Module-level docs** in `syn/ty.rs` explaining:
   - The Tarski universe approach
   - Relationship to `val::Ty`
   - When to use `Ty::El` vs direct constructors

2. **Examples** showing:
   - Creating syntax-level types
   - Using Check nodes
   - Converting between representations

3. **Design docs** explaining:
   - Why we need three representations
   - The role of El decoders
   - Migration from old Check structure

## Summary

This implementation adds a missing piece to the type system: syntax-level types that mirror the semantic types. The key insight is that just as we have:

- `Syntax` (unevaluated terms) → `Value` (evaluated terms)

We need:

- `syn::Ty` (unevaluated types) → `val::Ty` (evaluated types)

The Tarski universe approach with `El` decoders is consistently applied at both levels, creating a clean, symmetric design that makes the type system easier to understand and maintain.

