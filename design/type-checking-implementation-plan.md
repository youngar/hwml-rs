# Type Checking Implementation Plan - Phase 7

## Overview

This document details the implementation plan for type checking hardware constructs in `check.rs`.

## Type Checking Rules Reference

### HardwareUniverse Universe

```
─────────────────────────
Γ ⊢ Type : Type
```

### HardwareUniverse Types

```
─────────────────────────
Γ ⊢ Bit : Type

Γ ⊢ a : Type    Γ ⊢ b : Type
──────────────────────────────────────────
Γ ⊢ (a -> b) : Type
```

### Lift (HardwareUniverse Type → Meta Type)

```
Γ ⊢ ht : Type
────────────────────
Γ ⊢ ^ht : Type
```

### Quote (HardwareUniverse Term → Meta Term)

```
Γ ⊢ circuit : HWTerm ht    Γ ⊢ ht : Type
───────────────────────────────────────────────
Γ ⊢ 'circuit : ^ht
```

### Splice (Meta Term → HardwareUniverse Term)

```
Γ ⊢ tm : ^ht    Γ ⊢ ht : Type
────────────────────────────────────
Γ ⊢ ~tm : HWTerm ht
```

### HardwareUniverse Primitives

```
─────────────────────
Γ ⊢ 0 : HWTerm Bit

─────────────────────
Γ ⊢ 1 : HWTerm Bit

─────────────────────────────────────────────────
Γ ⊢ and : HWTerm (Bit -> Bit -> Bit)

─────────────────────────────────────────────────
Γ ⊢ or : HWTerm (Bit -> Bit -> Bit)

─────────────────────────────────────────────────
Γ ⊢ xor : HWTerm (Bit -> Bit -> Bit)

─────────────────────────────────────
Γ ⊢ not : HWTerm (Bit -> Bit)
```

### HardwareUniverse Lambda

```
Γ, x : HWTerm a ⊢ body : HWTerm b
──────────────────────────────────────
Γ ⊢ (λx. body) : HWTerm (a -> b)
```

### HardwareUniverse Application

```
Γ ⊢ f : HWTerm (a -> b)    Γ ⊢ arg : HWTerm a
──────────────────────────────────────────────────
Γ ⊢ f arg : HWTerm b
```

## Implementation Steps

### Step 1: Update Error Types

Add new error variants for hardware type checking:

```rust
pub enum Error<'db> {
    // ... existing variants ...
    
    /// Expected a hardware type (Type)
    NotHWType {
        tm: Rc<Syntax<'db>>,
        ty_got: RcValue<'db>,
    },
    
    /// Expected a lifted type (^ht)
    NotLiftedType {
        tm: Rc<Syntax<'db>>,
        ty_got: RcValue<'db>,
    },
    
    /// HardwareUniverse term type error
    HWTermTypeError {
        hw_term: Rc<HWTerm<'db>>,
        hw_ty_exp: RcValue<'db>,
        hw_ty_got: RcValue<'db>,
    },
    
    /// Cannot splice non-quoted value
    BadSplice {
        tm: Rc<Syntax<'db>>,
        ty_got: RcValue<'db>,
    },
}
```

### Step 2: Extend Type Synthesis

Update `type_synth` to handle new constructs:

```rust
pub fn type_synth<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    term: &Syntax<'db>,
) -> Result<RcValue<'db>, Error<'db>> {
    match term {
        // ... existing cases ...
        Syntax::Variable(variable) => type_synth_variable(env, variable),
        Syntax::Check(check) => type_synth_check(env, check),
        Syntax::Application(application) => type_synth_application(env, application),
        Syntax::Case(case) => type_synth_case(env, case),
        Syntax::Metavariable(metavariable) => type_synth_metavariable(env, metavariable),
        
        // HardwareUniverse constructs
        Syntax::Lift(lift) => type_synth_lift(env, lift),
        Syntax::Quote(quote) => type_synth_quote(env, quote),
        
        _ => Err(Error::BadSynth {
            tm: Rc::new(term.clone()),
        }),
    }
}
```

#### 4.5 Type Synthesize Quote

```rust
/// Synthesize type of quoted hardware term
/// 'circuit : ^ht when circuit : HWTerm ht
fn type_synth_quote<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    quote: &syn::Quote<'db>,
) -> Result<RcValue<'db>, Error<'db>> {
    // Type check the hardware term and get its hardware type
    let hw_ty = type_check_hwterm(env, &quote.hw_term)?;

    // Return ^ht
    Ok(Rc::new(Value::lift(hw_ty)))
}
```

#### 4.6 Type Check Quote

```rust
/// Check quoted term against expected type
/// 'circuit : ^ht when circuit : HWTerm ht
fn type_check_quote<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    quote: &syn::Quote<'db>,
    ty_exp: &Value<'db>,
) -> Result<(), Error<'db>> {
    // Expected type must be a lifted type ^ht
    let Value::Lift(hw_ty_exp) = ty_exp else {
        return Err(Error::NotLiftedType {
            tm: Rc::new(Syntax::Quote(quote.clone())),
            ty_got: Rc::new(ty_exp.clone()),
        });
    };

    // Type check the hardware term against the hardware type
    type_check_hwterm_against(env, &quote.hw_term, hw_ty_exp)?;
    Ok(())
}
```

### Step 5: Helper Functions

#### 5.1 Check if Term is HardwareUniverse Type

```rust
/// Check that a term is a valid hardware type (has type Type)
fn check_is_hwtype<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    term: &Syntax<'db>,
) -> Result<(), Error<'db>> {
    // Synthesize the type of the term
    let ty = type_synth(env, term)?;

    // Check that it's Type
    match &*ty {
        Value::Type(_) => Ok(()),
        _ => Err(Error::NotHWType {
            tm: Rc::new(term.clone()),
            ty_got: ty,
        }),
    }
}
```

#### 5.2 Type Check HardwareUniverse Term (Synthesis)

```rust
/// Type check a hardware term and synthesize its hardware type
/// Returns a Value that should be a hardware type (Bit, HArrow, etc.)
fn type_check_hwterm<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    hw_term: &HWTerm<'db>,
) -> Result<RcValue<'db>, Error<'db>> {
    match hw_term {
        // Bit constants
        HWTerm::Zero(_) => Ok(Rc::new(Value::bit())),
        HWTerm::One(_) => Ok(Rc::new(Value::bit())),

        // Bit operations
        HWTerm::And(_) | HWTerm::Or(_) | HWTerm::Xor(_) => {
            // and : Bit -> Bit -> Bit
            let bit = Rc::new(Value::bit());
            let bit_to_bit = Rc::new(Value::harrow(bit.clone(), bit.clone()));
            Ok(Rc::new(Value::harrow(bit, bit_to_bit)))
        }

        HWTerm::Not(_) => {
            // not : Bit -> Bit
            let bit = Rc::new(Value::bit());
            Ok(Rc::new(Value::harrow(bit.clone(), bit)))
        }

        // Variables
        HWTerm::HVariable(var) => {
            // Look up variable in environment
            // For now, we need to extend TCEnvironment to track hardware types
            todo!("hardware variable lookup")
        }

        // Constants
        HWTerm::HConst(const_id) => {
            // Look up constant in global environment
            todo!("hardware constant lookup")
        }

        // Lambda
        HWTerm::HLam(lam) => {
            // Need to infer the domain type
            // This is tricky without type annotations
            todo!("hardware lambda type inference")
        }

        // Application
        HWTerm::HApp(app) => {
            type_synth_hwterm_application(env, app)
        }

        // Splice
        HWTerm::Splice(splice) => {
            type_synth_hwterm_splice(env, splice)
        }

        // Type annotation
        HWTerm::HCheck(check) => {
            // Evaluate the type annotation
            let hw_ty = eval(env, &hwterm_to_syntax(&check.ty)?)?;

            // Check the term against the type
            type_check_hwterm_against(env, &check.term, &hw_ty)?;

            Ok(hw_ty)
        }
    }
}
```

#### 5.3 Type Check HardwareUniverse Application

```rust
/// Type synthesize hardware application
fn type_synth_hwterm_application<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    app: &hwterm::HWApplication<'db>,
) -> Result<RcValue<'db>, Error<'db>> {
    // Synthesize type of function
    let fun_ty = type_check_hwterm(env, &app.function)?;

    // Function type must be a hardware arrow
    let Value::HArrow(harrow) = &*fun_ty else {
        return Err(Error::HWTermTypeError {
            hw_term: Rc::new(HWTerm::HApp(app.clone())),
            hw_ty_exp: Rc::new(Value::harrow(
                Rc::new(Value::bit()),
                Rc::new(Value::bit()),
            )),
            hw_ty_got: fun_ty,
        });
    };

    // Check argument against source type
    type_check_hwterm_against(env, &app.argument, &harrow.source)?;

    // Return target type
    Ok(harrow.target.clone())
}
```

#### 5.4 Type Check HardwareUniverse Splice

```rust
/// Type synthesize hardware splice
fn type_synth_hwterm_splice<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    splice: &hwterm::Splice<'db>,
) -> Result<RcValue<'db>, Error<'db>> {
    // Synthesize type of meta term
    let meta_ty = type_synth(env, &splice.term)?;

    // Meta term must have a lifted type ^ht
    let Value::Lift(hw_ty) = &*meta_ty else {
        return Err(Error::BadSplice {
            tm: splice.term.clone(),
            ty_got: meta_ty,
        });
    };

    // Return the hardware type ht
    Ok(hw_ty.clone())
}
```

#### 5.5 Type Check HardwareUniverse Term Against Type

```rust
/// Type check a hardware term against an expected hardware type
fn type_check_hwterm_against<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    hw_term: &HWTerm<'db>,
    hw_ty_exp: &Value<'db>,
) -> Result<(), Error<'db>> {
    match hw_term {
        // For lambdas, we can check directly
        HWTerm::HLam(lam) => {
            type_check_hwterm_lambda(env, lam, hw_ty_exp)
        }

        // For everything else, synthesize and compare
        _ => {
            let hw_ty_got = type_check_hwterm(env, hw_term)?;

            // Check convertibility
            match equal::is_convertible(env.values.global, env.depth(), hw_ty_exp, &hw_ty_got) {
                Ok(()) => Ok(()),
                Err(_) => Err(Error::HWTermTypeError {
                    hw_term: Rc::new(hw_term.clone()),
                    hw_ty_exp: Rc::new(hw_ty_exp.clone()),
                    hw_ty_got,
                }),
            }
        }
    }
}
```

#### 5.6 Type Check HardwareUniverse Lambda

```rust
/// Type check hardware lambda against expected type
fn type_check_hwterm_lambda<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    lam: &hwterm::HWLambda<'db>,
    hw_ty_exp: &Value<'db>,
) -> Result<(), Error<'db>> {
    // Expected type must be a hardware arrow
    let Value::HArrow(harrow) = hw_ty_exp else {
        return Err(Error::HWTermTypeError {
            hw_term: Rc::new(HWTerm::HLam(lam.clone())),
            hw_ty_exp: Rc::new(hw_ty_exp.clone()),
            hw_ty_got: Rc::new(Value::harrow(
                Rc::new(Value::bit()),
                Rc::new(Value::bit()),
            )),
        });
    };

    // Extend environment with variable of source type
    // NOTE: We need to extend TCEnvironment to track hardware variables
    // For now, this is a placeholder
    todo!("extend environment with hardware variable and check body")
}
```

### Step 6: Update `check_type`

```rust
pub fn check_type<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    term: &Syntax<'db>,
) -> Result<(), Error<'db>> {
    // Special cases for hardware constructs
    if let Syntax::Lift(lift) = term {
        return check_lift_is_type(env, lift);
    }

    // Bit and HArrow are NOT valid types at meta level
    // They must be lifted
    if matches!(term, Syntax::Bit(_) | Syntax::HArrow(_)) {
        return Err(Error::BadType {
            tm: Rc::new(term.clone()),
        });
    }

    // ... existing logic for Pi, TypeConstructor, etc.
}

fn check_lift_is_type<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    lift: &syn::Lift<'db>,
) -> Result<(), Error<'db>> {
    // Check that the inner term is a valid hardware type
    check_is_hwtype(env, &lift.hw_type)
}
```

### Step 7: Environment Extensions (Future Work)

To properly support hardware variables, we need to extend `TCEnvironment`:

```rust
pub struct TCEnvironment<'db, 'g> {
    pub values: val::Environment<'db, 'g>,
    pub types: Vec<RcValue<'db>>,

    // NEW: Track hardware variables and their types
    pub hw_values: Vec<Rc<HWTerm<'db>>>,  // HardwareUniverse variable values
    pub hw_types: Vec<RcValue<'db>>,    // HardwareUniverse types (should be HWType values)
}
```

This is needed for:
- Looking up hardware variables
- Type checking hardware lambdas
- Proper scoping of hardware terms

## Summary

This implementation plan covers:

1. ✅ Error types for hardware constructs
2. ✅ Type synthesis for `Lift` and `Quote`
3. ✅ Type checking for `Bit`, `HArrow`, `Lift`, `Quote`
4. ✅ HardwareUniverse term type checking (primitives, application, splice)
5. ✅ Helper functions for hardware type checking
6. ⚠️ HardwareUniverse variables (needs environment extension)
7. ⚠️ HardwareUniverse lambdas (needs environment extension)

## Next Steps

1. Implement basic hardware type checking (Steps 1-6)
2. Extend environment to support hardware variables (Step 7)
3. Add tests for each construct
4. Implement hardware lambda type checking
5. Add support for more hardware primitives (vectors, etc.)

### Step 3: Extend Type Checking

Update `type_check` to handle new constructs:

```rust
pub fn type_check<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    term: &Syntax<'db>,
    ty: &Value<'db>,
) -> Result<(), Error<'db>> {
    match term {
        // ... existing cases ...
        Syntax::Pi(pi) => type_check_pi(env, pi, ty),
        Syntax::Lambda(lam) => type_check_lambda(env, lam, ty),
        Syntax::TypeConstructor(tc) => type_check_type_constructor(env, tc, ty),
        Syntax::DataConstructor(dc) => type_check_data_constructor(env, dc, ty),
        
        // HardwareUniverse type constructors
        Syntax::Bit(_) => type_check_bit(env, ty),
        Syntax::HArrow(harrow) => type_check_harrow(env, harrow, ty),
        
        // Staging constructs
        Syntax::Lift(lift) => type_check_lift(env, lift, ty),
        Syntax::Quote(quote) => type_check_quote(env, quote, ty),
        
        _ => type_check_synth_term(env, term, ty),
    }
}
```

### Step 4: Implement HardwareUniverse Type Checking Functions

#### 4.1 Type Check Bit

```rust
/// Check Bit against expected type
/// Bit : Type
fn type_check_bit<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    ty_exp: &Value<'db>,
) -> Result<(), Error<'db>> {
    // Bit must be checked against Type
    match ty_exp {
        Value::Type(_) => Ok(()),
        _ => Err(Error::BadCtor {
            tm: Rc::new(Syntax::Bit(Bit::new())),
            ty_exp: Rc::new(ty_exp.clone()),
        }),
    }
}
```

#### 4.2 Type Check HardwareUniverse Arrow

```rust
/// Check hardware arrow against expected type
/// (a -> b) : Type when a, b : Type
fn type_check_harrow<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    harrow: &syn::HArrow<'db>,
    ty_exp: &Value<'db>,
) -> Result<(), Error<'db>> {
    // HArrow must be checked against Type
    match ty_exp {
        Value::Type(_) => {
            // Check that source and target are hardware types
            check_is_hwtype(env, &harrow.source)?;
            check_is_hwtype(env, &harrow.target)?;
            Ok(())
        }
        _ => Err(Error::BadCtor {
            tm: Rc::new(Syntax::HArrow(harrow.clone())),
            ty_exp: Rc::new(ty_exp.clone()),
        }),
    }
}
```

#### 4.3 Type Synthesize Lift

```rust
/// Synthesize type of lifted hardware type
/// ^ht : Type when ht : Type
fn type_synth_lift<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    lift: &syn::Lift<'db>,
) -> Result<RcValue<'db>, Error<'db>> {
    // Check that the inner term is a hardware type
    check_is_hwtype(env, &lift.hw_type)?;
    
    // ^ht : Type (Universe 0)
    Ok(Rc::new(Value::universe(UniverseLevel(0))))
}
```

#### 4.4 Type Check Lift

```rust
/// Check lifted type against expected type
fn type_check_lift<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    lift: &syn::Lift<'db>,
    ty_exp: &Value<'db>,
) -> Result<(), Error<'db>> {
    // Lift must be checked against a universe
    match ty_exp {
        Value::Universe(_) => {
            check_is_hwtype(env, &lift.hw_type)?;
            Ok(())
        }
        _ => Err(Error::BadCtor {
            tm: Rc::new(Syntax::Lift(lift.clone())),
            ty_exp: Rc::new(ty_exp.clone()),
        }),
    }
}
```


