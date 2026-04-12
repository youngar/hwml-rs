# Core Language Reference (hwmlc)

**Version**: 0.1.0
**Audience**: Compiler engineers, tooling developers, type theory implementers

This is the **formal reference manual** for the hwml Core IR. This is not a tutorial. If you're learning hwml, start with the user guide.

**Prerequisites**: This reference assumes familiarity with:
- Dependent type theory and bidirectional typechecking
- Normalization by Evaluation (NbE)
- De Bruijn indices/levels
- Inductive families with parameters and indices

---

## Table of Contents

1. [Overview](#overview)
2. [Syntax Grammar](#syntax-grammar)
3. [Type System](#type-system)
4. [Evaluation Semantics](#evaluation-semantics)
5. [Global Declarations](#global-declarations)
6. [Design Rationale](#design-rationale)

---

## Overview

The hwml Core IR is a **dependently-typed lambda calculus** with:

- **Predicative universe hierarchy**: `U0 : U1 : U2 : ...`
- **Dependent function types** (Pi types): `∀(%x : A) -> B` where `B` may depend on `%x`
- **Lambda abstractions**: `\%x -> e` with implicit typing
- **Applications**: `f x` (left-associative juxtaposition) or `f[x, y, z]` (bracket notation)
- **Inductive type families** with parameters (uniform) and indices (varying)
- **Data constructors** for canonical values
- **Pattern matching** via case trees (constructor-only, no wildcards)
- **Propositional equality**: `Eq A x y` with `refl` and `transport`
- **Hardware types**: `^A`, `^s A`, `^m A` with separate universe hierarchy
- **Signal types**: `Bit`, `0`, `1`
- **Module types**: `M -> N` (hardware arrow), `mod %x -> e` (module abstraction)

### Key Design Decisions

1. **Bidirectional Typechecking**: Explicit `Synth` (inference) and `Check` (validation) modes
2. **Normalization by Evaluation (NbE)**: Conversion checking via semantic evaluation
3. **Explicit Type Constructor Syntax**: `#[@Name ...]` for types, `[@Name ...]` for data, `@Name` for constants
4. **Constructor-Only Patterns**: Case expressions match only on data constructors
5. **Two-Phase Module Checking**: Signatures added before validation, enabling full mutual recursion

---

## Syntax Grammar

The Core IR has a concrete textual syntax mapping to `Syntax<'db>` in `crates/hwml-core/src/syn/basic.rs`.

### Notation Conventions

- `%x`, `%y`, `%z` - De Bruijn **indices** (variables bound by lambda/pi/let)
- `@Name` - Global constant references
- `#[@Name ...]` - Type constructor applications
- `[@Name ...]` - Data constructor applications
- `U0`, `U1`, `U2` - Universe levels
- `∀(%x : A) -> B` - Dependent function type (Pi type)
- `\%x -> e` - Lambda abstraction
- `f x` - Application (left-associative)
- `f[x, y, z]` - Bracket application (explicit multi-arg)

### Core Syntax Forms

| Concrete Syntax | AST Constructor | Payload |
|----------------|-----------------|---------|
| `%0`, `%1`, `%2` | `Syntax::Var(n)` | `usize` |
| `@Name` | `Syntax::Const(id)` | `ConstId` |
| `U0`, `U1`, `U2` | `Syntax::Universe(n)` | `usize` |
| `∀(%x : A) -> B` | `Syntax::Pi(name, dom, cod)` | `(Option<String>, RcSyntax, RcSyntax)` |
| `\%x -> e` | `Syntax::Lambda(name, body)` | `(Option<String>, RcSyntax)` |
| `f x` | `Syntax::App(fn, arg)` | `(RcSyntax, RcSyntax)` |
| `let %x := e in body` | `Syntax::Let(name, val, body)` | `(Option<String>, RcSyntax, RcSyntax)` |
| `#[@Name ...]` | `Syntax::TypeCon(id, args)` | `(TypeConId, Vec<RcSyntax>)` |
| `[@Name ...]` | `Syntax::DataCon(id, args)` | `(DataConId, Vec<RcSyntax>)` |
| `case e of ...` | `Syntax::Case(...)` | `(RcSyntax, Vec<Branch>, RcSyntax)` |
| `SignalUniverse` | `Syntax::SignalUniverse` | unit |
| `HardwareUniverse` | `Syntax::HardwareUniverse` | unit |
| `ModuleUniverse` | `Syntax::ModuleUniverse` | unit |
| `^A` | `Syntax::LiftCode(ty)` | `RcSyntax` |
| `^s A` | `Syntax::LiftSignal(ty)` | `RcSyntax` |
| `^m A` | `Syntax::LiftModule(ty)` | `RcSyntax` |
| `M -> N` | `Syntax::HardwareArrow(dom, cod)` | `(RcSyntax, RcSyntax)` |
| `mod %x -> e` | `Syntax::Module(name, body)` | `(Option<String>, RcSyntax)` |
| `f<T>(x)` | `Syntax::HApplication(fn, ty, arg)` | `(RcSyntax, RcSyntax, RcSyntax)` |
| `Eq A x y` | `Syntax::Eq(ty, lhs, rhs)` | `(RcSyntax, RcSyntax, RcSyntax)` |
| `refl` | `Syntax::Refl` | unit |
| `transport ...` | `Syntax::Transport(...)` | `(Option<String>, RcSyntax, RcSyntax, RcSyntax)` |

---

## Type System

The Core uses **bidirectional typechecking** with three main judgments:

1. **Synthesis** (`Γ ⊢ e ⇒ T`): Infer the type `T` of expression `e`
2. **Checking** (`Γ ⊢ e ⇐ T`): Validate that `e` has type `T`
3. **Universe Checking** (`Γ ⊢ T : Un`): Validate that `T` is a type in universe `Un`

Implementation: `crates/hwml-core/src/check.rs`

### Universes

**Syntax**: `U0`, `U1`, `U2`, ...

**AST**: `Syntax::Universe(n)`

**Typing Rule** (Synth):
```
─────────────────
Γ ⊢ Un ⇒ U(n+1)
```

**Evaluation**: `eval(Un, env) = Value::Universe(n)` (canonical form)

**Design Note**: Universes are **predicative** (no `Type : Type`). Each universe `Un` is a type in the next universe `U(n+1)`. This prevents Russell's paradox and ensures logical consistency.

### Variables

**Syntax**: `%0`, `%1`, `%2`, ... (De Bruijn indices)

**AST**: `Syntax::Var(n)`

**Typing Rule** (Synth):
```
Γ[n] = T
─────────────
Γ ⊢ %n ⇒ T
```

**Evaluation**: `eval(%n, env) = env[n]` (lookup in environment)

**Failure Mode**: Index `n` out of bounds (unbound variable)

**Design Note**: De Bruijn indices eliminate alpha-equivalence issues. Index `%0` refers to the **most recently bound** variable, `%1` to the second-most recent, etc.

### Constants

**Syntax**: `@Name`

**AST**: `Syntax::Const(id)`

**Typing Rule** (Synth):
```
Σ(@Name) = T
──────────────
Γ ⊢ @Name ⇒ T
```

**Evaluation**: `eval(@Name, env) = Σ(@Name).value` (global definition lookup)

**Failure Mode**: Constant `@Name` not found in signature `Σ`

**Design Note**: Constants are **global definitions** with a fixed type and value. They are resolved by name during parsing and stored as `ConstId` in the AST.

### Pi Types (Dependent Functions)

**Syntax**: `∀(%x : A) -> B` or `A -> B` (non-dependent shorthand)

**AST**: `Syntax::Pi(Option<String>, RcSyntax, RcSyntax)`

**Typing Rule** (CheckType):
```
Γ ⊢ A : Un
Γ, %x : A ⊢ B : Um
──────────────────────────
Γ ⊢ (∀(%x : A) -> B) : Umax(n,m)
```

**Evaluation**: `eval(∀(%x : A) -> B, env) = Value::Pi(name, eval(A, env), Closure(B, env))`

**Design Note**: Pi types are the **type of functions**. The codomain `B` can depend on the value of the parameter `%x`. Non-dependent functions `A -> B` are syntactic sugar for `∀(%_ : A) -> B`.

### Lambda Abstractions

**Syntax**: `\%x -> e`

**AST**: `Syntax::Lambda(Option<String>, RcSyntax)`

**Typing Rule** (Check):
```
Expected type: ∀(%x : A) -> B
Γ, %x : A ⊢ e ⇐ B
──────────────────────────
Γ ⊢ (\%x -> e) ⇐ ∀(%x : A) -> B
```

**Evaluation**: `eval(\%x -> e, env) = Value::Lambda(name, Closure(e, env))` (canonical form)

**Failure Mode**: Expected type is not a Pi type

**Design Note**: Lambdas are **introduction forms** for Pi types. They can only be checked, not synthesized (no type inference for lambdas).

### Application

**Syntax**: `f x` (left-associative) or `f[x, y, z]` (bracket notation)

**AST**: `Syntax::App(RcSyntax, RcSyntax)`

**Typing Rule** (Synth):
```
Γ ⊢ f ⇒ ∀(%x : A) -> B
Γ ⊢ x ⇐ A
────────────────────────
Γ ⊢ f x ⇒ B[x/%x]
```

**Evaluation**:
- **Beta reduction**: `eval((\%x -> e) v, env) = eval(e, env ++ [v])`
- **Neutral**: `eval(neutral v, env) = Value::Neutral(Eliminator::App(neutral, v))`

**Failure Modes**:
- `f` does not synthesize to a Pi type
- `x` does not check against domain type `A`

**Design Note**: Application is the **elimination form** for Pi types. The result type `B[x/%x]` is the codomain with the parameter substituted by the argument.

### Let Bindings

**Syntax**: `let %x := e in body`

**AST**: `Syntax::Let(Option<String>, RcSyntax, RcSyntax)`

**Typing Rule** (Synth):
```
Γ ⊢ e ⇒ A
Γ, %x : A ⊢ body ⇒ B
──────────────────────────
Γ ⊢ (let %x := e in body) ⇒ B
```

**Evaluation**: `eval(let %x := e in body, env) = eval(body, env ++ [eval(e, env)])` (substitution)

**Design Note**: Let bindings are **definitional** (not recursive). The value `e` is evaluated and substituted into `body`. This is equivalent to `(\%x -> body) e` but more efficient.

---

## Inductive Types

The Core IR supports **inductive type families** with parameters and indices.

### Type Constructors

**Syntax**: `#[@Name p1 p2 ... | i1 i2 ...]`

**AST**: `Syntax::TypeCon(TypeConId, Vec<RcSyntax>)`

**Typing Rule** (CheckType):
```
Σ(@Name) = TypeConstructor { params: n, indices: m, universe: u }
Γ ⊢ p1 ⇐ P1, ..., Γ ⊢ pn ⇐ Pn
Γ ⊢ i1 ⇐ I1, ..., Γ ⊢ im ⇐ Im
────────────────────────────────────────
Γ ⊢ #[@Name p1 ... pn | i1 ... im] : Uu
```

**Evaluation**: `eval(#[@Name ...], env) = Value::TypeCon(id, eval_args)` (canonical form)

**Design Note**: Type constructors are **type-level functions** that produce types. Parameters are **uniform** across all constructors, while indices can **vary** per constructor.

### Data Constructors

**Syntax**: `[@Name a1 a2 ...]`

**AST**: `Syntax::DataCon(DataConId, Vec<RcSyntax>)`

**Typing Rule** (Synth):
```
Σ(@Name) = DataConstructor { type_con: T, arg_types: [A1, ..., An], result_indices: [i1, ..., im] }
Γ ⊢ a1 ⇐ A1, ..., Γ ⊢ an ⇐ An
────────────────────────────────────────────────
Γ ⊢ [@Name a1 ... an] ⇒ #[T p1 ... pk | i1 ... im]
```

**Evaluation**: `eval([@Name ...], env) = Value::Data(id, eval_args)` (canonical form)

**Design Note**: Data constructors are **introduction forms** for inductive types. They produce values of the type constructor with specific indices.

### Pattern Matching (Case)

**Syntax**: `case e of { @Con1 %x %y -> branch1 | @Con2 %z -> branch2 | ... } : ReturnType`

**AST**: `Syntax::Case(RcSyntax, Vec<Branch>, RcSyntax)`

**Typing Rule** (Synth):
```
Γ ⊢ e ⇒ #[@T p1 ... pk | i1 ... im]
For each constructor @Conj of @T:
  Γ, %x1 : A1, ..., %xn : An ⊢ branchj ⇐ ReturnType
Γ ⊢ ReturnType : Un
────────────────────────────────────────────────
Γ ⊢ (case e of { ... }) ⇒ ReturnType
```

**Evaluation**:
- **Match**: `eval(case [@Con args] of { @Con %xs -> branch | ... }, env) = eval(branch, env ++ args)`
- **Stuck**: `eval(case neutral of { ... }, env) = Value::Neutral(Eliminator::Case(...))`

**Failure Modes**:
- `e` does not synthesize to a type constructor
- Branches are not exhaustive (missing constructors)
- Branch patterns are not constructor-only (no wildcards)

**Design Note**: Case expressions are **elimination forms** for inductive types. They must be **exhaustive** (cover all constructors) and use **constructor-only patterns** (no wildcards or nested patterns).

---

## Propositional Equality

The Core IR includes **propositional equality** as a primitive type former with reflection and transport.

### Equality Types

**Syntax**: `Eq A x y`

**AST**: `Syntax::Eq(RcSyntax, RcSyntax, RcSyntax)`

**Typing Rule** (CheckType):
```
Γ ⊢ A : Un
Γ ⊢ x ⇐ A
Γ ⊢ y ⇐ A
──────────────────
Γ ⊢ Eq A x y : Un
```

**Evaluation**: `eval(Eq A x y, env) = Value::Eq(eval(A, env), eval(x, env), eval(y, env))`

**Design Note**: Equality types are **heterogeneous** in the sense that `x` and `y` must have the same type `A`, but `A` itself can be a dependent type. This is **propositional equality** (proof-relevant), not **definitional equality** (conversion checking).

### Reflexivity (refl)

**Syntax**: `refl`

**AST**: `Syntax::Refl`

**Typing Rule** (Check):
```
Expected type: Eq A x y
Γ ⊢ x ≡ y : A  (conversion check)
──────────────────────────────
Γ ⊢ refl ⇐ Eq A x y
```

**Evaluation**: `eval(refl, env) = Value::Refl` (canonical form)

**Failure Mode**: `x` and `y` are not convertible (not definitionally equal)

**Design Note**: `refl` is the **introduction form** for equality types. It can only be used when `x` and `y` are **definitionally equal** (convertible via normalization).

### Transport

**Syntax**: `transport [%x] |- P proof value`

**AST**: `Syntax::Transport(Option<String>, RcSyntax, RcSyntax, RcSyntax)`

**Typing Rule** (Synth):
```
Γ ⊢ proof ⇒ Eq A x y
Γ, %x : A ⊢ P : Un
Γ ⊢ value ⇐ P[x/%x]
────────────────────────────────
Γ ⊢ (transport [%x] |- P proof value) ⇒ P[y/%x]
```

**Evaluation**:
- **With refl**: `eval(transport [%x] |- P refl value, env) = eval(value, env)` (transport along refl is identity)
- **Stuck**: `eval(transport [%x] |- P neutral value, env) = Value::Neutral(Eliminator::Transport(...))` (transport on neutral proof is stuck)

**Failure Modes**:
- `proof` does not synthesize to an `Eq` type
- `value` does not check against `P[x/%x]`
- Motive `P` is not a valid type family

**Design Note**: Transport is the **elimination form** for equality types. It allows converting a value of type `P[x/%x]` to type `P[y/%x]` given a proof of `Eq A x y`. This is the core mechanism for **proof-relevant type casting**.

---

## Hardware Types

The Core IR includes a **separate universe hierarchy** for hardware description, enabling type-safe hardware synthesis.

### Universe Hierarchy

**Syntax**: `SignalUniverse`, `HardwareUniverse`, `ModuleUniverse`

**AST**: `Syntax::SignalUniverse`, `Syntax::HardwareUniverse`, `Syntax::ModuleUniverse`

**Typing Rules**: These universes are **not synthesizable**. They can only appear as expected types in checking mode.

**Design Note**: Hardware types live in a **separate universe hierarchy** from computational types. This prevents mixing hardware and software types inappropriately.

### Lift (^)

**Syntax**: `^A`

**AST**: `Syntax::LiftCode(RcSyntax)`

**Typing Rule** (CheckType):
```
Γ ⊢ A : Un
──────────────────────────
Γ ⊢ ^A : HardwareUniverse
```

**Evaluation**: `eval(^A, env) = Value::Lift(eval(A, env))` (canonical form)

**Design Note**: Lift converts a **computational type** `A` into a **hardware type** `^A`. This represents synthesizable hardware that computes values of type `A`.

### Hardware Arrow (->)

**Syntax**: `M -> N`

**AST**: `Syntax::HardwareArrow(RcSyntax, RcSyntax)`

**Typing Rule** (CheckType):
```
Γ ⊢ M : HardwareUniverse
Γ ⊢ N : HardwareUniverse
──────────────────────────
Γ ⊢ M -> N : ModuleUniverse
```

**Evaluation**: `eval(M -> N, env) = Value::HardwareArrow(eval(M, env), eval(N, env))` (canonical form)

**Design Note**: Hardware arrows represent **stateful hardware modules** (sequential circuits) that transform input hardware to output hardware. Unlike Pi types, hardware arrows are **non-dependent** (the output type does not depend on the input value).

### Module Abstraction (mod)

**Syntax**: `mod %x -> e`

**AST**: `Syntax::Module(Option<String>, RcSyntax)`

**Typing Rule** (Check):
```
Expected type: M -> N
Γ, %x : M ⊢ e ⇐ N
──────────────────────────
Γ ⊢ (mod %x -> e) ⇐ M -> N
```

**Evaluation**: `eval(mod %x -> e, env) = Value::Module(name, Closure(e, env))` (canonical form)

**Design Note**: Module abstractions are the **introduction form** for hardware arrows. They represent sequential circuits with state.

### Hardware Application (f&lt;T&gt;(x))

**Syntax**: `f<T>(x)`

**AST**: `Syntax::HApplication(RcSyntax, RcSyntax, RcSyntax)`

**Typing Rule** (Synth):
```
Γ ⊢ f ⇒ M -> N
Γ ⊢ x ⇐ M
────────────────────────
Γ ⊢ f<T>(x) ⇒ N
```

**Evaluation**:
- **Beta reduction**: `eval((mod %x -> e)<T>(v), env) = eval(e, env ++ [v])`
- **Neutral**: `eval(neutral<T>(v), env) = Value::Neutral(Eliminator::HApp(neutral, T, v))`

**Design Note**: Hardware application is the **elimination form** for hardware arrows. The `<T>` syntax allows explicit type arguments for generic modules.

---

## Global Declarations

The Core IR supports three kinds of global declarations: **type constructors**, **constants**, and **primitives**.

### Type Constructor Declarations

**Syntax**: `tcon @Name (params: n) (indices: m) : Uu`

**Purpose**: Declare an inductive type family with parameters and indices.

**Example**:
```hwmlc,ignore
tcon @Vec (params: 1) (indices: 1) : U0
```

This declares a vector type `Vec A n` where `A` is a parameter (the element type) and `n` is an index (the length).

### Data Constructor Declarations

**Syntax**: `dcon @Name : TypeSignature`

**Purpose**: Declare a constructor for an inductive type.

**Example**:
```hwmlc,ignore
dcon @Nil : ∀(A : U0) -> #[@Vec A | @Zero]
dcon @Cons : ∀(A : U0) -> ∀(n : @Nat) -> A -> #[@Vec A | n] -> #[@Vec A | @Succ n]
```

### Constant Declarations

**Syntax**: `const @Name : Type := value`

**Purpose**: Declare a global definition with a type and value.

**Example**:
```hwmlc,ignore
const @identity : ∀(A : U0) -> A -> A := \A -> \x -> x
```

### Primitive Declarations

**Syntax**: `prim @Name : Type`

**Purpose**: Declare an external primitive with a type but no definition.

**Example**:
```hwmlc,ignore
prim @Bit : SignalUniverse
```

---

## Design Rationale

### Why Bidirectional Typechecking?

Bidirectional typechecking separates **synthesis** (type inference) from **checking** (type validation). This makes the type system more predictable and easier to implement. Lambdas and case expressions can only be checked, not synthesized, which avoids complex type inference algorithms.

### Why De Bruijn Indices?

De Bruijn indices eliminate alpha-equivalence issues (renaming bound variables). This simplifies substitution, conversion checking, and normalization. The downside is that indices are less readable than names, but the Core IR is not meant to be written by hand.

### Why Constructor-Only Patterns?

Constructor-only patterns (no wildcards or nested patterns) simplify the type system and make exhaustiveness checking trivial. Wildcards and nested patterns can be desugared in the surface language.

### Why Separate Hardware Universes?

Separating hardware types from computational types prevents mixing synthesizable and non-synthesizable code. This ensures that hardware modules can be compiled to Verilog without runtime dependencies.

### Why Propositional Equality?

Propositional equality (proof-relevant) allows reasoning about equality at the type level. This enables dependent types to express invariants like "this vector has length n" or "this circuit has width w". Definitional equality (conversion checking) is used for type checking, while propositional equality is used for proofs.

