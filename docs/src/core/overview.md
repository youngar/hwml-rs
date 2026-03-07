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

- **Bound variables**: `%name` (user-provided names)
- **Unbound variables**: `!n` (De Bruijn levels, used in printer for unbound vars)
- **Constants**: `@Name` (user-defined) or `$Name` (primitives)
- **Type constructors**: `#[@Name args...]` (fully saturated instances)
- **Data constructors**: `[@Name args...]` (value construction)
- **Universe metavariable**: `Un` in typing rules represents an arbitrary universe level from the standard hierarchy (`U0`, `U1`, `U2`, ...)

### EBNF Grammar (Core Expressions)

```ebnf
expr ::= universe                          (* Un *)
       | variable                          (* %name or !n *)
       | constant                          (* @Name *)
       | primitive                         (* $Name *)
       | type_constructor                  (* #[@Name args...] *)
       | data_constructor                  (* [@Name args...] *)
       | pi                                (* ∀(%x : A) -> B or A -> B *)
       | lambda                            (* \%x -> e *)
       | application                       (* f x or f[x, y, z] *)
       | check                             (* (e : T) *)
       | eq_type                           (* Eq A x y *)
       | refl                              (* refl *)
       | transport                         (* transport [%x] |- P proof value *)
       | case                              (* e case { @C1 => e1 | @C2 %x => e2 } *)
       | lift                              (* ^ e *)
       | slift                             (* ^s e *)
       | mlift                             (* ^m e *)
       | harrow                            (* M -> N *)
       | module                            (* mod %x -> e *)
       | happlication                      (* f<T>(x) *)
       | bit                               (* Bit *)
       | zero                              (* 0 *)
       | one                               (* 1 *)

universe ::= "U" digit+                    (* U0, U1, U2, ... *)
           | "SignalUniverse"
           | "HardwareUniverse"
           | "ModuleUniverse"

variable ::= "%" identifier                (* bound: %x, %foo *)
           | "!" digit+                    (* unbound: !0, !1 *)

constant ::= "@" identifier                (* @Bool, @True *)
primitive ::= "$" identifier               (* $builtin *)

type_constructor ::= "#[" "@" identifier expr* "]"
data_constructor ::= "[" "@" identifier expr* "]"

pi ::= "∀" "(" "%" identifier ":" expr ")" "->" expr
     | expr "->" expr                      (* non-dependent *)

lambda ::= "\" "%" identifier "->" expr

application ::= expr expr                  (* left-associative *)
              | expr "[" expr ("," expr)* "]"

check ::= "(" expr ":" expr ")"

eq_type ::= "Eq" expr expr expr

transport ::= "transport" "[" "%" identifier "]" "|-" expr expr expr

case ::= expr "case" "{" branch ("|" branch)* "}"
branch ::= "@" identifier ("%" identifier)* "=>" expr
```

### AST Mapping

Each syntax node maps to a variant of `Syntax<'db>`:

| Syntax | AST Variant | Rust Struct |
|--------|-------------|-------------|
| `U0` | `Syntax::Universe(0)` | `Universe(u32)` |
| `%x` | `Syntax::Variable(var)` | `Variable { index, name }` |
| `@Name` | `Syntax::Constant(id)` | `ConstantId<'db>` |
| `#[@Name a b]` | `Syntax::TypeConstructor(id, args)` | `(ConstantId<'db>, Vec<RcSyntax<'db>>)` |
| `[@Name a b]` | `Syntax::DataConstructor(id, args)` | `(ConstantId<'db>, Vec<RcSyntax<'db>>)` |
| `∀(%x : A) -> B` | `Syntax::Pi(name, dom, cod)` | `(Option<String>, RcSyntax, RcSyntax)` |
| `\%x -> e` | `Syntax::Lambda(name, body)` | `(Option<String>, RcSyntax)` |
| `f x` | `Syntax::Application(f, x)` | `(RcSyntax, RcSyntax)` |
| `(e : T)` | `Syntax::Check(e, T)` | `(RcSyntax, RcSyntax)` |
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

**Evaluation**: `eval(Un) = Value::Universe(n)` (canonical form)

**Example**:
```hwmlc
const @U0Value : U1 = U0;
```

### Variables

**Syntax**: `%name` (bound), `!n` (unbound in printer output)

**AST**: `Syntax::Variable(Variable { index, name })`

**Typing Rule** (Synth):
```
Γ(i) = T
─────────────────
Γ ⊢ %i ⇒ T
```

**Evaluation**: `eval(%i, env) = env[i]` (lookup in environment)

**Context Invariant**: Variables use De Bruijn **indices** (0 = innermost binder). The printer converts to De Bruijn **levels** for unbound variables.

**Example**:
```hwmlc
const @Identity : ∀(%A : U0) -> ∀(%x : %A) -> %A = \%A -> \%x -> %x;
```

### Constants

**Syntax**: `@Name`

**AST**: `Syntax::Constant(ConstantId<'db>)`

**Typing Rule** (Synth):
```
GlobalEnv(@Name) = (type: T, value: v)
──────────────────────────────────────
Γ ⊢ @Name ⇒ T
```

**Evaluation**: `eval(@Name, globals) = eval(globals[@Name].value, [])`

**Design Note**: Constants are **transparent** (unfold during conversion checking). The global environment stores both the type and the defining expression as `RcSyntax<'db>`, evaluated on-demand.

**Example**:
```hwmlc
tcon @Bool : -> U0 where
    dcon @True : #[@Bool]
    dcon @False : #[@Bool]
;

const @Not : ∀(%b : #[@Bool]) -> #[@Bool] = \%b -> %b case { @True => [@False] | @False => [@True] };
```

### Type Constructors

**Syntax**: `#[@Name arg1 arg2 ...]`

**AST**: `Syntax::TypeConstructor(ConstantId<'db>, Vec<RcSyntax<'db>>)`

**Typing Rule** (Synth):
```
GlobalEnv(@Name) = TypeConstructorInfo { params, indices, universe }
Γ ⊢ a1 ⇐ P1    ...    Γ ⊢ an ⇐ Pn    (params)
Γ ⊢ i1 ⇐ I1    ...    Γ ⊢ im ⇐ Im    (indices)
────────────────────────────────────────────────
Γ ⊢ #[@Name a1 ... an i1 ... im] ⇒ universe
```

**Evaluation**: `eval(#[@Name args], env) = Value::TypeConstructor(id, eval_args)`

**Design Note**: Type constructors must be **fully saturated** (all parameters and indices provided). Partial application is not supported.

**Example**:
```hwmlc
tcon @Nat : -> U0 where
    dcon @Zero : #[@Nat]
    dcon @Succ (%n : #[@Nat]) : #[@Nat]
;

const @NatType : U1 = #[@Nat];
```

### Data Constructors

**Syntax**: `[@Name arg1 arg2 ...]`

**AST**: `Syntax::DataConstructor(ConstantId<'db>, Vec<RcSyntax<'db>>)`

**Typing Rule** (Check):
```
Expected type: #[@T params... indices...]
GlobalEnv(@Name) = DataConstructorInfo { type_constructor: @T, arguments: [A1, ..., An], result_type }
Γ ⊢ a1 ⇐ A1    ...    Γ ⊢ an ⇐ An
Γ ⊢ result_type ≡ #[@T params... indices...]
────────────────────────────────────────────────
Γ ⊢ [@Name a1 ... an] ⇐ #[@T params... indices...]
```

**Evaluation**: `eval([@Name args], env) = Value::Data(id, eval_args)` (canonical form)

**Design Note**: Data constructors are **canonical values** (do not reduce further). They are the introduction forms for inductive types.

**Example**:
```hwmlc
tcon @Nat : -> U0 where
    dcon @Zero : #[@Nat]
    dcon @Succ (%n : #[@Nat]) : #[@Nat]
;

const @Three : #[@Nat] = [@Succ [@Succ [@Succ [@Zero]]]];
```

### Pi Types (Dependent Functions)

**Syntax**: `∀(%x : A) -> B` (dependent) or `A -> B` (non-dependent)

**AST**: `Syntax::Pi(Option<String>, RcSyntax, RcSyntax)`

**Typing Rule** (Check):
```
Expected type: Un
Γ ⊢ A : type
Γ, %x : A ⊢ B ⇐ Un
─────────────────────────
Γ ⊢ (∀(%x : A) -> B) ⇐ Un
```

**Evaluation**: `eval(∀(%x : A) -> B, env) = Value::Pi(name, eval(A, env), Closure(B, env))`

**Design Note**: The codomain `B` is stored as a **closure** (unevaluated syntax + environment) to support dependency on `%x`.

**Example**:
```hwmlc
const @Identity : ∀(%A : U0) -> ∀(%x : %A) -> %A = \%A -> \%x -> %x;
const @Const : ∀(%A : U0) -> ∀(%B : U0) -> ∀(%x : %A) -> ∀(%y : %B) -> %A = \%A -> \%B -> \%x -> \%y -> %x;
```

### Lambda Abstractions

**Syntax**: `\%x -> e`

**AST**: `Syntax::Lambda(Option<String>, RcSyntax)`

**Typing Rule** (Check):
```
Expected type: ∀(%x : A) -> B
Γ, %x : A ⊢ e ⇐ B
──────────────────────
Γ ⊢ (\%x -> e) ⇐ ∀(%x : A) -> B
```

**Evaluation**: `eval(\%x -> e, env) = Value::Lambda(name, Closure(e, env))` (canonical form)

**Failure Mode**: Checking a lambda against a non-Pi type fails with a type error.

**Design Note**: Lambdas are **canonical values** (introduction forms for Pi types). They do not synthesize types; they must be checked against a known Pi type.

**Example**:
```hwmlc
const @Double : ∀(%A : U0) -> ∀(%f : ∀(%x : %A) -> %A) -> ∀(%x : %A) -> %A =
    \%A -> \%f -> \%x -> %f[%f[%x]];
```

### Application

**Syntax**: `f x` (juxtaposition, left-associative) or `f[x, y, z]` (bracket notation)

**AST**: `Syntax::Application(RcSyntax, RcSyntax)` (bracket notation desugars to nested applications)

**Typing Rule** (Synth):
```
Γ ⊢ f ⇒ ∀(%x : A) -> B
Γ ⊢ arg ⇐ A
────────────────────────
Γ ⊢ f arg ⇒ B[arg/%x]
```

**Evaluation**:
- **Beta reduction**: `eval((\%x -> e) v, env) = eval(e, env ++ [v])`
- **Neutral**: `eval(neutral v, env) = Value::Neutral(Eliminator::App(neutral, v))`

**Design Note**: Application performs **beta reduction** when the function is a lambda. When the function is a neutral term (variable, constant application, etc.), the application becomes part of the neutral's **spine**.

**Example**:
```hwmlc
const @Apply : ∀(%A : U0) -> ∀(%B : U0) -> ∀(%f : ∀(%x : %A) -> %B) -> ∀(%x : %A) -> %B =
    \%A -> \%B -> \%f -> \%x -> %f[%x];
```

### Type Annotations (Check)

**Syntax**: `(e : T)`

**AST**: `Syntax::Check(RcSyntax, RcSyntax)`

**Typing Rule** (Synth):
```
Γ ⊢ T : Un
Γ ⊢ e ⇐ T
──────────────
Γ ⊢ (e : T) ⇒ T
```

**Evaluation**: `eval((e : T), env) = eval(e, env)` (annotation is erased)

**Design Note**: Check nodes allow switching from Synth mode to Check mode. They are the primary mechanism for providing type information when the typechecker cannot infer it.

**Example**:
```hwmlc
const @Annotated : U1 = (U0 : U1);
```

### Case Expressions (Pattern Matching)

**Syntax**: `scrutinee case { @C1 => e1 | @C2 %x %y => e2 | ... }`

**AST**: `Syntax::Case { scrutinee, branches, return_type }`

**Typing Rule** (Check):
```
scrutinee must be a variable: Γ(scrutinee) = #[@T params... indices...]
GlobalEnv(@T) = TypeConstructorInfo { constructors: [@C1, ..., @Cn] }
For each branch @Ci %x1 ... %xk => ei:
    Γ, %x1 : A1, ..., %xk : Ak ⊢ ei ⇐ expected_type
All constructors covered (exhaustiveness)
────────────────────────────────────────────────
Γ ⊢ (scrutinee case { branches }) ⇐ expected_type
```

**Evaluation**:
- **Canonical scrutinee**: `eval(([@C args] case { @C %xs => e | ... }), env) = eval(e, env ++ args)`
- **Neutral scrutinee**: `eval((neutral case { ... }), env) = Value::Neutral(Eliminator::Case(neutral, branches))`

**Failure Modes**:
- Non-exhaustive patterns (missing constructor)
- Redundant patterns (duplicate constructor)
- Scrutinee does not synthesize to a type constructor

**Design Note**: Case expressions use **constructor-only patterns** (no variable patterns, no wildcards). This simplifies exhaustiveness checking and ensures that case trees are **decision trees** (not general pattern matching).

**Example**:
```hwmlc
tcon @Bool : -> U0 where
    dcon @True : #[@Bool]
    dcon @False : #[@Bool]
;

const @Not : ∀(%b : #[@Bool]) -> #[@Bool] =
    \%b -> %b case { @True => [@False] | @False => [@True] };
```

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

**Example**:
```hwmlc
tcon @Bool : -> U0 where
    dcon @True : #[@Bool]
    dcon @False : #[@Bool]
;

const @TrueEqTrue : Eq #[@Bool] [@True] [@True] = refl;
const @BoolEqType : U1 = Eq U0 #[@Bool] #[@Bool];
```

### Reflexivity (refl)

**Syntax**: `refl`

**AST**: `Syntax::Refl`

**Typing Rule** (Check):
```
Expected type: Eq A x y
Γ ⊢ x ≡ y : A    (definitional equality)
──────────────────────────────────────
Γ ⊢ refl ⇐ Eq A x y
```

**Evaluation**: `eval(refl, env) = Value::Refl` (canonical form)

**Failure Mode**: `refl` can only prove `Eq A x y` when `x` and `y` are **definitionally equal** (i.e., they normalize to the same value). If `x` and `y` are not convertible, typechecking fails.

**Design Note**: This is the **reflection principle**: definitional equality implies propositional equality. The converse (propositional equality implies definitional equality) does not hold in general.

**Example**:
```hwmlc
const @ReflExample : Eq U1 U0 U0 = refl;
```

### Transport

**Syntax**: `transport [%x] |- P proof value`

**AST**: `Syntax::Transport(Option<String>, RcSyntax, RcSyntax, RcSyntax)`

**Typing Rule** (Synth):
```
Γ ⊢ proof ⇒ Eq A x y
Γ, %x : A ⊢ P : Un    (motive)
Γ ⊢ value ⇐ P[x/%x]
────────────────────────────────
Γ ⊢ transport [%x] |- P proof value ⇒ P[y/%x]
```

**Evaluation**:
- **With refl**: `eval(transport [%x] |- P refl value, env) = eval(value, env)` (transport along refl is identity)
- **Stuck**: `eval(transport [%x] |- P neutral value, env) = Value::Neutral(Eliminator::Transport(...))` (transport on neutral proof is stuck)

**Failure Modes**:
- `proof` does not synthesize to an `Eq` type
- `value` does not check against `P[x/%x]`
- Motive `P` is not a valid type family

**Design Note**: Transport is the **elimination form** for equality types. It allows converting a value of type `P[x/%x]` to type `P[y/%x]` given a proof of `Eq A x y`. This is the core mechanism for **proof-relevant type casting**.

**Why Transport Instead of Pattern Matching?** Dependent pattern matching on equality would require the **K axiom** (uniqueness of identity proofs), which is incompatible with Homotopy Type Theory and makes the theory less extensional. Transport is more general and does not assume K.

**Example**:
```hwmlc
const @Symm : ∀(%A : U0) -> ∀(%x : %A) -> ∀(%y : %A) -> ∀(%p : Eq %A %x %y) -> Eq %A %y %x =
    \%A -> \%x -> \%y -> \%p -> transport [%z] |- Eq %A %z %x %p refl;
```

---

## Hardware Types

The Core IR includes a **separate universe hierarchy** for hardware description, enabling type-safe hardware synthesis.

### Universe Hierarchy

**Syntax**: `SignalUniverse`, `HardwareUniverse`, `ModuleUniverse`

**AST**: `Syntax::SignalUniverse`, `Syntax::HardwareUniverse`, `Syntax::ModuleUniverse`

**Typing Rules**: These universes are **not synthesizable**. They can only appear as expected types in checking mode.

**Design Note**: Hardware universes are **separate** from the standard universe hierarchy. This prevents accidental mixing of software types and hardware types. Unlike `U0`, `U1`, etc., these universes cannot be synthesized - they can only be used as expected types when checking that a term is a valid signal type, hardware type, or module type.

### Hardware Lift (^)

**Syntax**: `^ ht`

**AST**: `Syntax::Lift(RcSyntax)`

**Typing Rule** (Synth):
```
Γ ⊢ ht : HardwareUniverse
──────────────────────────
Γ ⊢ ^ ht ⇒ U0
```

**Evaluation**: `eval(^ ht, env) = Value::Lift(eval(ht, env))`

**Design Note**: Hardware lift `^` is the **only synthesizable** hardware construct. It converts a **hardware type** into a **meta-level type** (living in `U0`), allowing hardware types to be used in dependent types. This is the bridge from the hardware world back to the software world.

### Signal Lift (^s)

**Syntax**: `^s A`

**AST**: `Syntax::SLift(RcSyntax)`

**Typing Rule** (Check):
```
Expected type: HardwareUniverse
Γ ⊢ A : SignalUniverse
──────────────────────────
Γ ⊢ ^s A ⇐ HardwareUniverse
```

**Semantics**: If `A : SignalUniverse`, then `^s A : HardwareUniverse` (a hardware type that is a signal).

**Evaluation**: `eval(^s A, env) = Value::SLift(eval(A, env))`

**Design Note**: Signal lift converts a **signal type** into a **hardware type** (a combinational circuit producing that signal). This represents **stateless** hardware.

### Module Lift (^m)

**Syntax**: `^m A`

**AST**: `Syntax::MLift(RcSyntax)`

**Typing Rule** (Check):
```
Expected type: HardwareUniverse
Γ ⊢ A : ModuleUniverse
──────────────────────────
Γ ⊢ ^m A ⇐ HardwareUniverse
```

**Semantics**: If `A : ModuleUniverse`, then `^m A : HardwareUniverse` (a hardware type that is a module).

**Evaluation**: `eval(^m A, env) = Value::MLift(eval(A, env))`

**Design Note**: Module lift converts a **module type** into a **hardware type** (a hardware module). This enables **generic hardware** (e.g., parameterized by bit width).

### Bit Type

**Syntax**: `Bit`

**AST**: `Syntax::Bit`

**Typing Rule** (Check):
```
Expected type: SignalUniverse
──────────────────────────
Γ ⊢ Bit ⇐ SignalUniverse
```

**Evaluation**: `eval(Bit, env) = Value::Bit` (canonical form)

**Design Note**: `Bit` is the **primitive signal type** representing a single wire. It is the foundation of all hardware types.

### Bit Literals (0, 1)

**Syntax**: `0`, `1`

**AST**: `Syntax::Zero`, `Syntax::One`

**Typing Rule** (Check):
```
Expected type: ^ (^s Bit)
──────────────────────────
Γ ⊢ 0 ⇐ ^ (^s Bit)

Expected type: ^ (^s Bit)
──────────────────────────
Γ ⊢ 1 ⇐ ^ (^s Bit)
```

**Evaluation**: `eval(0, env) = Value::Zero`, `eval(1, env) = Value::One` (canonical forms)

**Design Note**: Bit literals are **hardware constants** (combinational circuits producing constant signals). They have type `^ (^s Bit)` (hardware producing a bit signal), not `Bit` (signal type).

**Example**:
```hwmlc
const @BitZero : ^ (^s Bit) = 0;
const @BitOne : ^ (^s Bit) = 1;
```

### Hardware Arrow (M -> N)

**Syntax**: `M -> N`

**AST**: `Syntax::HArrow(RcSyntax, RcSyntax)`

**Typing Rule** (Check):
```
Expected type: ModuleUniverse
Γ ⊢ M : HardwareUniverse
Γ ⊢ N : HardwareUniverse
──────────────────────────
Γ ⊢ M -> N ⇐ ModuleUniverse
```

**Evaluation**: `eval(M -> N, env) = Value::HArrow(eval(M, env), eval(N, env))`

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

### Hardware Application (f<T>(x))

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

Implementation: `crates/hwml-core/src/declaration.rs`, `crates/hwml-core/src/check_module.rs`

### Type Constructor Declarations

**Syntax**:
```
tcon @Name (%p1 : T1) ... : (%i1 : I1) ... -> Universe where
    dcon @Constructor1 (%a1 : A1) ... : ResultType
    dcon @Constructor2 (%b1 : B1) ... : ResultType
    ...
;
```

**AST**: `Declaration::TypeConstructor { name, parameters, indices, universe, constructors }`

**Semantics**:
1. **Parameters** (`%p1 : T1, ...`) are **uniform** across all values of the type (e.g., the element type of a list).
2. **Indices** (`%i1 : I1, ...`) **vary** per constructor (e.g., the length of a vector).
3. **Universe** specifies which universe the type lives in (e.g., `U0`, `U1`).
4. **Data constructors** are the introduction forms for the type.

**Validation** (Two-Phase):
- **Phase 1**: Add type constructor signature to global environment (name, parameters, indices, universe).
- **Phase 2**: Validate each data constructor's type against the type constructor signature.

**Design Note**: The distinction between parameters and indices is crucial for **efficient compilation**. Parameters are erased at runtime, while indices may affect runtime representation.

**Example**:
```hwmlc
tcon @Nat : -> U0 where
    dcon @Zero : #[@Nat]
    dcon @Succ (%n : #[@Nat]) : #[@Nat]
;

tcon @List (%A : U0) : -> U0 where
    dcon @Nil : #[@List %A]
    dcon @Cons (%x : %A) (%xs : #[@List %A]) : #[@List %A]
;

tcon @Vec (%A : U0) : (%n : #[@Nat]) -> U0 where
    dcon @VNil : #[@Vec %A [@Zero]]
    dcon @VCons (%n : #[@Nat]) (%x : %A) (%xs : #[@Vec %A %n]) : #[@Vec %A [@Succ %n]]
;
```

### Constant Declarations

**Syntax**:
```
const @Name : Type = value;
```

**AST**: `Declaration::Constant { name, ty, value }`

**Semantics**:
1. **Type** is the declared type of the constant.
2. **Value** is the defining expression (stored as `RcSyntax<'db>`).
3. Constants are **transparent** (unfold during conversion checking).

**Validation** (Two-Phase):
- **Phase 1**: Add constant signature to global environment (name, type).
- **Phase 2**: Typecheck `value` against `type`.

**Design Note**: Constants are **lazy** (the value is stored as syntax, not evaluated until needed). This enables mutual recursion and avoids evaluation order issues.

**Example**:
```hwmlc
const @Identity : ∀(%A : U0) -> ∀(%x : %A) -> %A = \%A -> \%x -> %x;
```

### Primitive Declarations

**Syntax**:
```
prim $Name : Type;
```

**AST**: `Declaration::Primitive { name, ty }`

**Semantics**:
1. **Type** is the declared type of the primitive.
2. **No value** is provided (primitives are axioms).
3. Primitives are **opaque** (do not unfold during conversion checking).

**Validation**: Typecheck the type signature (no value to validate).

**Design Note**: Primitives are used for **built-in operations** that cannot be defined in the Core IR (e.g., hardware primitives, external functions). They are **stuck** during evaluation (become neutral terms).



---

## Evaluation Semantics

The Core IR uses **Normalization by Evaluation (NbE)** for conversion checking and evaluation.

Implementation: `crates/hwml-core/src/eval.rs`, `crates/hwml-core/src/quote.rs`

### Semantic Domain

Expressions evaluate to **values** (`Value<'db>`):

- **Canonical forms**: `Value::Universe`, `Value::Lambda`, `Value::Module`, `Value::Data`, `Value::Refl`, `Value::Zero`, `Value::One`, `Value::Bit`
- **Type formers**: `Value::Pi`, `Value::Eq`, `Value::TypeConstructor`, `Value::HArrow`, `Value::Lift`, `Value::SLift`, `Value::MLift`
- **Neutral terms**: `Value::Neutral(Flex | Rigid, Eliminator)`

### Canonical vs. Neutral

- **Canonical values** are **fully evaluated** (e.g., `[@True]`, `\%x -> e`, `refl`).
- **Neutral values** are **stuck** on a variable, constant, or primitive (e.g., `%x`, `$prim`, `%x case { ... }`).

### Neutral Terms (Spine Representation)

Neutral terms use a **spine representation**:
- **Head**: `Flex(MetaVariable)` or `Rigid(Variable | Constant | Primitive)`
- **Spine**: Sequence of eliminators (`App`, `Case`, `Transport`, `HApp`)

**Example**: `%f %x %y case { @C => e }` evaluates to:
```
Neutral(Rigid(Variable(f)), [App(x), App(y), Case(...)])
```

### Normalization by Evaluation (NbE)

**Algorithm**:
1. **Evaluate** syntax to semantic values (`eval : Syntax -> Env -> Value`)
2. **Quote** values back to normal forms (`quote : Value -> Level -> Syntax`)

**Conversion Checking**: `x ≡ y` iff `quote(eval(x)) == quote(eval(y))`

**Design Note**: NbE is **more efficient** than syntactic reduction because it performs beta-reduction during evaluation (no need to traverse syntax repeatedly). It also handles **eta-expansion** automatically during quoting.

### Closures

Dependent types require **closures** to represent unevaluated bodies:
- `Value::Pi(name, domain, Closure(body, env))`
- `Value::Lambda(name, Closure(body, env))`

**Closure Application**: `apply_closure(Closure(body, env), arg) = eval(body, env ++ [arg])`

### Stuck vs. Error

- **Stuck**: Evaluation cannot proceed due to a neutral term (e.g., `%x case { ... }`). This is **valid** (the term is well-typed but not fully reducible).
- **Error**: Evaluation encounters an invalid operation (e.g., applying a non-function). This is a **bug** (the term should have been rejected by the typechecker).

**Design Note**: The evaluator **panics** on errors (because they indicate typechecker bugs). Stuck terms are represented as `Value::Neutral`.

---

## Design Rationale

### Why Transport Instead of Dependent Pattern Matching?

**Problem**: Dependent pattern matching on equality types requires the **K axiom** (uniqueness of identity proofs):
```
K : ∀(A : Type) -> ∀(x : A) -> ∀(p : Eq A x x) -> Eq (Eq A x x) p refl
```

**Issue**: K is **incompatible** with:
- **Homotopy Type Theory** (HoTT), where equality types represent paths in spaces
- **Univalence**, where equivalent types can be equal
- **Proof irrelevance**, where all proofs of the same proposition are equal

**Solution**: Use `transport` as the **primitive eliminator** for equality. Transport does not assume K and is compatible with HoTT.

**Trade-off**: Transport is less convenient than pattern matching, but it is more general and does not commit to a specific equality theory.

### Why Constructor-Only Patterns?

**Problem**: General pattern matching with variable patterns and wildcards requires:
- **Overlapping pattern detection** (which pattern matches first?)
- **Redundancy checking** (are some patterns unreachable?)
- **Coverage checking** (are all cases handled?)

**Solution**: Restrict patterns to **constructors only** (no variables, no wildcards). This makes exhaustiveness checking **trivial** (just check that all constructors are covered).

**Trade-off**: Less expressive patterns, but **simpler implementation** and **clearer semantics**.

### Why Two-Phase Module Checking?

**Problem**: Mutual recursion requires that all declarations are available before validation.

**Solution**: **Phase 1** adds all signatures to the global environment. **Phase 2** validates all bodies.

**Trade-off**: Requires storing types and values as `RcSyntax<'db>` (lazy evaluation), but enables **full mutual recursion** without topological sorting.

### Why Separate Hardware Universes?

**Problem**: Mixing software types and hardware types can lead to **unsound compilation**:
- Software functions cannot be synthesized to hardware
- Hardware modules cannot be executed as software

**Solution**: Use **separate universe hierarchies** (`U0, U1, ...` for software, `SignalUniverse, HardwareUniverse, ModuleUniverse` for hardware). The type system **prevents** mixing.

**Trade-off**: More complex type system, but **guaranteed soundness** for hardware synthesis.

### Why Lazy Evaluation for Constants?

**Problem**: Eager evaluation of constants can cause:
- **Evaluation order issues** (which constant is evaluated first?)
- **Infinite loops** (recursive constants never terminate)
- **Memory bloat** (large constants are evaluated even if unused)

**Solution**: Store constant values as `RcSyntax<'db>` and evaluate **on-demand** during typechecking or conversion checking.

**Trade-off**: Requires re-evaluation if a constant is used multiple times, but enables **mutual recursion** and **lazy semantics**.

---

## Examples

### Simple Inductive Type
```hwmlc
tcon @Bool : -> U0 where
    dcon @True : #[@Bool]
    dcon @False : #[@Bool]
;

const @Not : ∀(%b : #[@Bool]) -> #[@Bool] = \%b -> %b case { @True => [@False] | @False => [@True] };
const @And : ∀(%x : #[@Bool]) -> ∀(%y : #[@Bool]) -> #[@Bool] =
    \%x -> \%y -> %x case { @True => %y | @False => [@False] };
```

### Parameterized Type
```hwmlc
tcon @List (%A : U0) : -> U0 where
    dcon @Nil : #[@List %A]
    dcon @Cons (%x : %A) (%xs : #[@List %A]) : #[@List %A]
;
```





### Propositional Equality
```hwmlc
const @Symm : ∀(%A : U0) -> ∀(%x : %A) -> ∀(%y : %A) -> ∀(%p : Eq %A %x %y) -> Eq %A %y %x =
    \%A -> \%x -> \%y -> \%p -> transport [%z] |- Eq %A %z %x %p refl;

const @Trans : ∀(%A : U0) -> ∀(%x : %A) -> ∀(%y : %A) -> ∀(%z : %A) ->
               ∀(%p : Eq %A %x %y) -> ∀(%q : Eq %A %y %z) -> Eq %A %x %z =
    \%A -> \%x -> \%y -> \%z -> \%p -> \%q -> transport [%w] |- Eq %A %x %w %q %p;
```

### Hardware Description
```hwmlc
const @BitZero : ^ (^s Bit) = 0;
const @BitOne : ^ (^s Bit) = 1;
```
