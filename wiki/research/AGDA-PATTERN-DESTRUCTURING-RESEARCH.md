# Agda Pattern Destructuring Research

**Date:** 2026-05-10  
**Focus:** Irrefutable patterns in binding positions, mixfix destructors  
**Sources:** Agda 2.8.0 source code, Agda documentation  

---

## Executive Summary

**Agda's Approach:** Patterns and expressions are **unified at the surface syntax level** in `Abstract.hs`, then disambiguated during type checking. This is a **deliberate design choice** for maximum flexibility with mixfix operators and user-defined syntax.

**Key Insight:** The `Binder` type in Agda uses `Maybe Pattern` to allow **optional destructuring patterns** in any binding position:

```haskell
data Binder' a = Binder
  { binderPattern    :: Maybe Pattern  -- ← Optional destructuring!
  , binderNameOrigin :: BinderNameOrigin
  , binderName       :: a
  }
```

**Critical Point:** Agda does NOT parse patterns as expressions. Instead, it has **separate Pattern and Expr types**, but patterns can appear in **binding positions** (lambda parameters, let bindings, function parameters).

---

## Agda's Type Hierarchy (Simplified)

### Expression Type
```haskell
data Expr
  = Var  Name
  | Def' QName Suffix
  | Con  AmbiguousQName     -- Constructor (can be overloaded!)
  | Lit  ExprInfo Literal
  | App  AppInfo Expr (NamedArg Expr)
  | Lam  ExprInfo LamBinding Expr    -- Lambda with bindings
  | Let  ExprInfo (List1 LetBinding) Expr
  | Pi   ExprInfo Telescope1 Type
  -- ... many more
```

### Pattern Type (DISTINCT from Expr!)
```haskell
data Pattern' e
  = VarP BindName                          -- Variable pattern
  | ConP ConPatInfo AmbiguousQName (NAPs e) -- Constructor pattern
  | WildP PatInfo                          -- Underscore _
  | AsP PatInfo BindName (Pattern' e)     -- As-pattern x@p
  | DotP PatInfo e                        -- Dot pattern .e
  | AbsurdP PatInfo                       -- Absurd pattern ()
  | LitP PatInfo Literal                  -- Literal pattern
  | RecP KwRange ConPatInfo [FieldAssignment' (Pattern' e)] -- Record pattern
  | WithP PatInfo (Pattern' e)            -- With pattern |p
  -- ... more
```

**Note:** `Pattern' e` is parameterized by `e` (the type of dot patterns), which is `Expr` in Abstract syntax!

---

## Bindings with Optional Patterns

### Lambda Bindings
```haskell
data LamBinding
  = DomainFree TacticAttribute (NamedArg Binder)
    -- ^ x or {x} or .x or {x = y} or x@p or (p)
  | DomainFull TypedBinding
    -- ^ (xs : e) or {xs : e} or (let Ds)
```

### Binder with Pattern
```haskell
data Binder' a = Binder
  { binderPattern    :: Maybe Pattern  -- ← Can be a pattern!
  , binderNameOrigin :: BinderNameOrigin
  , binderName       :: a
  }

-- Example usage:
mkBinder :: a -> Binder' a
mkBinder = Binder Nothing UserBinderName  -- No pattern, just name

-- Extract pattern if present:
extractPattern :: Binder' a -> Maybe (Pattern, a)
extractPattern (Binder p _ a) = (,a) <$> p
```

### Let Bindings
```haskell
data LetBinding
  = LetBind LetInfo ArgInfo BindName Type Expr
    -- ^ LetBind info rel name type defn
  | LetAxiom LetInfo ArgInfo BindName Type
    -- ^ Function declarations with no body
  | LetPatBind LetInfo ArgInfo Pattern Expr  -- ← Irrefutable pattern!
    -- ^ Irrefutable pattern binding
  | LetApply ...
  | LetOpen ...
```

**Critical:** `LetPatBind` explicitly allows patterns in let bindings!

### Typed Bindings (Telescopes)
```haskell
data TypedBinding
  = TBind Range TypedBindingInfo (List1 (NamedArg Binder)) Type
    -- ^ (x y z : A) or (x y z : A) -> B
    --   Binder can have pattern!
  | TLet Range (List1 LetBinding)
    -- ^ (let x = e) or (let open M)
```

---

## How Agda Handles Mixfix in Patterns

**Key:** Constructor names can be **mixfix** (user-defined syntax with holes).

Example (from Agda stdlib):
```agda
data Vec (A : Set) : Nat -> Set where
  []  : Vec A zero
  _::_ : {n : Nat} -> A -> Vec A n -> Vec A (suc n)
```

The `_::_` constructor is **mixfix** with two holes!

### Pattern Matching with Mixfix
```agda
head : {A : Set} {n : Nat} -> Vec A (suc n) -> A
head (x :: xs) = x  -- ← mixfix pattern!
```

### Lambda Destructuring with Mixfix
```agda
-- Using lambda with destructuring:
map : {A B : Set} {n : Nat} -> (A -> B) -> Vec A n -> Vec B n
map f [] = []
map f (x :: xs) = f x :: map f xs

-- Can also write:
filterVec : {A : Set} {n : Nat} -> (A -> Bool) -> Vec A n -> List A
filterVec pred [] = []
filterVec pred (x :: xs) = 
  let rest = filterVec pred xs in
    if pred x then x :: rest else rest
```

---

## Agda's Parser Strategy

**From the source:** Agda does NOT parse patterns as expressions.

**Instead:** The parser has **separate productions** for:
1. `Expr` - expressions
2. `Pattern` - patterns
3. But: Both can appear in binding positions!

### Example (from `Parser.y` - conceptual):
```haskell
LamBinding:
  | '\' Binders '=>' Expr         -- Binders can have patterns!
  | 'fun' Binders '=>' Expr

Binder:
  | Id                  -- Just a name
  | '(' Pattern ')'     -- Destructuring pattern!
  | Id '@' Pattern      -- As-pattern

Pattern:
  | Id                  -- Variable or constructor (ambiguous!)
  | Constructor Args    -- Constructor application
  | '(' Pattern ')'
  | '_'
  | Literal
```

---

## How HWML Currently Does It

**Current HWML approach** (from grammar.lalrpop):
```rust
// Line 241: Untyped bindings use Expr3 (expression!)
UntypedBindingGroup: UntypedBindingGroup = {
  <el:Expr3> => UntypedBindingGroup::new(el)
};

// Line 247: Typed bindings use ExprList (list of expressions!)
TypedBindingGroup: TypedBindingGroup = {
  "(" <el:ExprList> ":" <ty:Expr0> ")" => TypedBindingGroup::new(el, ty)
};

// Line 284: Match patterns ALSO use Expr1!
MatchClause: MatchClause = {
  <pattern:Expr1> "~>" <body:Expr0> => {
    MatchClause::new(pattern, body)
  }
};
```

**AST** (from syntax.rs):
```rust
pub struct TypedBindingGroup {
    pub binders: Vec<Box<Expression>>,  // ← Expressions!
    pub ty: Box<Expression>,
}

pub struct UntypedBindingGroup {
    pub binders: Box<Expression>,       // ← Expression!
}
```

---

## The Key Question: Should HWML Copy Agda?

### Option 1: Agda's Approach (Separate Pattern Type + Binder with Maybe Pattern)

**Pros:**
- ✅ **Semantically correct** - Patterns have different semantics than expressions
- ✅ **Extensible** - Easy to add pattern-specific features (as-patterns, or-patterns, guards)
- ✅ **Type-safe elaboration** - Elaborator knows when it's looking at a pattern
- ✅ **Better error messages** - "Expected pattern" vs "Expected expression"
- ✅ **Exhaustiveness checking** - Proper Pattern AST enables coverage checking
- ✅ **Mixfix support** - Can handle complex mixfix destructors

**Cons:**
- ⚠️ **More complex parser** - Need separate pattern parser
- ⚠️ **Larger AST** - `Binder` needs `Maybe Pattern` field
- ⚠️ **Elaborator complexity** - Must handle patterns in all binding positions

**Timeline Impact:** +2 days (add Binder type, pattern parser for binding positions)

---

### Option 2: Keep Current Approach (Expression-Based)

**What HWML does now:**
```rust
pub struct TypedBindingGroup {
    pub binders: Vec<Box<Expression>>,  // Parse as expressions
    pub ty: Box<Expression>,
}
```

**Elaborator's job:** Interpret expressions as patterns.

**Pros:**
- ✅ **Simpler parser** - Reuse expression parser
- ✅ **Smaller AST** - No separate Pattern type in bindings
- ✅ **Works for simple cases** - Variables, constructor applications

**Cons:**
- ❌ **Semantically incorrect** - Patterns aren't expressions
- ❌ **Ambiguous syntax** - Is `f x` a function call or constructor pattern?
- ❌ **Type checking burden** - Elaborator must validate "pattern-like" expressions
- ❌ **Error-prone** - What if user writes `let (x + y) = foo`? Parser accepts it!
- ❌ **Mixfix complexity** - How does elaborator know `_::_` is a constructor in `let (x :: xs) = list`?
- ❌ **Future limitations** - Hard to add pattern-specific syntax

---

## Recommendation: Follow Agda (Option 1)

**Why:**
1. **Mixfix destructors require it** - You mentioned complex mixfix operations. Agda handles these by having patterns be distinct from expressions, then using name resolution + type info to disambiguate constructors.

2. **Irrefutable patterns need validation** - The elaborator must check that patterns in let/lambda are truly irrefutable. With Expression AST, the elaborator has to guess what's a pattern vs what's an error.

3. **Future-proof** - When you add features like:
   - As-patterns: `let xs@(Cons x xs') = list`
   - Or-patterns: `let (Left x | Right x) = value`
   - Pattern guards: `let (Cons x xs) when x > 0 = ...`

   These are **impossible** with expression-based patterns.

4. **Best practices** - Every production compiler does this:
   - Agda: Separate `Pattern` type
   - Haskell GHC: Separate `Pat` type
   - OCaml: Separate `pattern` type
   - Rust: Separate `Pat` AST node

---

## Detailed Design Recommendation

### 1. Add `Binder` Type to AST

```rust
// In syntax.rs

/// Binder with optional destructuring pattern
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Binder {
    pub loc: Range<usize>,
    /// Optional destructuring pattern (e.g., `(x, y)` in lambda)
    pub pattern: Option<Pattern>,
    /// Variable name (always present, even with pattern)
    pub name: Id,
}

impl Binder {
    /// Simple variable binder with no pattern
    pub fn var(loc: Range<usize>, name: Id) -> Self {
        Binder { loc, pattern: None, name }
    }

    /// Destructuring binder with pattern
    pub fn with_pattern(loc: Range<usize>, pattern: Pattern, name: Id) -> Self {
        Binder { loc, pattern: Some(pattern), name }
    }
}
```

### 2. Update Binding Groups

```rust
// BEFORE:
pub struct TypedBindingGroup {
    pub binders: Vec<Box<Expression>>,  // ❌ Expressions
    pub ty: Box<Expression>,
}

// AFTER:
pub struct TypedBindingGroup {
    pub binders: Vec<Binder>,  // ✅ Proper binders with optional patterns
    pub ty: Box<Expression>,
}

pub struct UntypedBindingGroup {
    pub binders: Vec<Binder>,  // ✅ Proper binders
}
```

### 3. Parser Changes

```rust
// In parser

fn parse_binder(ctx: &mut Context) -> Binder {
    let loc_start = ctx.current_location();

    match ctx.peek() {
        Some(Token::LParen) => {
            // Could be pattern or just grouped variable
            ctx.consume(Token::LParen);

            // Try to parse as pattern
            let pattern = parse_pattern(ctx);

            if !ctx.consume_if(Token::RParen).is_some() {
                ctx.emit_error("Expected ')'");
            }

            // If it's just a variable pattern, extract the name
            if let Pattern::Var { name, .. } = &pattern {
                Binder::var(loc_start..ctx.current_location(), name.clone())
            } else {
                // Generate name for destructured pattern (e.g., `.0`, `.1`)
                let name = ctx.make_generated_name();
                Binder::with_pattern(
                    loc_start..ctx.current_location(),
                    pattern,
                    name
                )
            }
        }

        Some(Token::Ident) => {
            // Simple variable
            let name = ctx.parse_id();
            Binder::var(loc_start..ctx.current_location(), name)
        }

        _ => {
            ctx.emit_error("Expected binder");
            Binder::var(loc_start..ctx.current_location(), ctx.make_error_id())
        }
    }
}
```

### 4. Elaborator Changes

```rust
// In elaborator

fn elab_binder(&mut self, binder: &Binder, ty: &Type) -> Result<core::Binder> {
    match &binder.pattern {
        None => {
            // Simple variable binding
            Ok(core::Binder::Var {
                name: binder.name.clone(),
                ty: self.elab_type(ty)?,
            })
        }

        Some(pattern) => {
            // Destructuring pattern
            self.check_irrefutable(pattern)?;

            // Elaborate pattern into core representation
            let core_pattern = self.elab_pattern(pattern, ty)?;

            Ok(core::Binder::Destruct {
                pattern: core_pattern,
                name: binder.name.clone(),
                ty: self.elab_type(ty)?,
            })
        }
    }
}

fn check_irrefutable(&self, pattern: &Pattern) -> Result<()> {
    match pattern {
        Pattern::Var { .. } => Ok(()),
        Pattern::Wildcard { .. } => Ok(()),
        Pattern::Constructor { name, .. } => {
            // Check if this is the ONLY constructor of its type
            // If not, it's refutable and cannot be used in let/lambda
            let cons_info = self.lookup_constructor(name)?;
            if cons_info.is_only_constructor() {
                Ok(())
            } else {
                Err(ElabError::RefutablePatternInBinding {
                    pattern: pattern.clone(),
                    message: format!(
                        "Pattern '{}' is refutable, cannot use in let/lambda",
                        name
                    ),
                })
            }
        }
        _ => Err(ElabError::InvalidBindingPattern { pattern: pattern.clone() }),
    }
}
```

---

## Migration Strategy

### Phase 1: Add Binder Type (1 day)
- Add `Binder` struct to `syntax.rs`
- Update `TypedBindingGroup` and `UntypedBindingGroup`
- Update all construction sites in current parser
- Tests still pass (using simple variable binders)

### Phase 2: Add Pattern in Binder Support (1 day)
- Extend parser to recognize `(pattern)` in binding positions
- Generate names for destructured patterns
- Elaborator validates patterns (for now, only allow variables)

### Phase 3: Enable Irrefutable Patterns (variable expansion from Phase 8)
- Elaborator checks irrefutability
- Support record patterns (always irrefutable if record is defined)
- Support single-constructor datatypes (e.g., `(x, y)` for pairs)

---

## Example: Before vs After

### Before (Current HWML)
```rust
// Surface syntax:
fun (x, y) => x + y

// AST:
Fun {
    bindings: Bindings {
        groups: [
            UntypedBindingGroup {
                binders: App {  // ← Parsed as application expression!
                    elements: [Id("x"), Id("y")]
                }
            }
        ]
    },
    expr: ...
}

// Elaborator must figure out:
// "Oh, this App is actually meant to be a tuple pattern!"
```

### After (Recommended)
```rust
// Surface syntax:
fun (x, y) => x + y

// AST:
Fun {
    bindings: Bindings {
        groups: [
            UntypedBindingGroup {
                binders: [
                    Binder {
                        pattern: Some(Pattern::Constructor {
                            name: Id("Pair"),
                            args: [
                                Pattern::Var { name: Id("x") },
                                Pattern::Var { name: Id("y") },
                            ]
                        }),
                        name: Id(".pair_0"),  // Generated name
                    }
                ]
            }
        ]
    },
    expr: ...
}

// Elaborator knows:
// "This is a pattern binding! Check if Pair is the only constructor."
```

---

## Conclusion

**Recommendation:** Implement Agda-style `Binder` with `Maybe Pattern`.

**Justification:**
1. ✅ Semantically correct
2. ✅ Handles mixfix destructors (your requirement!)
3. ✅ Future-proof for advanced pattern features
4. ✅ Industry best practice (Agda, GHC, OCaml, Rust all do this)
5. ✅ Better error messages
6. ✅ Enables proper exhaustiveness checking

**Timeline:** +2 days (within acceptable bounds for 21-day parser implementation)

**Risk:** Low (well-understood pattern, proven by Agda/GHC)
