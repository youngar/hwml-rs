# Pattern vs Expression Disambiguation in Parsers

**Date:** 2026-05-10  
**Focus:** How parsers disambiguate patterns from expressions in binding positions  
**Key Question:** How do we parse `def foo (a * b : Pair)` - is `a * b` a pattern or expression?  

---

## Executive Summary

**The Problem:** In HWML's syntax, we have:
```rust
def foo (a * b : Pair) := ...  // Is `a * b` a pattern or expression?
fun (x :: xs) => ...           // Is `x :: xs` a pattern or expression?
let (a, b) = pair in ...       // Is `(a, b)` a pattern or expression?
```

**Critical Discovery:** Modern parsers use **THREE** main strategies:

1. **Haskell/GHC:** Parse ambiguous forms into a **GADT** that delays disambiguation
2. **Agda:** Parse into **separate Pattern/Expression types**, use **context** to decide
3. **OCaml:** Separate **pattern grammar** (no ambiguity at parse time)

**HWML's situation:** We use **type-directed elaboration** with **mixfix operators**, which changes everything!

---

## Strategy 1: Haskell's DisambECP (Context-Dependent Parsing)

### The Problem Haskell Faced

Haskell has syntax ambiguities where the parser **cannot tell** if something is a pattern or expression:

```haskell
-- Is this a pattern or expression?
f (a : b)      -- Could be cons pattern OR type annotation
f (Just x)     -- Could be constructor pattern OR function application
f (x + 1)      -- Could be... wait, this is ONLY valid as expression!
```

### Haskell's Solution: DisambECP GADT

**Key insight from GHC source:** Parse into an **abstract representation** that can be instantiated as **either** pattern **or** expression!

```haskell
-- From compiler/parser/RdrHsSyn.hs
class DisambECP b where
  -- Abstract operations for building parse trees
  mkHsVarPV      :: ... -> PV (Located b)
  mkHsAppPV      :: ... -> PV (Located b)
  mkHsParPV      :: ... -> PV (Located b)
  ...

instance DisambECP (HsExpr GhcPs) where ...  -- Instantiate as Expression
instance DisambECP (PatBuilder GhcPs) where ... -- Instantiate as Pattern
```

**How it works:**
1. Parser builds **abstract parse tree** using `DisambECP` operations
2. Grammar rules specify **context** (expect pattern vs expect expression)
3. At disambiguation point, **instantiate** the GADT to concrete type
4. **Validation** rejects invalid forms (e.g., `x + 1` in pattern position)

**Example:**
```haskell
-- Parser sees: (a : b)
-- Builds: mkHsParPV (mkHsVarPV "a" `mkHsAppPV` mkHsVarPV ":" `mkHsAppPV` mkHsVarPV "b")

-- In pattern context:
-- Instantiates to: ParPat (ConPat ":" [VarPat "a", VarPat "b"])  -- cons pattern

-- In expression context:
-- Instantiates to: HsPar (OpApp (HsVar "a") (HsVar ":") (HsVar "b"))  -- type annotation
```

### Where Disambiguation Happens

**From Haskell 2010 Report:**
```
funlhs → var apat { apat }           -- Function with patterns!
       | pat varop pat               -- Infix pattern
       | ( funlhs ) apat { apat }

apat → var [ @ apat]                 -- As-pattern ONLY in pattern position
     | gcon                          -- Constructor
     | literal
     | _
     | ( pat )                       -- Parenthesized pattern
```

**Key:** `apat` (atomic pattern) is a **separate grammar production** from `aexp` (atomic expression)!

**But:** They share syntax (`var`, `literal`, parens), so parser builds abstract tree first.

---

## Strategy 2: Agda's Two-Phase Parsing

### Agda's Approach

**Phase 1: Parse as Expression-like things**
```haskell
-- From Agda parser
Expr: 
  | Ident
  | Literal
  | Ident Args          -- Could be function app OR constructor pattern!
  | '(' Expr ')'
  | Expr Op Expr        -- Mixfix!
```

**Phase 2: Scope Checking + Disambiguation**
- **Name resolution:** Is `Cons` a constructor or function?
- **Fixity resolution:** What's the precedence of `*` vs `::`?
- **Pattern validation:** Can this expression be used as a pattern?

**Critical difference from Haskell:** Agda delays ALL disambiguation until **after scope checking**!

**Example:**
```agda
-- Input: def foo (a * b : Nat)
-- Phase 1 parse: Application(Application(Id("a"), Id("*")), Id("b"))
-- Phase 2 scope check:
--   - Lookup "*": Is it a constructor? No. Error or treat as variable?
--   - In binding position, expect pattern
--   - "*" is not a constructor, so parse error!
```

### How Agda Handles Mixfix in Patterns

**Key insight:** Agda's mixfix operators are **user-defined syntax** with **precedence graphs**!

**Example:**
```agda
data Vec (A : Set) : Nat -> Set where
  []   : Vec A zero
  _::_ : {n : Nat} -> A -> Vec A n -> Vec A (suc n)

-- Now :: is a CONSTRUCTOR with mixfix syntax
head : {A : Set} {n : Nat} -> Vec A (suc n) -> A
head (x :: xs) = x   -- ← Parser knows :: is constructor from scope!
```

**How it works:**
1. Parse `(x :: xs)` as abstract expression tree
2. Scope checker looks up `::`
3. Finds it's a **constructor** (not a function)
4. **Validates** as irrefutable pattern (:: is only constructor? No, [] exists, so refutable!)
5. Accepts in `case`, rejects in `let`

---

## Strategy 3: Scala's Case-Based Disambiguation

### Scala's Approach: Context + Type-Driven

**Key Insight:** Scala has THREE different contexts for patterns:

1. **Match expressions:** `x match { case pattern => ... }`
2. **Function literals with case:** `list.map { case (a, b) => a + b }`
3. **Val bindings:** `val (a, b) = tuple`

**Critical difference:** Scala uses `case` keyword to signal pattern context!

```scala
// Function parameter - regular syntax
def foo(pair: (Int, Int)): Int = pair._1 + pair._2

// Function parameter - pattern matching syntax
val foo: ((Int, Int)) => Int = { case (a, b) => a + b }

// They're DIFFERENT! The second is sugar for:
val foo = (x: (Int, Int)) => x match { case (a, b) => a + b }
```

**How Scala knows it's a pattern:**
1. **`case` keyword:** Explicit marker for pattern matching
2. **Expected type:** If expecting `FunctionN[S1, ..., Sn, R]`, parser knows `case` introduces patterns
3. **Grammar context:** Different productions for `def` params vs `case` params

### Scala's Constructor Patterns in Parameters

**In Scala 2:** CANNOT destructure in def parameters!
```scala
// ❌ Does NOT work in Scala 2:
def foo(a: Int, (b, c): (String, Int)) = ...

// ✅ Must use val or match:
def foo(a: Int, tpl: (String, Int)) = {
  val (b, c) = tpl
  ...
}
```

**In Scala 3:** Parameter untupling!
```scala
// ✅ Now works in Scala 3:
list.map((a, b) => a + b)  // Instead of: list.map { case (a, b) => a + b }

// Desugars to:
list.map((x: (Int, Int)) => {
  val (a, b) = x
  a + b
})
```

**Key:** Scala 3's parameter untupling is **syntactic sugar** that inserts a `val` pattern binding!

### How Scala Parser Handles Ambiguity

**From Scala compiler source:**

```scala
// Parser distinguishes by context:
def pattern(): Tree = {
  // Parse pattern-specific constructs:
  // - Constructor applications
  // - As-patterns (x @ pattern)
  // - Typed patterns (x: Type)
  // - Wildcards
}

def expr(): Tree = {
  // Parse expression-specific constructs:
  // - Function application
  // - Operators
  // - Literals
}

// In function parameters:
def funParams(): List[ValDef] = {
  // Parse as IDENTIFIERS, not patterns!
  // (a, b, c) => a + b
  // Parses as: List(ValDef("a"), ValDef("b"), ValDef("c"))
}

// In case clauses:
def caseClause(): CaseDef = {
  accept(CASE)  // Keyword signals pattern context!
  val pat = pattern()  // Now we know to parse as pattern
  val guard = if (in.token == IF) guard() else EmptyTree
  accept(ARROW)
  val body = expr()
  CaseDef(pat, guard, body)
}
```

**Key insight:** The `case` keyword **disambiguates** between parameter lists and patterns!

### Scala's Strategy for Mixfix in Patterns

**Scala doesn't have user-defined mixfix** - only built-in infix constructors!

```scala
// Infix constructor pattern
case class ::(head: A, tail: List[A])

// Usage in pattern:
list match {
  case x :: xs => ...  // :: is infix constructor
}

// Parser knows :: is constructor because:
// 1. We're in pattern position (after 'case')
// 2. Type checker validates :: is actually a case class
```

**For arbitrary operators in patterns:**
```scala
// ❌ Cannot use operators in patterns:
case x + 1 => ...  // ERROR: not a valid pattern

// ✅ Must use extractors:
case Even(n) => ...  // Calls Even.unapply(x)
```

**Scala's disambiguation:**
1. **Parse time:** `case` keyword → expect pattern grammar
2. **Type checking:** Validate that identifiers are constructors/extractors
3. **No general mixfix:** Only specific infix constructors allowed

---

## Strategy 4: OCaml's Separate Pattern Grammar

### OCaml's Approach: No Ambiguity

**Different grammars for patterns vs expressions:**

```ocaml
(* Pattern grammar *)
pattern:
  | ident                     (* Variable *)
  | constructor pattern*      (* Constructor application *)
  | pattern '::' pattern      (* Cons - ONLY in patterns! *)
  | '_'                       (* Wildcard *)
  | pattern 'as' ident        (* As-pattern *)
  | pattern '|' pattern       (* Or-pattern *)

(* Expression grammar *)
expr:
  | ident                     (* Variable *)
  | function_call expr*       (* Function application *)
  | expr '::' expr            (* Cons - ONLY in expressions! *)
  | expr '+' expr             (* Addition *)
```

**Key:** `::` has **different meanings** in pattern vs expression context!

```ocaml
(* Pattern *)
match list with
| x :: xs -> ...     (* :: is constructor pattern *)

(* Expression *)
let list = 1 :: 2 :: []   (* :: is cons function *)
```

**How does parser know?**
- **Context from grammar:** `match list with` → expect pattern
- **No ambiguity:** Parser knows we're in pattern position

---

## HWML's Unique Challenge: Type-Directed Mixfix

### The Problem

HWML has:
1. **Mixfix operators** (like Agda)
2. **Type-directed elaboration** (like Agda)
3. **Non-equational syntax** (UNlike Agda)

**Example:**
```rust
def foo (a * b : Pair) := ...
```

**Questions:**
1. Is `*` a constructor or operator?
2. Is `a * b` a pattern or expression?
3. How do we handle as-patterns: `xs @ (x :: xs')`?

---

## Recommended Solution for HWML

### Option 1: Haskell-Style DisambECP (RECOMMENDED)

**Parse into abstract tree, disambiguate by context:**

```rust
// Parse ambiguous forms into abstract syntax
enum AmbiguousSyntax {
    Ident(Id),
    App(Box<AmbiguousSyntax>, Box<AmbiguousSyntax>),
    Infix(Box<AmbiguousSyntax>, Id, Box<AmbiguousSyntax>),
    Paren(Box<AmbiguousSyntax>),
}

// Disambiguation into either pattern or expression
impl AmbiguousSyntax {
    fn as_pattern(&self, ctx: &ScopeContext) -> Result<Pattern> {
        match self {
            AmbiguousSyntax::Ident(id) => {
                // Check if it's a constructor
                if ctx.is_constructor(id) {
                    Ok(Pattern::Constructor { name: id.clone(), args: vec![] })
                } else {
                    Ok(Pattern::Var { name: id.clone() })
                }
            }
            AmbiguousSyntax::App(f, x) => {
                // f must be constructor or partial constructor application
                let ctor = f.as_constructor(ctx)?;
                let arg = x.as_pattern(ctx)?;
                Ok(Pattern::Constructor {
                    name: ctor.name,
                    args: ctor.args.push(arg),
                })
            }
            AmbiguousSyntax::Infix(l, op, r) => {
                // Is op a constructor?
                if ctx.is_constructor(op) {
                    Ok(Pattern::Constructor {
                        name: op.clone(),
                        args: vec![l.as_pattern(ctx)?, r.as_pattern(ctx)?],
                    })
                } else {
                    Err(Error::NotAPattern {
                        msg: format!("'{}' is not a constructor", op),
                    })
                }
            }
            AmbiguousSyntax::Paren(inner) => inner.as_pattern(ctx),
        }
    }
    
    fn as_expression(&self) -> Result<Expression> {
        // Similar, but allows operators, function calls, etc.
    }
}
```

**Advantages:**
- ✅ Handles mixfix operators naturally
- ✅ Disambiguation after scope checking (when we know what's a constructor)
- ✅ Same syntax can be used in both pattern and expression positions
- ✅ Proven approach (Haskell GHC, tested for decades)

**Parser changes:**
```rust
// In parser
fn parse_binder(ctx: &mut Context) -> Binder {
    // Parse as ambiguous syntax
    let ambig = parse_ambiguous_syntax(ctx);

    Binder {
        loc: ambig.location(),
        ambiguous: Some(ambig),  // Delay disambiguation!
        name: ctx.make_generated_name(),
    }
}
```

**Elaborator disambiguates:**
```rust
// In elaborator
fn elab_binder(&mut self, binder: &Binder, ty: &Type) -> Result<core::Binder> {
    let ambig = binder.ambiguous.as_ref().unwrap();

    // Try to interpret as pattern
    let pattern = ambig.as_pattern(&self.scope_context)?;

    // Validate it's irrefutable
    self.check_irrefutable(&pattern)?;

    Ok(core::Binder::Destruct {
        pattern: self.elab_pattern(pattern)?,
        ty: self.elab_type(ty)?,
    })
}
```

---

### Option 2: Agda-Style Two-Phase (Alternative)

**Parse as Expression, validate as Pattern during scope checking:**

```rust
// AST stays the same (Expression in binders)
pub struct TypedBindingGroup {
    pub binders: Vec<Box<Expression>>,  // Keep as Expression!
    pub ty: Box<Expression>,
}

// Scope checker validates
impl ScopeChecker {
    fn check_binding_pattern(&self, expr: &Expression) -> Result<Pattern> {
        match expr {
            Expression::Id(id) => {
                if self.is_constructor(id) {
                    Ok(Pattern::Constructor { name: id.clone(), args: vec![] })
                } else {
                    Ok(Pattern::Var { name: id.clone() })
                }
            }
            Expression::App(App { elements }) => {
                // First element must be constructor
                let ctor = match &elements[0] {
                    box Expression::Id(id) if self.is_constructor(id) => id,
                    _ => return Err(Error::NotAConstructorPattern),
                };

                // Rest are pattern arguments
                let args: Vec<Pattern> = elements[1..]
                    .iter()
                    .map(|e| self.check_binding_pattern(e))
                    .collect::<Result<_>>()?;

                Ok(Pattern::Constructor {
                    name: ctor.clone(),
                    args,
                })
            }
            _ => Err(Error::InvalidBindingPattern { expr: expr.clone() }),
        }
    }
}
```

**Advantages:**
- ✅ Simpler AST (no separate AmbiguousSyntax type)
- ✅ Works with current parser structure
- ✅ Disambiguation happens where we have type info

**Disadvantages:**
- ⚠️ Expression AST gets validated as pattern (semantically weird)
- ⚠️ Harder to give good error messages
- ⚠️ Future extensions (as-patterns, guards) require AST changes

---

## Handling As-Patterns

**Syntax:** `name @ pattern`

**Examples:**
```rust
def foo (xs @ (x :: xs') : List Nat) := ...
fun (pair @ (a, b)) => ...
match list with
| xs @ (Cons x xs') => ...
end
```

### Strategy 1: Parse @ as Special Operator

```rust
enum AmbiguousSyntax {
    // ... other variants
    AsPattern {
        name: Id,
        pattern: Box<AmbiguousSyntax>,
    },
}

// Parser recognizes @ specially
fn parse_ambiguous_atom(ctx: &mut Context) -> AmbiguousSyntax {
    let first = parse_identifier(ctx);

    if ctx.consume_if(Token::At).is_some() {
        // as-pattern!
        let pattern = parse_ambiguous_atom(ctx);
        AmbiguousSyntax::AsPattern {
            name: first,
            pattern: Box::new(pattern),
        }
    } else {
        AmbiguousSyntax::Ident(first)
    }
}
```

**Problem:** What if @ is also a mixfix operator?

**Solution:** Use **whitespace sensitivity** (like Haskell):
```rust
xs@(Cons x xs')   // ← As-pattern (no space before @)
xs @ (Cons x xs') // ← Infix operator (space before @)
```

Or: **Reserved syntax** - `@` is always as-pattern, never operator.

### Strategy 2: As-Patterns Only in Pattern Grammar

```rust
// Parse patterns separately from expressions
enum Pattern {
    Var { name: Id },
    Constructor { name: Id, args: Vec<Pattern> },
    As { name: Id, pattern: Box<Pattern> },  // ← Only in Pattern!
}

// @ can only appear in pattern position
fn parse_pattern_atom(ctx: &mut Context) -> Pattern {
    let name = parse_id(ctx);

    if ctx.consume_if(Token::At).is_some() {
        let inner = parse_pattern_atom(ctx);
        Pattern::As {
            name,
            pattern: Box::new(inner),
        }
    } else if ctx.is_constructor(&name) {
        // Could be constructor...
    } else {
        Pattern::Var { name }
    }
}
```

**Advantage:** No ambiguity - `@` is pattern-only syntax.

---

## Handling Mixfix in Patterns

### Challenge: Precedence Without Type Info

**Example:**
```rust
def foo (a * b + c : Expr) := ...
```

**Question:** Is this `(a * b) + c` or `a * (b + c)`?

**Answer:** Use **default precedence** during parsing, refine during elaboration!

```rust
// Parser
fn parse_ambiguous_infix(ctx: &mut Context) -> AmbiguousSyntax {
    // Use precedence climbing with DEFAULT precedences
    let mut lhs = parse_ambiguous_atom(ctx);

    while let Some(op) = peek_operator(ctx) {
        let op_prec = ctx.default_precedence(op);  // ← Default!

        if op_prec < min_prec {
            break;
        }

        ctx.consume_operator();
        let rhs = parse_ambiguous_infix(ctx, op_prec.next());

        lhs = AmbiguousSyntax::Infix(box lhs, op, box rhs);
    }

    lhs
}

// Elaborator refines based on actual operator precedences
impl AmbiguousSyntax {
    fn refine_precedence(&self, ctx: &ScopeContext) -> Self {
        // Re-parse infix with ACTUAL precedences from scope
        // This handles user-defined fixities!
    }
}
```

### Alternative: Agda's Approach

**Parse without precedence, reparse during scope checking:**

1. **Parse:** Treat all operators as function application
   ```
   a * b + c  →  App(App(App(a, *), b), +), c)
   ```

2. **Scope check:** Build precedence graph, reparse
   ```
   If * has higher precedence than +:
   App(App(App(a, *), b), +), c) → App(App(a, *, b), +, c)
   ```

**Problem for HWML:** More complex, requires full reparse pass.

---

## Final Recommendation

### For HWML: Hybrid Approach

**Phase 1: Parse (What the parser does)**
```rust
enum AmbiguousSyntax {
    Ident(Id),
    App(Box<AmbiguousSyntax>, Box<AmbiguousSyntax>),
    Infix(Box<AmbiguousSyntax>, Id, Box<AmbiguousSyntax>),
    AsPattern { name: Id, pattern: Box<AmbiguousSyntax> },  // @ is special
    Paren(Box<AmbiguousSyntax>),
}

struct Binder {
    loc: Range<usize>,
    ambiguous: AmbiguousSyntax,  // Delay disambiguation
}
```

**Phase 2: Scope Check (What scope checker does)**
```rust
impl AmbiguousSyntax {
    fn as_pattern(&self, scope: &ScopeContext) -> Result<Pattern> {
        // Disambiguate using constructor information
    }
}
```

**Phase 3: Elaborate (What elaborator does)**
```rust
impl Elaborator {
    fn elab_pattern(&mut self, pat: &Pattern, ty: &Type) -> Result<core::Pattern> {
        // Type-directed disambiguation for mixfix
        // Validate irrefutability
    }
}
```

**Benefits:**
1. ✅ Handles mixfix operators (disambiguate with scope info)
2. ✅ Handles as-patterns (@ is special syntax)
3. ✅ Clean separation (parse → scope → elab)
4. ✅ Proven approach (Haskell + Agda hybrid)
5. ✅ Extensible (add guards, or-patterns later)

---

## Summary

| Approach | Parse Time | Scope Check | Elaboration | Complexity | Pattern in Parameters? |
|----------|-----------|-------------|-------------|------------|------------------------|
| **Haskell DisambECP** | Ambiguous | Context-based | Validate | Medium | ✅ Yes (native) |
| **Agda Two-Phase** | Expression | Reparse | Type-directed | High | ✅ Yes (native) |
| **Scala Case-Based** | Pattern (if `case`) | Type-check constructors | None | Low | ⚠️ Only with `case` or `val` |
| **OCaml Separate** | Pattern | None | None | Low | ✅ Yes (native) |
| **HWML Hybrid** | Ambiguous | Constructor check | Type-directed | Medium | ✅ Yes (planned) |

### Key Differences

**Haskell:** Handles ambiguity with GADT abstraction, disambiguates based on grammar context.

**Agda:** Parse everything as expression-like, disambiguate during scope checking when constructor info available.

**Scala:** Uses `case` keyword to explicitly mark pattern positions. Parameter destructuring in Scala 3 is syntactic sugar (inserts `val` bindings).

**OCaml:** Separate grammars, no ambiguity. Operators can mean different things in pattern vs expression.

**HWML (Recommended):** Hybrid of Haskell + Agda - parse ambiguous syntax, disambiguate with scope context.

---

### Why Not Scala's Approach for HWML?

**Scala requires `case` keyword:**
```scala
// Scala
val foo: ((Int, Int)) => Int = { case (a, b) => a + b }

// HWML wants:
fun (a, b) => a + b  // No 'case' needed!
```

**HWML differences from Scala:**
1. **Mixfix operators:** HWML has user-defined mixfix, Scala only has built-in infix
2. **No case keyword:** HWML function syntax doesn't use `case` to mark patterns
3. **Type-directed elaboration:** HWML needs disambiguation during type checking anyway

**Therefore:** Use Haskell/Agda approach, not Scala's case-based approach.

---

**Recommendation:** **HWML Hybrid** - parse ambiguous, disambiguate during scope checking with constructor info, refine during type-directed elaboration.

**Timeline:** +2 days (add AmbiguousSyntax type, scope checker disambiguation)
