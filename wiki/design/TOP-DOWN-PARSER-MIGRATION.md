# Top-Down Recursive Parser Migration (from LALRPOP)

**Date:** 2026-05-10
**Status:** DESIGN - Ready for implementation (with critical revisions)
**Impact:** MAJOR - Complete parser rewrite, minimal change to lexer/AST
**Confidence:** 0.98

> **📋 COMPLETE DESIGN:** This document integrates three design documents:
> 1. Base architecture (this doc)
> 2. [[TOP-DOWN-PARSER-REVISION-TYPE-SAFETY]] - Type safety + error recovery fixes
> 3. [[PARSER-PROVENANCE-TRACKING]] - Parsing context tracking
>
> **Read all three for the complete picture.**

---

## Executive Summary

Replace LALRPOP-based parser with **Carbon-style top-down recursive descent parser** using:
- **State machine** with explicit state stack (states carry their own data)
- **Top-level while loop** driving parse
- **Handler dispatch** pattern (one handler per state)
- **Typed result stacks** (no runtime downcasting!)
- **Block-depth-aware error recovery** (no file swallowing!)
- **Provenance tracking** (rich error context)
- **Minimal lexer changes** (`hwml-surface/src/lex.rs` - unchanged)
- **Minimal AST changes** (`hwml-surface/src/syntax.rs` - add Error/Hole variants with provenance)

**Benefits:**
- ✅ **Better error recovery** - Multiple errors per parse, block-scoped recovery
- ✅ **Better diagnostics** - Context-aware messages with full parsing stack
- ✅ **Type safety** - Compile-time guarantees, no runtime panics
- ✅ **Easier debugging** - Explicit control flow, inspectable stacks
- ✅ **Faster iteration** - No build.rs codegen step
- ✅ **Foundation for future** - Enables mixfix operators, layout-sensitive parsing

**Trade-offs:**
- ❌ **More manual code** - ~2500 LOC vs ~350 LOC LALRPOP grammar
- ⚠️ **Initial implementation cost** - 4 weeks vs 0 (already have LALRPOP)
- ✅ **But:** Type-safe, robust, extensible, better errors

---

## Current Architecture (LALRPOP)

### Files
```
crates/hwml-surface/
├── build.rs              ← Runs LALRPOP codegen
├── src/
│   ├── grammar.lalrpop   ← 341 lines, generates ~5000 LOC Rust
│   ├── lex.rs            ← Logos-based lexer (UNCHANGED)
│   ├── syntax.rs         ← AST types (UNCHANGED)
│   └── parsing.rs        ← Thin wrapper around generated parser
```

### Problems
1. **Poor error recovery** - LALRPOP stops at first error
2. **Generic error messages** - "expected one of: ..." not helpful
3. **Opaque codegen** - generated code hard to debug
4. **Build-time dependency** - slows down development iteration
5. **Limited future** - can't support mixfix, layout sensitivity

---

## Target Architecture (Carbon-Style)

### New File Structure
```
crates/hwml-surface/
├── src/
│   ├── lex.rs            ← UNCHANGED (Logos lexer)
│   ├── syntax.rs         ← UNCHANGED (AST types)
│   ├── parse/
│   │   ├── mod.rs        ← Public API, main parse loop
│   │   ├── context.rs    ← Parser context (state stack, position, errors)
│   │   ├── state.rs      ← State enum definition
│   │   ├── handle_stmt.rs       ← Statement handlers (namespace, def, meta, prim, inductive, open)
│   │   ├── handle_expr.rs       ← Expression handlers (pi, arrow, app, fun, let, match)
│   │   ├── handle_bindings.rs   ← Binding group handlers
│   │   └── handle_inductive.rs  ← Inductive-specific handlers (constructors, indices)
```

**NO build.rs** - Pure Rust, no codegen!

---

## Design Principles (from Carbon)

### 1. Postorder Node Emission

**Pattern:** Nodes added to output in postorder (children before parents).

**Why:** Enables efficient single-pass checking later.

**Example:**
```rust
// Parsing: def foo : Nat := 42
// Postorder emission:
[DefIntroducer(def), Id(foo), Universe(Nat), Num(42), Def]
```

**HWML Adjustment:** Our AST already stores children in parent structs, so we build tree during parse (not flat postorder). This is fine - we're not optimizing for Carbon's checking style yet.

### 2. State Stack

**Pattern:** Explicit stack of parser states, top-level while loop pops and dispatches.

**Carbon Example:**
```cpp
while (!state_stack_.empty()) {
  auto state = state_stack_.back();
  state_stack_.pop_back();
  HandleState(state);  // Dispatch to handle_<feature>.cpp
}
```

**HWML Translation:**
```rust
pub struct Parser<'input> {
    context: Context<'input>,
}

impl<'input> Parser<'input> {
    pub fn parse(mut self) -> ParseResult {
        while let Some(state) = self.context.pop_state() {
            self.handle_state(state);
        }
        self.context.finalize()
    }

    fn handle_state(&mut self, state: State) {
        match state {
            State::Program => handle_program(self),
            State::Statement => handle_statement(self),
            State::DefAfterName => handle_def_after_name(self),
            // ... ~50 states total
        }
    }
}
```

### 3. Handler Dispatch

**Pattern:** One handler function per state, organized by feature.

**Files (Carbon style):**
```
handle_stmt.rs       ← namespace, def, meta, prim, open
handle_expr.rs       ← expressions (pi, arrow, app, etc.)
handle_bindings.rs   ← binding groups
handle_inductive.rs  ← inductive types + constructors
```

**Handler Signature:**
```rust
fn handle_def(ctx: &mut Context) {
    // 1. Pop state
    let state = ctx.pop_state();

    // 2. Consume tokens, build AST
    let def_kw = ctx.consume_token(Token::Def);
    let name = ctx.parse_id();

    // 3. Push next states (LIFO order - last pushed is next)
    ctx.push_state(State::DefFinish { def_kw, name });
    ctx.push_state(State::OptionalBindings);
}
```

### 4. Error Recovery

**Pattern:** Structured error recovery per state.

```rust
fn handle_def_after_name(ctx: &mut Context) {
    // Expected: optional bindings, optional ":", ":=", expr

    if ctx.at_token(Token::Assign) {
        // Missing type annotation is OK
        ctx.push_state(State::DefFinish);
        ctx.push_state(State::Expr);
        ctx.consume(Token::Assign);
    } else if ctx.at_token(Token::Colon) {
        // Has type annotation
        ctx.consume(Token::Colon);
        ctx.push_state(State::DefAfterType);
        ctx.push_state(State::Expr);
    } else {
        // ERROR: Expected ":" or ":="
        ctx.emit_error("Expected ':' or ':=' after definition name");
        ctx.skip_to_recovery_point(&[Token::Def, Token::Meta, Token::RBrace]);
        ctx.add_invalid_node();
    }
}
```

**Recovery Strategy:**
- Skip tokens until recovery point (next statement, closing brace)
- Add `InvalidParse` node to keep tree structurally valid
- Mark parent nodes with `has_error` flag
- Continue parsing (collect multiple errors!)

### 5. Bracketing Nodes

**Pattern:** Opening brackets signal start of variable-length subtrees.

**Carbon Example:**
```cpp
// Parsing: namespace Foo { def x := 1 }
// Emits bracketing sequence:
[NamespaceIntroducer(namespace), Id(Foo), LBrace,
 DefIntroducer(def), Id(x), Num(1), Def,
 NamespaceEnd(RBrace)]
```

**HWML Simplification:** We build tree eagerly, so bracketing is implicit in AST structure. No need for explicit bracketing nodes.

---

## Core Data Structures

### Context (Revised - Type-Safe Design)

**See [[TOP-DOWN-PARSER-REVISION-TYPE-SAFETY]] and [[PARSER-PROVENANCE-TRACKING]] for full details.**

```rust
pub struct Context<'input> {
    // ===== Input =====
    /// Source input (for byte ranges)
    input: &'input [u8],

    /// Source file path (for provenance)
    file_path: Option<String>,

    /// Token stream (from lexer)
    tokens: Vec<(Token, Range<usize>)>,

    /// Current position in token stream
    position: usize,

    // ===== State Machine =====
    /// Parser state stack (states carry their own data!)
    state_stack: Vec<State>,

    // ===== Typed Result Stacks (NO generic PartialNode!) =====
    /// Expression results being built
    expr_stack: Vec<Box<Expression>>,

    /// Binding groups being built
    bindings_stack: Vec<Bindings>,

    /// Typed binding groups being built
    typed_bindings_stack: Vec<TypedBindings>,

    /// Statement results being built
    statement_stack: Vec<Statement>,

    /// Identifiers being collected
    id_stack: Vec<Id>,

    // ===== Error Handling =====
    /// Collected parse errors
    errors: Vec<ParseError>,

    // ===== Block Depth Tracking (for error recovery) =====
    /// Block context stack (namespace, match, function, etc.)
    block_depth: Vec<BlockContext>,

    /// Brace matching stack
    brace_stack: Vec<Range<usize>>,

    /// Paren matching stack
    paren_stack: Vec<Range<usize>>,

    // ===== Provenance Tracking =====
    /// Stack of parsing operations in progress
    provenance_stack: Vec<ParseContext>,
}

impl<'input> Context<'input> {
    // ===== State Management =====
    fn push_state(&mut self, state: State);
    fn pop_state(&mut self) -> Option<State>;

    // ===== Token Consumption =====
    fn at_token(&self, tok: Token) -> bool;
    fn consume(&mut self, tok: Token) -> Range<usize>;
    fn consume_if(&mut self, tok: Token) -> Option<Range<usize>>;
    fn peek(&self) -> Option<&Token>;
    fn current_location(&self) -> Range<usize>;

    // ===== Typed Stack Operations (Type-Safe!) =====
    fn push_expr(&mut self, expr: Box<Expression>);
    fn pop_expr(&mut self) -> Box<Expression>;
    fn pop_optional_expr(&mut self) -> Option<Box<Expression>>;

    fn push_bindings(&mut self, bindings: Bindings);
    fn pop_bindings(&mut self) -> Bindings;

    fn push_statement(&mut self, stmt: Statement);
    fn pop_statement(&mut self) -> Statement;

    fn push_id(&mut self, id: Id);
    fn pop_id(&mut self) -> Id;

    // ===== Error Handling (with provenance) =====
    fn emit_error(&mut self, msg: impl Into<String>);
    fn emit_error_with_provenance(&mut self, msg: impl Into<String>);
    fn skip_to_recovery_point(&mut self, recovery: &[Token]);  // Block-depth-aware!

    // ===== Error Node Creation (with provenance) =====
    fn make_error_expr(&self) -> Box<Expression>;
    fn make_hole_expr(&self) -> Box<Expression>;
    fn make_error_statement(&self) -> Statement;

    // ===== Block Depth Tracking =====
    fn enter_block(&mut self, kind: BlockKind);
    fn exit_block(&mut self);
    fn current_block_kind(&self) -> BlockKind;
    fn current_brace_depth(&self) -> usize;

    // ===== Provenance Tracking =====
    fn enter_context(&mut self, ctx: ParseContext);
    fn exit_context(&mut self);
    fn capture_provenance(&self) -> ParseProvenance;

    // ===== Finalization =====
    fn finalize(self) -> ParseResult;
}
```

### State Enum (States Carry Their Own Data!)

**Key Design:** States carry all accumulated data, eliminating the need for a generic node stack.

```rust
#[derive(Clone, Debug)]
pub enum State {
    // ===== Top-level =====
    Program,
    Statement,

    // ===== Namespace =====
    NamespaceStart { loc: Range<usize>, name: Id },
    NamespaceBody { loc: Range<usize>, name: Id },

    // ===== Def Statement =====
    DefStart { loc: Range<usize> },
    DefAfterName {
        loc: Range<usize>,
        name: Id,
    },
    DefAfterBindings {
        loc: Range<usize>,
        name: Id,
        bindings: Bindings,
    },
    DefAfterType {
        loc: Range<usize>,
        name: Id,
        bindings: Bindings,
        ty: Box<Expression>,
    },
    DefAfterValue {
        loc: Range<usize>,
        name: Id,
        bindings: Bindings,
        ty: Option<Box<Expression>>,
        // value will be popped from expr_stack
    },

    // ===== Meta Statement (similar structure) =====
    MetaStart { loc: Range<usize> },
    MetaAfterName { loc: Range<usize>, name: Id },
    // ... similar progression

    // ===== Prim Statement =====
    PrimStart { loc: Range<usize> },
    PrimAfterName { loc: Range<usize>, name: Id },

    // ===== Inductive =====
    InductiveStart { loc: Range<usize> },
    InductiveAfterName {
        loc: Range<usize>,
        name: Id,
    },
    InductiveAfterParams {
        loc: Range<usize>,
        name: Id,
        params: TypedBindings,
    },
    InductiveAfterIndices {
        loc: Range<usize>,
        name: Id,
        params: TypedBindings,
        indices: TypedBindings,
    },
    InductiveConstructors {
        loc: Range<usize>,
        name: Id,
        params: TypedBindings,
        indices: TypedBindings,
        universe: Box<Expression>,
        constructors: Vec<Constructor>,
    },
    Constructor,

    // ===== Expressions =====
    ExprStart { min_prec: Precedence },
    ExprFinish { partial: Box<Expression> },

    PiAfterBindings {
        loc: Range<usize>,
        bindings: TypedBindings,
    },

    FunAfterKeyword { loc: Range<usize> },
    FunAfterBindings {
        loc: Range<usize>,
        bindings: Bindings,
    },

    LetAfterKeyword { loc: Range<usize> },
    LetAfterName {
        loc: Range<usize>,
        name: Id,
    },
    // ... etc

    // ===== Bindings =====
    Bindings,
    BindingGroup,
    TypedBindingGroup,
}
```

**Benefits:**
- ✅ Each state knows exactly what data it needs
- ✅ No downcasting (compiler knows the types!)
- ✅ Clear ownership (data moves through states)
- ✅ Easy to debug (inspect state variants)

### Precedence Handling

```rust
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Precedence {
    Lowest,      // Pi, Arrow, FatArrow
    App,         // Application (juxtaposition)
    Dot,         // a.b field access
    Atomic,      // Literals, ids, parens
}

// Expression parser uses precedence climbing
fn parse_expr_with_precedence(ctx: &mut Context, min_prec: Precedence) -> Box<Expression> {
    let mut lhs = parse_atomic_expr(ctx);

    while let Some(op) = peek_binary_op(ctx) {
        let op_prec = op.precedence();
        if op_prec < min_prec {
            break;
        }

        ctx.consume_operator(op);
        let rhs = parse_expr_with_precedence(ctx, op_prec.next());
        lhs = construct_binary(op, lhs, rhs);
    }

    lhs
}
```

---

## Implementation Plan (Revised - 4 Weeks + 2 Days)

**Total Timeline:** 22 days (includes Pattern grammar + scope checker operator resolution)

**🚨 CRITICAL UPDATE:** HWML uses Agda-style mixfix operators. Parser CANNOT determine operator structure without scope/fixity information. See [[PATTERN-MIXFIX-AGDA-STYLE]] for details.

**Key Change:** Parser produces flat application sequences (`AppSeq`). Scope checker reparses using fixity information.

### Phase 1: Foundation (2.5 days)

**Goal:** Basic infrastructure with typed stacks and provenance.

**Tasks:**
1. Create `parse/mod.rs` with `Parser` struct and main loop
2. Create `parse/context.rs` with `Context` struct
   - Typed stacks (expr_stack, bindings_stack, etc.)
   - Block depth tracking (block_depth, brace_stack)
   - Provenance tracking (provenance_stack)
3. Create `parse/state.rs` with `State` enum (states carry data)
4. Create `parse/provenance.rs` with `ParseContext` and `ParseProvenance` types
5. Update `syntax.rs` with Error/Hole variants + provenance types
6. Write tests for token consumption, state stack, typed stacks

**Deliverable:** Compiles, has complete infrastructure, no actual parsing yet.

---

### Phase 2: Simple Statements (2 days)

**Goal:** Parse `prim`, `def`, `meta` (simplest statements).

**Tasks:**
1. Implement `handle_stmt.rs`:
   - `handle_statement()` - dispatch on keyword
   - `handle_prim()` - `prim id : Expr` with provenance
   - `handle_def()` - `def id Bindings? (: Expr)? := Expr` with provenance
   - `handle_meta()` - `meta id Bindings? (: Expr)? := Expr` with provenance
   - Use `enter_context`/`exit_context` for provenance tracking

2. Implement basic expression parsing:
   - `handle_expr.rs::parse_atomic()` - literals, ids, parens
   - Use typed expr_stack
   - Create error nodes with provenance on failure

3. Write tests:
   - `prim Nat : Type`
   - `def zero : Nat := 0`
   - `meta id : Nat := 42`
   - Test error recovery with provenance

**Deliverable:** Can parse simple top-level definitions with rich error context.

---

### Phase 3: Expressions (2 days)

**Goal:** Full expression grammar with precedence.

**Tasks:**
1. Implement precedence climbing in `handle_expr.rs`:
   - `parse_expr_with_precedence()` using typed expr_stack
   - Binary operators: `->`, `=>`, application, `.`
   - Pi types: `(x : A) -> B` with `enter_context(ParseContext::PiType)`
   - Fun: `fun x => e` with `enter_context(ParseContext::FunLambda)`
   - Let: `let x := e in e` with `enter_context(ParseContext::LetBinding)`
   - Use `make_error_expr()` on parse failures

2. Handle parentheses and grouping (track paren_stack for balancing)

3. Write tests for each expression form with error cases

**Deliverable:** Can parse complex expressions with provenance-aware error recovery.

---

### Phase 4: Bindings (1 day) 🚨 SIMPLIFIED

**Goal:** Parse binding groups `(x y z : Nat) (f : Nat -> Bool)` as FLAT SEQUENCES.

**Tasks:**
1. Implement `handle_bindings.rs`:
   - Parse binders as `Pattern::AppSeq` (flat list of identifiers)
   - NO operator parsing, NO precedence climbing
   - Just collect adjacent atoms into a sequence
   - Typed bindings: `(binders... : type)` → push to typed_bindings_stack
   - Use `enter_context(ParseContext::TypedBindingGroup)` for provenance
   - Create error bindings on failure

2. Integrate with `def`, `meta`, `fun`, `let`, `pi`

**Deliverable:** Full binding support with flat pattern sequences (simpler than original plan!)

---

### Phase 5: Inductive Types (2 days)

**Goal:** Parse `inductive` declarations with constructors.

**Tasks:**
1. Implement `handle_inductive.rs`:
   - `inductive Name (params) : (indices) -> Universe where`
   - Use `enter_context(ParseContext::Inductive { name })` for provenance
   - Constructor parsing: `| Ctor : Type` with `enter_context(ParseContext::Constructor)`
   - Handle `where` + constructor list
   - Error recovery: create error constructors on failure

2. Special case: parameters vs indices
   - Parameters before `:`
   - Indices between `:` and `->`

3. Write tests for Vec, List, Nat with error cases

**Deliverable:** Full inductive support with provenance.

---

### Phase 6: Namespace and Open (1 day)

**Goal:** Parse module system constructs.

**Tasks:**
1. Implement namespace parsing:
   - `namespace Name { ... }`
   - Use `enter_context(ParseContext::Namespace { name })` for provenance
   - Track brace_stack for balancing
   - Nested namespaces with block_depth tracking
   - Recursive statement parsing inside braces

2. Implement open parsing:
   - `open Name`
   - Modifiers: `(only)`, `hiding`, `renaming`
   - `as` alias

**Deliverable:** Full module system parsing with block-depth tracking.

---

### Phase 7: Error Recovery (2.5 days) ⚠️ CRITICAL

**Goal:** Robust block-depth-aware error handling, multiple errors per parse.

**Tasks:**
1. **Implement block-depth-aware recovery** (see [[TOP-DOWN-PARSER-REVISION-TYPE-SAFETY]]):
   - `skip_to_recovery_point()` that tracks block nesting
   - Statement level: skip to next `def`, `meta`, `}` but not past current block
   - Expression level: skip to `,`, `)`, `in`, `where` but not past current scope
   - Track brace_depth and paren_depth during recovery
   - **Ensure recovery doesn't "swallow" valid code**

2. Error node creation with provenance:
   - Use `make_error_expr()` and `make_error_statement()`
   - Capture full provenance stack in error nodes

3. Structured error messages with provenance:
   - "Expected X after Y"
   - "while parsing Z" (from provenance stack)
   - Show what was found instead

4. Test with intentionally broken input:
   - Errors inside nested blocks
   - Errors inside match expressions
   - Multiple errors in one parse

**Deliverable:** Parser continues after errors, collects multiple diagnostics, never swallows valid code.

---

### Phase 8: Match Expressions (1 day) 🚨 SIMPLIFIED

**Goal:** Parse pattern matching with flat pattern sequences.

**Tasks:**
1. **Pattern AST already implemented in Phase 4!**
   - `Pattern::AppSeq` for flat sequences
   - `Pattern::Ident`, `Underscore`, `Num`, `Str`
   - `Pattern::As` for as-patterns
   - `Pattern::Paren` for grouping

2. **Implement match expression parsing:**
   - `match e with | pat => body | pat => body end`
   - Use existing pattern parser (flat sequences)
   - Use `enter_context(ParseContext::MatchExpression)` for provenance
   - Each clause: `enter_context(ParseContext::MatchClause { pattern_loc })`
   - Error recovery within match (don't skip past `end`)
   - Block-depth tracking for nested matches

3. Test with patterns (all parsed as flat sequences):
   - Variable patterns: `x` → `Ident("x")`
   - Constructor patterns: `Cons x xs` → `AppSeq([Ident("Cons"), Ident("x"), Ident("xs")])`
   - Mixfix patterns: `if x then y else z` → `AppSeq([Ident("if"), ...])`
   - Wildcard patterns: `_`
   - Literal patterns: `0`, `42`
   - Error cases with provenance

**Deliverable:** Full match support (reuses Pattern grammar from Phase 4, much simpler!)

---

### Phase 9: Scope Checker Operator Resolution (2 days) ⚠️ NEW PHASE

**Goal:** Reparse flat pattern sequences into structured operators using scope/fixity information.

**Location:** `crates/hwml-scope/src/` (NEW CRATE or part of existing scope checker)

**Tasks:**
1. **Implement operator discovery:**
   - `find_applicable_operators(&[ResolvedName])` → find mixfix operators that could apply
   - Build database of operator parts and fixity declarations
   - Match operator parts against flat sequences

2. **Implement precedence graph:**
   - `PrecedenceGraph::build()` - construct precedence DAG from operators
   - Handle precedence conflicts
   - Support associativity (left/right/non-associative)

3. **Implement precedence climbing with fixity:**
   - `precedence_climb()` - reparse flat sequence using operator precedences
   - Generate all valid parsings (may be multiple!)
   - Build SPPF (Shared Packed Parse Forest) for ambiguous cases

4. **Integrate with pattern resolution:**
   - `resolve_pattern(surface::Pattern) -> core::Pattern`
   - Handle `Pattern::AppSeq` by reparsing
   - Produce `core::Pattern::Constructor` or `core::Pattern::MixfixOp`
   - Produce `core::Pattern::Ambiguous` if multiple parsings exist

5. Test with:
   - Simple constructors: `Cons x xs`
   - Mixfix operators: `if x then y else z`
   - Nested operators: `if (if a then b else c) then d else e`
   - Ambiguous precedence (should produce multiple candidates)
   - Error cases (no matching operators)

**Deliverable:** Scope checker can reparse patterns with full mixfix support!

**References:** See [[PATTERN-MIXFIX-AGDA-STYLE]] for detailed algorithm.

---

### Phase 10: Migration and Testing (2 days) 🔄 RENUMBERED

**Goal:** Replace LALRPOP, pass all existing tests.

**Tasks:**
1. Update `parsing.rs` to use new parser
2. Remove `build.rs` and LALRPOP dependency
3. Update `Cargo.toml`
4. Run full test suite
5. Fix any regressions
6. Verify error messages include provenance
7. Test error recovery on real-world broken code
8. **Test mixfix patterns** with scope checker integration

**Deliverable:** Complete migration, no LALRPOP, better errors, full mixfix support.

---

## Error Recovery Examples

### Example 1: Missing `:=` in Def

**Input:**
```
def foo : Nat 42
```

**LALRPOP (current):**
```
Error at offset 14: Unexpected token: 42, expected one of: ":="
```
Parsing stops. ❌

**Top-Down (new):**
```rust
fn handle_def_after_type(ctx: &mut Context) {
    if ctx.at_token(Token::Assign) {
        ctx.consume(Token::Assign);
        ctx.push_state(State::DefFinish);
        ctx.push_state(State::Expr);
    } else {
        // ERROR: expected :=
        ctx.emit_error_at(
            ctx.current_location(),
            "Expected ':=' after type annotation in definition"
        );

        // Recovery: assume user forgot :=, try to parse expr anyway
        if looks_like_expression(ctx.peek()) {
            ctx.push_state(State::DefFinish);
            ctx.push_state(State::Expr);
        } else {
            // Give up, skip to next statement
            ctx.skip_to_recovery_point(&[Token::Def, Token::Meta, Token::RBrace]);
        }
    }
}
```

**Output:**
```
Error at line 1, column 14: Expected ':=' after type annotation in definition
  def foo : Nat 42
                ^-- here
```
Parsing continues! ✅

---

### Example 2: Multiple Errors

**Input:**
```
def foo  Nat := 42      -- Missing ":"
def bar : := 10         -- Missing type
def baz : Nat  10       -- Missing ":="
```

**LALRPOP:** Stops at first error. ❌

**Top-Down:** Reports all three errors in one pass. ✅

---

## Precedence Handling Details

### Carbon's Approach

Carbon uses **operator precedence in state stack** (elegant but complex).

**HWML's Approach:** Use **precedence climbing** (simpler, well-understood).

```rust
#[derive(Copy, Clone, PartialOrd, Ord, PartialEq, Eq)]
enum Precedence {
    Lowest = 0,   // Pi, Arrow, FatArrow
    App = 1,      // Application (whitespace)
    Dot = 2,      // Field access a.b
    Atomic = 3,   // Literals, ids, parens
}

fn parse_expr(ctx: &mut Context) -> Box<Expression> {
    parse_expr_prec(ctx, Precedence::Lowest)
}

fn parse_expr_prec(ctx: &mut Context, min_prec: Precedence) -> Box<Expression> {
    // Parse left-hand side (atomic or prefix)
    let mut lhs = parse_prefix_expr(ctx);

    // Climb precedence levels
    loop {
        // Peek at next operator
        let op = match peek_binary_op(ctx) {
            Some(op) if op.precedence() >= min_prec => op,
            _ => break, // Lower precedence or no operator
        };

        ctx.consume_operator(op);

        // Parse right-hand side with higher precedence
        // (left-associative: +1, right-associative: +0)
        let rhs_prec = if op.is_right_assoc() {
            op.precedence()
        } else {
            op.precedence().next()
        };
        let rhs = parse_expr_prec(ctx, rhs_prec);

        // Construct binary operation
        lhs = match op {
            BinaryOp::Arrow => Expression::Arrow(Arrow::new(lhs, rhs)),
            BinaryOp::FatArrow => Expression::FatArrow(FatArrow::new(lhs, rhs)),
            BinaryOp::Dot => Expression::Dot(Dot::new(lhs, rhs)),
            // Application is implicit (no operator token)
        };
    }

    lhs
}

fn parse_prefix_expr(ctx: &mut Context) -> Box<Expression> {
    match ctx.peek() {
        Some(Token::LParen) if looks_like_pi(ctx) => parse_pi(ctx),
        Some(Token::Fun) => parse_fun(ctx),
        Some(Token::Let) => parse_let(ctx),
        Some(Token::Match) => parse_match(ctx),
        _ => parse_atomic_expr(ctx),
    }
}

fn parse_atomic_expr(ctx: &mut Context) -> Box<Expression> {
    match ctx.peek() {
        Some(Token::Ident) => parse_id(ctx),
        Some(Token::Num) => parse_num(ctx),
        Some(Token::Type) => parse_universe(ctx),
        Some(Token::Underscore) => parse_underscore(ctx),
        Some(Token::LParen) => parse_paren(ctx),
        _ => {
            ctx.emit_error("Expected expression");
            ctx.make_error_expr()
        }
    }
}
```

### Application Parsing

**Special case:** Application is **juxtaposition** (no operator).

```rust
// Parse: f x y z  (application chain)
fn parse_application(ctx: &mut Context) -> Box<Expression> {
    let mut elements = vec![parse_atomic_expr(ctx)];

    // Collect sequence of atoms
    while is_start_of_atomic_expr(ctx.peek()) {
        elements.push(parse_atomic_expr(ctx));
    }

    if elements.len() == 1 {
        elements.pop().unwrap()
    } else {
        Box::new(Expression::App(App::new(elements)))
    }
}
```

---

## AST Changes (Minimal!)

### Required Changes: Error/Hole Variants + Pattern Grammar

**See [[TOP-DOWN-PARSER-REVISION-TYPE-SAFETY]] and [[PARSER-PROVENANCE-TRACKING]]**

```rust
// In syntax.rs - ADD these variants and types

// 1. Add to Expression enum
pub enum Expression {
    Pi(Pi),
    Arrow(Arrow),
    App(App),
    Fun(Fun),
    LetIn(LetIn),
    Match(Match),  // NEW: Match expression
    // ... all existing variants UNCHANGED

    // NEW: Error placeholder with provenance
    Error {
        loc: Range<usize>,
        provenance: ParseProvenance,
    },

    // NEW: Missing expression with provenance
    Hole {
        loc: Range<usize>,
        provenance: ParseProvenance,
    },
}

// 2. ADD: Pattern AST (Agda-style flat sequences!) 🚨 UPDATED
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Pattern {
    /// Single identifier (variable, constructor, or operator part)
    /// Scope checker determines which!
    Ident(Id),

    /// Flat application sequence - NOT YET PARSED INTO OPERATORS
    /// Parser just collects adjacent atoms into a flat list
    /// Example: "if x then y else z" → AppSeq([if, x, then, y, else, z])
    /// Scope checker will reparse this using fixity information
    AppSeq {
        loc: Range<usize>,
        elements: Vec<Pattern>,  // Flat list - no operator structure yet!
    },

    /// As-pattern: name @ pattern
    /// Special syntax, parsed eagerly (@ is never an operator part)
    As {
        loc: Range<usize>,
        name: Id,
        pattern: Box<Pattern>,
    },

    /// Wildcard: `_`
    Underscore {
        loc: Range<usize>,
    },

    /// Number literal: `42`
    Num {
        loc: Range<usize>,
        value: i64,
    },

    /// String literal
    Str {
        loc: Range<usize>,
        value: String,
    },

    /// Parenthesized pattern: `(p)`
    /// Forces grouping
    Paren {
        loc: Range<usize>,
        pattern: Box<Pattern>,
    },

    /// Error pattern with provenance
    Error {
        loc: Range<usize>,
        provenance: ParseProvenance,
    },
}

// 2b. ADD: Binder struct
pub struct Binder {
    pub loc: Range<usize>,
    pub pattern: Pattern,  // Unparsed! Scope checker resolves.
}

// 3. ADD: Match clause
#[derive(Clone, Debug)]
pub struct MatchClause {
    pub loc: Range<usize>,
    pub pattern: Pattern,
    pub body: Box<Expression>,
}

// 4. ADD: Match expression
#[derive(Clone, Debug)]
pub struct Match {
    pub loc: Range<usize>,
    pub scrutinee: Box<Expression>,
    pub clauses: Vec<MatchClause>,
}

impl Match {
    pub fn new(loc: Range<usize>, scrutinee: Box<Expression>, clauses: Vec<MatchClause>) -> Self {
        Self { loc, scrutinee, clauses }
    }

    pub fn location(&self) -> Range<usize> {
        self.loc.clone()
    }
}

// NEW: Provenance type
pub struct ParseProvenance {
    /// Stack of parsing contexts (innermost last)
    pub contexts: Vec<ParseContext>,

    /// Source file (if known)
    pub file: Option<String>,

    /// Location where error was created
    pub error_loc: Range<usize>,

    /// Optional: What tokens we expected
    pub expected: Option<Vec<Token>>,

    /// Optional: What token we found instead
    pub found: Option<Token>,
}

pub enum ParseContext {
    File { path: String },
    Namespace { name: String, loc: Range<usize> },
    Def { name: String, loc: Range<usize> },
    FunLambda { loc: Range<usize> },
    LetBinding { name: String, loc: Range<usize> },
    MatchExpression { loc: Range<usize> },
    // ... all parsing operations
}

// Also add to Statement for statement-level errors:
pub enum Statement {
    Namespace(Namespace),
    Def(Def),
    Meta(Meta),
    Prim(Prim),
    Inductive(Inductive),
    Open(Open),

    // NEW: Invalid statement with provenance
    Invalid {
        loc: Range<usize>,
        provenance: ParseProvenance,
    },
}
```

### Everything Else: Unchanged!

**Existing AST structures are fully compatible:**

```rust
pub struct Def {
    pub loc: Range<usize>,
    pub id: Id,
    pub bindings: Bindings,
    pub ty: Option<Box<Expression>>,
    pub value: Box<Expression>,
}
// ↑ UNCHANGED - Parser builds these exactly as before
```

**Top-Down Parser Output:**

```rust
fn handle_def_finish(ctx: &mut Context, state: DefAfterValue) {
    // Type-safe pop from expr_stack!
    let value = ctx.pop_expr();

    let def = Def::new(
        state.loc,
        state.name,
        state.bindings,
        state.ty,
        value,
    );

    ctx.push_statement(Statement::Def(def));
}
```

**Result:** Parser outputs `Program { statements: Vec<Statement> }`, exactly as before (but with better error nodes!).

---

## Lexer Compatibility

### No Changes Required!

**Current Lexer (lex.rs using Logos):**
```rust
pub enum Token {
    Namespace, Def, Meta, Prim,
    Let, In, Fun, Match, With, End,
    LParen, RParen, LBrace, RBrace,
    Arrow, FatArrow, Colon, Assign,
    // ... all tokens unchanged
}
```

**Top-Down Parser:** Consumes `Token` stream, no lexer changes.

```rust
impl<'input> Context<'input> {
    fn new(input: &'input [u8]) -> Self {
        let lexer = Lexer::new(input);  // Same Logos lexer!
        let tokens: Vec<_> = lexer.collect();
        Context { tokens, position: 0, /* ... */ }
    }
}
```

---

## Testing Strategy

### Unit Tests (Per Handler)

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_simple_def() {
        let input = b"def foo : Nat := 42";
        let result = parse(input);
        assert!(result.errors.is_empty());
        assert_eq!(result.program.statements.len(), 1);

        let Statement::Def(def) = &result.program.statements[0];
        assert_eq!(def.id.value.as_ref(), "foo");
    }

    #[test]
    fn test_parse_def_missing_assign() {
        let input = b"def foo : Nat 42";
        let result = parse(input);
        assert_eq!(result.errors.len(), 1);
        assert!(result.errors[0].message.contains("Expected ':='"));
        // Should still produce a Def node (with has_error flag)
        assert_eq!(result.program.statements.len(), 1);
    }
}
```

### Integration Tests (Full Programs)

```rust
#[test]
fn test_parse_full_program() {
    let input = b"
        namespace Nat {
            inductive Nat : Type where
                | zero : Nat
                | succ : Nat -> Nat

            def add (n m : Nat) : Nat :=
                match n with
                | zero => m
                | succ n' => succ (add n' m)
                end
        }

        open Nat
    ";
    let result = parse(input);
    assert!(result.errors.is_empty());
    assert_eq!(result.program.statements.len(), 2);
}
```

### Fuzz Testing

```rust
#[test]
fn fuzz_parser_no_panic() {
    use quickcheck::quickcheck;

    fn prop(input: Vec<u8>) -> bool {
        let _ = parse(&input);
        true  // Just ensure no panic
    }

    quickcheck(prop as fn(Vec<u8>) -> bool);
}
```

---

## Migration Checklist (4 Weeks + 2 Days) 🚨 UPDATED

- [ ] **Week 1: Foundation + Core Features**
  - [ ] Phase 1: Infrastructure with typed stacks + provenance (2.5 days)
  - [ ] Phase 2: Simple statements (2 days)
  - [ ] Phase 3: Expressions (2 days)

- [ ] **Week 2: Complete Grammar**
  - [ ] Phase 4: Bindings with flat Pattern sequences (1 day) 🚨 SIMPLER
  - [ ] Phase 5: Inductive (2 days)
  - [ ] Phase 6: Namespace/Open (1 day)
  - [ ] Phase 7: Block-depth-aware error recovery (2.5 days) ⚠️

- [ ] **Week 3: Pattern Support + Migration**
  - [ ] Phase 8: Match expressions (1 day) 🚨 SIMPLER (reuses Phase 4)
  - [ ] Phase 9: Scope checker operator resolution (2 days) ⚠️ NEW!
  - [ ] Phase 10: Migration + testing (2 days) 🔄 RENUMBERED

- [ ] **Week 4: Polish + Documentation**
  - [ ] Provenance integration testing (1 day)
  - [ ] Error message quality review (1 day)
  - [ ] Performance testing (1 day)
  - [ ] Mixfix pattern testing (1 day) 🚨 NEW!
  - [ ] Error recovery stress testing (1 day)

---

## Success Metrics

### Functional
- ✅ Parses all existing test cases
- ✅ Produces identical AST to LALRPOP version (modulo error nodes)
- ✅ Collects multiple errors per parse (vs 1 with LALRPOP)
- ✅ **Better error messages with provenance** (context-aware)
- ✅ **No file swallowing** (block-depth-aware error recovery)
- ✅ **No runtime panics** (type-safe stacks)

### Non-Functional
- ✅ No build.rs dependency
- ✅ Faster development iteration (no codegen)
- ✅ Parser code is debuggable (step through with debugger, inspect typed stacks)
- ✅ Foundation for future features (mixfix, layout)
- ✅ **Robust error handling** (confined recovery, full provenance)

### Performance
- ⚠️ Acceptable: Within 2x of LALRPOP speed
- ✅ Good: Within 1.5x of LALRPOP speed
- 🎯 Excellent: Faster than LALRPOP

(Measure with `cargo bench` on real-world programs)

### Error Quality (NEW)
- ✅ Error messages show full parsing context
- ✅ Errors confined to local scope (no file swallowing)
- ✅ Multiple errors reported in single pass
- ✅ Provenance captured for downstream phases (elaborator, type-checker)

---

## Future Extensions (Not in Scope)

### Enabled by This Design

1. **Mixfix Operators** (see `wiki/research/mixfix-type-directed-parsing.md`)
   - Parser can handle ambiguous operator sequences
   - Generate SPPF (Shared Packed Parse Forest)
   - Type-checker disambiguates

2. **Layout-Sensitive Parsing** (Python/Haskell-style)
   - Track indentation in lexer
   - Parser respects layout rules
   - Enables `where`-blocks without `end`

3. **Incremental Parsing**
   - Cached parse trees per statement
   - Re-parse only changed regions
   - Integrate with Salsa

4. **Better IDE Support**
   - Partial parse trees for incomplete code
   - Error tolerant parsing
   - Syntax highlighting from parser state

---

## References

### Design Inspiration
- [[carbon-parsing-ast-infrastructure]] - Carbon's parser architecture (2026-05-10)
- Carbon `toolchain/parse/` directory - Implementation reference
- Carbon `toolchain/docs/parse.md` - Postorder tree, bracketing nodes

### HWML Context
- `crates/hwml-surface/src/lex.rs` - Current lexer (UNCHANGED)
- `crates/hwml-surface/src/syntax.rs` - Current AST (MINIMAL CHANGES: +Error/Hole variants with provenance)
- `crates/hwml-surface/src/grammar.lalrpop` - Current grammar (TO REPLACE)

### Related Design Documents
- [[TOP-DOWN-PARSER-REVISION-TYPE-SAFETY]] - **CRITICAL** Type-safe stacks + block-depth error recovery
- [[PARSER-PROVENANCE-TRACKING]] - Parsing context capture for diagnostics
- [[provenance-deep-dive]] - Elaborator provenance (complementary system)
- [[DIAGNOSTIC-FRAMEWORK-SUMMARY]] - How provenance feeds diagnostics

### Related Research
- [[benes-flow-variational-overloading]] - Future: mixfix + overloading
- [[mixfix-backtracking-free-parsing]] - Future: bounded backtracking
- [[parse-forest-type-disambiguation]] - Future: SPPF + type-directed

---

**Status:** ✅ Ready for implementation (all critical revisions integrated, Agda-style mixfix patterns)
**Estimated Timeline:** 4 weeks + 2 days (22 days total) 🚨 UPDATED
- Week 1: Foundation + core features (5 days)
- Week 2: Complete grammar + error recovery (5 days)
- Week 3: Pattern support + scope checker operator resolution (5 days) 🚨 NEW PHASE
- Week 4: Polish + documentation (5 days)
- +2 days: Flat pattern parsing (Phase 4) + scope checker operator resolution (Phase 9)

**Risk:** Low (can develop alongside LALRPOP, switch when ready)

**Key Improvements Over Naive Design:**
1. ✅ Type-safe stacks (no runtime panics)
2. ✅ Block-depth-aware error recovery (no file swallowing)
3. ✅ Provenance tracking (rich error context)
4. ✅ **Agda-style flat pattern sequences** (parser doesn't need fixity info!)
5. ✅ **Scope checker operator resolution** (correct phase for disambiguation!)

**Critical Insight:** HWML uses Agda-style mixfix operators. Parser cannot determine operator structure without scope/fixity information. See [[PATTERN-MIXFIX-AGDA-STYLE]] for full details.

**Next Step:** Create `crates/hwml-surface/src/parse/` directory, begin Phase 1
