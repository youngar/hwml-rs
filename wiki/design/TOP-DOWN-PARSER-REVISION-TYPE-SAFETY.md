# Top-Down Parser Design: Type Safety Revision

**Date:** 2026-05-10  
**Status:** CRITICAL REVISION - Fixes type-safety and error recovery flaws  
**Supersedes:** Sections of TOP-DOWN-PARSER-MIGRATION.md  
**Confidence:** 0.98  

---

## Problem Statement

The initial design in `TOP-DOWN-PARSER-MIGRATION.md` has **two critical flaws**:

1. **Type-Safety Trap:** `node_stack: Vec<PartialNode>` requires runtime downcasting, leading to panics
2. **Naive Error Recovery:** Flat token list skipping swallows entire files in nested contexts

Both flaws would cause **compiler crashes** in production. This revision fixes them.

---

## Flaw #1: The PartialNode Type-Safety Trap

### Original (Broken) Design

```rust
pub struct Context<'input> {
    node_stack: Vec<PartialNode>,  // ❌ Runtime type errors!
}

enum PartialNode {
    Expr(Box<Expression>),
    Bindings(Bindings),
    Statement(Statement),
    Id(Id),
    // ... 15 more variants
}

// In handler:
fn handle_def_finish(ctx: &mut Context) {
    let value = ctx.pop_expr();      // ❌ What if it's actually Bindings?
    let ty = ctx.pop_optional_expr(); // ❌ Runtime panic if stack is wrong!
    // ...
}

impl Context<'_> {
    fn pop_expr(&mut self) -> Box<Expression> {
        match self.node_stack.pop() {
            Some(PartialNode::Expr(e)) => e,
            _ => panic!("Expected expression on stack!"),  // 💥 CRASH
        }
    }
}
```

**Problem:** If parser state machine gets out of sync (especially during error recovery), `pop_expr()` panics and crashes the compiler.

---

### Solution: Typed State Payloads

**Key Insight:** State variants carry their own data, eliminating the node stack!

```rust
#[derive(Clone, Debug)]
pub enum State {
    // Top-level
    Program,
    Statement,
    
    // Def statement - each state carries exactly what it needs
    DefStart {
        loc: Range<usize>,
    },
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
        value: Box<Expression>,
    },
    
    // Expression states
    ExprStart { min_prec: Precedence },
    ExprFinish { partial: Box<Expression> },
    
    // ... all other states carry their own data
}
```

**Handler Pattern:**

```rust
fn handle_def_start(ctx: &mut Context, state: DefStart) {
    // Consume "def" keyword
    ctx.consume(Token::Def);
    
    // Parse identifier
    let name = ctx.parse_id();
    
    // Push next state with accumulated data
    ctx.push_state(State::DefAfterName {
        loc: state.loc,
        name,
    });
}

fn handle_def_after_name(ctx: &mut Context, state: DefAfterName) {
    // Parse optional bindings
    let bindings = ctx.parse_optional_bindings();
    
    // Check for type annotation
    if ctx.at_token(Token::Colon) {
        ctx.consume(Token::Colon);
        ctx.push_state(State::DefAfterType {
            loc: state.loc,
            name: state.name,
            bindings,
            ty: /* will be filled by expr state */
        });
        ctx.push_state(State::ExprStart { min_prec: Precedence::Lowest });
    } else if ctx.at_token(Token::Assign) {
        // No type annotation
        ctx.push_state(State::DefAfterType {
            loc: state.loc,
            name: state.name,
            bindings,
            ty: Box::new(Expression::Hole), // Will be replaced
        });
    }
}
```

**Wait, how do we pass the expression result back?**

---

### Solution Part 2: Result Stack (Typed!)

Instead of generic `PartialNode`, use **typed result stacks**:

```rust
pub struct Context<'input> {
    // Separate typed stacks for each category
    expr_stack: Vec<Box<Expression>>,
    bindings_stack: Vec<Bindings>,
    statement_stack: Vec<Statement>,
    id_stack: Vec<Id>,
    
    // NO generic PartialNode stack!
}

impl Context<'_> {
    fn push_expr(&mut self, expr: Box<Expression>) {
        self.expr_stack.push(expr);
    }
    
    fn pop_expr(&mut self) -> Box<Expression> {
        self.expr_stack.pop()
            .expect("BUG: expr_stack empty - parser state machine corrupted")
    }
    
    fn pop_optional_expr(&mut self) -> Option<Box<Expression>> {
        if self.expr_stack.is_empty() {
            None
        } else {
            Some(self.expr_stack.pop().unwrap())
        }
    }
}
```

**Revised Handler:**

```rust
fn handle_def_after_value(ctx: &mut Context, state: DefAfterValue) {
    // Type-safe pop - compiler knows this is Box<Expression>!
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

**Benefits:**
- ✅ **Compile-time type safety** - Can't call `pop_expr()` and get `Bindings`
- ✅ **Clear ownership** - Each stack owns its type
- ✅ **Better error messages** - Panic messages say which stack is wrong
- ✅ **Easier debugging** - Inspect stacks in debugger, see actual types

---

### Error Recovery with Typed Stacks

**Problem:** What if error recovery leaves stacks in inconsistent state?

**Solution:** Poison/Error nodes + stack cleanup

```rust
impl Context<'_> {
    fn recover_from_error(&mut self, error_loc: Range<usize>) {
        // Push error sentinel values onto stacks
        self.expr_stack.push(Box::new(Expression::Error(error_loc.clone())));
        self.bindings_stack.push(Bindings::empty());
        
        // Skip to recovery point
        self.skip_to_recovery_with_depth_tracking(/* ... */);
    }
    
    fn clear_stacks_to_statement_boundary(&mut self) {
        // When recovering from statement-level error, clear partial results
        self.expr_stack.clear();
        self.bindings_stack.clear();
        // statement_stack stays (we're building statements)
    }
}
```

**Add Error variants to AST:**

```rust
// In syntax.rs (SMALL ADDITION to AST)
pub enum Expression {
    Pi(Pi),
    Arrow(Arrow),
    // ... existing variants
    Error(Range<usize>),  // NEW: Error placeholder
    Hole(Range<usize>),   // NEW: Missing expression
}

pub struct Bindings {
    pub groups: Vec<BindingGroup>,
    pub has_error: bool,  // NEW: Mark error state
}
```

This is a **minimal AST change** (just 2 new Expression variants + error flag).

---

## Flaw #2: Naive Error Recovery

### Original (Broken) Design

```rust
ctx.skip_to_recovery_point(&[Token::Def, Token::Meta, Token::RBrace]);
```

**Problem:** Skips tokens blindly, can swallow entire file.

**Example:**
```lean
namespace Foo {
    def a : Nat :=     -- Missing value
    def b : Nat := 2
    def c : Nat := 3
    ...
}  -- 500 lines later

namespace Bar {
    def x : Nat := 1
}
```

If error recovery skips to `Token::Def`, it might jump out of `Foo`, skip hundreds of lines, and land at `def x` in `Bar`. The user sees one error and 500 lines disappear!

---

### Solution: Block-Depth-Aware Recovery

```rust
pub struct Context<'input> {
    // ... other fields
    
    /// Track nesting depth for error recovery
    block_depth: Vec<BlockContext>,
}

#[derive(Copy, Clone, Debug)]
struct BlockContext {
    /// What kind of block (namespace, match, etc.)
    kind: BlockKind,
    
    /// Brace depth when block started
    brace_depth: usize,
    
    /// Paren depth when block started
    paren_depth: usize,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum BlockKind {
    Namespace,
    Match,
    Function,
    TopLevel,
}

impl Context<'_> {
    fn enter_block(&mut self, kind: BlockKind) {
        self.block_depth.push(BlockContext {
            kind,
            brace_depth: self.current_brace_depth(),
            paren_depth: self.current_paren_depth(),
        });
    }
    
    fn exit_block(&mut self) {
        self.block_depth.pop();
    }
    
    fn current_block_kind(&self) -> BlockKind {
        self.block_depth.last()
            .map(|b| b.kind)
            .unwrap_or(BlockKind::TopLevel)
    }
}
```

**Smart Recovery:**

```rust
impl Context<'_> {
    fn skip_to_recovery_point(&mut self, recovery_tokens: &[Token]) {
        let start_depth = self.block_depth.len();
        
        while let Some(token) = self.peek() {
            // STOP if we've exited the error's block
            if self.block_depth.len() < start_depth {
                break;  // Don't leave the block!
            }
            
            // STOP if we hit a recovery token at the right depth
            if recovery_tokens.contains(token) &&
               self.block_depth.len() == start_depth {
                break;
            }
            
            // Track block entry/exit
            match token {
                Token::LBrace => self.enter_anonymous_block(),
                Token::RBrace => {
                    self.exit_anonymous_block();
                    // If we just exited the error's block, stop
                    if self.block_depth.len() < start_depth {
                        break;
                    }
                }
                _ => {}
            }
            
            self.advance();
        }
    }
}
```

**Example (Fixed):**

```lean
namespace Foo {
    def a : Nat :=     -- ERROR: missing value
    def b : Nat := 2
}

namespace Bar {
    def x : Nat := 1
}
```

**Old behavior:** Skip from error to `def x`, swallow `def b` and entire `Bar` namespace ❌

**New behavior:**  
1. Error at `def a`
2. Skip to next `def` at same block depth
3. Find `def b`, stop there ✅
4. Parse `def b` normally
5. Continue to `}`, exit namespace
6. Parse `Bar` normally ✅

---

### Recovery Strategy Table

| **Error Context** | **Recovery Tokens** | **Block Constraint** |
|-------------------|---------------------|----------------------|
| Top-level statement | `[Namespace, Def, Meta, Prim]` | Top-level only |
| Inside namespace | `[Def, Meta, Prim, RBrace]` | Current namespace depth |
| Inside match | `[Pipe, End, RBrace]` | Current match depth |
| Expression | `[Comma, RParen, RBrace, In, End]` | Current expr depth |
| Bindings | `[Arrow, Assign, Colon]` | Current binding depth |

---

## Revised Context Structure

```rust
pub struct Context<'input> {
    // Input
    input: &'input [u8],
    tokens: Vec<(Token, Range<usize>)>,
    position: usize,
    
    // State machine
    state_stack: Vec<State>,  // States carry their own data!
    
    // Typed result stacks (NO generic PartialNode!)
    expr_stack: Vec<Box<Expression>>,
    bindings_stack: Vec<Bindings>,
    statement_stack: Vec<Statement>,
    id_stack: Vec<Id>,
    typed_bindings_stack: Vec<TypedBindings>,
    
    // Error handling
    errors: Vec<ParseError>,
    
    // Block depth tracking for error recovery
    block_depth: Vec<BlockContext>,
    
    // Brace/paren matching (for recovery)
    brace_stack: Vec<Range<usize>>,
    paren_stack: Vec<Range<usize>>,
}
```

---

## Handler Example (Complete)

```rust
fn handle_def_start(ctx: &mut Context) {
    let loc_start = ctx.current_location();
    ctx.consume(Token::Def);
    
    // Parse identifier
    let name = match ctx.parse_id() {
        Ok(id) => id,
        Err(e) => {
            ctx.emit_error(e);
            ctx.skip_to_recovery_point(&[Token::Def, Token::Meta, Token::RBrace]);
            return; // Abort this def
        }
    };
    
    // Parse optional bindings
    let bindings = ctx.parse_optional_bindings();
    
    // Parse optional type annotation
    let ty = if ctx.consume_if(Token::Colon).is_some() {
        ctx.push_state(State::DefAfterType {
            loc: loc_start..ctx.current_location(),
            name: name.clone(),
            bindings: bindings.clone(),
        });
        ctx.push_state(State::ExprStart { min_prec: Precedence::Lowest });
        return; // Expression state will call DefAfterType
    } else {
        None
    };
    
    // Expect :=
    if ctx.consume_if(Token::Assign).is_none() {
        ctx.emit_error_at(
            ctx.current_location(),
            "Expected ':=' in definition"
        );
        // Recovery: try to parse value anyway
        if !looks_like_statement_start(ctx.peek()) {
            ctx.push_state(State::DefAfterValue {
                loc: loc_start..ctx.current_location(),
                name,
                bindings,
                ty,
            });
            ctx.push_state(State::ExprStart { min_prec: Precedence::Lowest });
        } else {
            ctx.skip_to_recovery_point(&[Token::Def, Token::Meta, Token::RBrace]);
        }
        return;
    }
    
    // Parse value expression
    ctx.push_state(State::DefAfterValue {
        loc: loc_start..ctx.current_location(),
        name,
        bindings,
        ty,
    });
    ctx.push_state(State::ExprStart { min_prec: Precedence::Lowest });
}

fn handle_def_after_value(ctx: &mut Context, state: DefAfterValue) {
    // Type-safe pop!
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

---

## Summary of Changes

### What Changed from Original Design

| **Aspect** | **Original (Broken)** | **Revised (Fixed)** |
|------------|----------------------|---------------------|
| **Node Storage** | `Vec<PartialNode>` enum | Typed stacks per category |
| **Type Safety** | Runtime downcasting | Compile-time guarantees |
| **State Payloads** | Empty states | States carry accumulated data |
| **Error Recovery** | Flat token list | Block-depth-aware skipping |
| **Recovery Scope** | File-wide swallowing | Confined to current block |
| **AST Changes** | None | +2 Expression variants (Error, Hole) |

### Type Safety Improvements

**Before:**
```rust
let expr = ctx.pop_expr();  // 💥 Might panic if stack has Bindings
```

**After:**
```rust
let expr = ctx.pop_expr();  // ✅ Compiler knows this is Box<Expression>
```

### Error Recovery Improvements

**Before:**
```rust
ctx.skip_to_recovery_point(&[Token::Def]);  // 💥 Might skip 1000 lines
```

**After:**
```rust
ctx.skip_to_recovery_point(&[Token::Def]);  // ✅ Stops at block boundary
```

---

## Impact on Implementation Timeline

**Original:** 3 weeks  
**Revised:** 3.5 weeks (extra 0.5 weeks for block depth tracking)

**Phases Updated:**
- Phase 1: +1 day for typed stacks
- Phase 7: +1 day for block-depth-aware recovery

**Total:** Still feasible in 3-4 weeks.

---

## References

- [[TOP-DOWN-PARSER-MIGRATION]] - Original design (sections superseded)
- [[carbon-parsing-ast-infrastructure]] - Carbon's approach (we diverge here)

**Status:** Ready for implementation with these critical fixes  
**Risk:** Low → Very Low (type safety + scoped recovery = robust)
