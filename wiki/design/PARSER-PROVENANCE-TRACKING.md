# Parser Provenance Tracking

**Date:** 2026-05-10  
**Status:** DESIGN ADDITION - Extends TOP-DOWN-PARSER-REVISION-TYPE-SAFETY  
**Impact:** MEDIUM - Improves diagnostic context  
**Confidence:** 0.95  

---

## Motivation

When the parser hits an error and creates an `Expression::Error` or `Expression::Hole` node, we need to capture **what we were doing** so that later phases (elaborator, type-checker) can provide better diagnostics.

**Example:**

Without provenance:
```
Error: Expected ':=' after type annotation
  at line 5, column 10
```

With provenance:
```
Error: Expected ':=' after type annotation
  while parsing definition 'compute_result'
    in namespace 'Math.Vector'
      in file 'vector.hwml'
  at line 5, column 10
```

The provenance stack shows the **parsing context** when the error occurred.

---

## Design: Provenance Stack

### Core Types

```rust
/// A parsing operation that can be in progress
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ParseContext {
    // Top-level
    File { path: String },
    
    // Statements
    Namespace { name: String, loc: Range<usize> },
    Def { name: String, loc: Range<usize> },
    Meta { name: String, loc: Range<usize> },
    Prim { name: String, loc: Range<usize> },
    Inductive { name: String, loc: Range<usize> },
    Constructor { name: String, parent_inductive: String, loc: Range<usize> },
    
    // Expressions
    PiType { loc: Range<usize> },
    FunLambda { loc: Range<usize> },
    LetBinding { name: String, loc: Range<usize> },
    MatchExpression { loc: Range<usize> },
    MatchClause { pattern_loc: Range<usize> },
    Application { loc: Range<usize> },
    FieldAccess { field: String, loc: Range<usize> },
    
    // Bindings
    TypedBindingGroup { loc: Range<usize> },
    UntypedBindingGroup { loc: Range<usize> },
}

/// Provenance captured when creating error nodes
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParseProvenance {
    /// Stack of parsing contexts (innermost last)
    pub contexts: Vec<ParseContext>,
    
    /// Source file (if known)
    pub file: Option<String>,
    
    /// Location where error was created
    pub error_loc: Range<usize>,
    
    /// Optional: What token we expected but didn't find
    pub expected: Option<Vec<Token>>,
    
    /// Optional: What token we found instead
    pub found: Option<Token>,
}
```

---

## Integration with Context

```rust
pub struct Context<'input> {
    // ... existing fields (tokens, state_stack, typed stacks, block_depth)
    
    /// Provenance stack tracking parsing operations
    provenance_stack: Vec<ParseContext>,
    
    /// Source file path (for provenance)
    file_path: Option<String>,
}

impl<'input> Context<'input> {
    /// Enter a parsing context (push onto provenance stack)
    pub fn enter_context(&mut self, ctx: ParseContext) {
        self.provenance_stack.push(ctx);
    }
    
    /// Exit a parsing context (pop from provenance stack)
    pub fn exit_context(&mut self) {
        self.provenance_stack.pop();
    }
    
    /// Create provenance snapshot for current parse state
    pub fn capture_provenance(&self) -> ParseProvenance {
        ParseProvenance {
            contexts: self.provenance_stack.clone(),
            file: self.file_path.clone(),
            error_loc: self.current_location(),
            expected: None,
            found: self.peek().cloned(),
        }
    }
    
    /// Create error expression with provenance
    pub fn make_error_expr(&self) -> Box<Expression> {
        Box::new(Expression::Error {
            loc: self.current_location(),
            provenance: self.capture_provenance(),
        })
    }
    
    /// Create hole expression with provenance
    pub fn make_hole_expr(&self) -> Box<Expression> {
        Box::new(Expression::Hole {
            loc: self.current_location(),
            provenance: self.capture_provenance(),
        })
    }
}
```

---

## Updated AST (Minimal Changes)

```rust
// In syntax.rs - UPDATE Error and Hole variants

pub enum Expression {
    Pi(Pi),
    Arrow(Arrow),
    // ... existing variants
    
    /// Error placeholder (was: Error(Range<usize>))
    Error {
        loc: Range<usize>,
        provenance: ParseProvenance,
    },
    
    /// Missing expression (was: Hole(Range<usize>))
    Hole {
        loc: Range<usize>,
        provenance: ParseProvenance,
    },
}

// Similar for Statement-level errors
pub enum Statement {
    Namespace(Namespace),
    Def(Def),
    // ... existing variants
    
    /// Invalid statement with provenance
    Invalid {
        loc: Range<usize>,
        provenance: ParseProvenance,
    },
}
```

---

## Handler Pattern with Provenance

### Example: Parsing a Definition

```rust
fn handle_def_start(ctx: &mut Context) {
    let loc_start = ctx.current_location();
    ctx.consume(Token::Def);
    
    // Parse identifier
    let name = match ctx.parse_id() {
        Ok(id) => id,
        Err(e) => {
            // ERROR: Can't parse name
            ctx.emit_error(e);
            
            // Create error statement with provenance
            let stmt = Statement::Invalid {
                loc: loc_start..ctx.current_location(),
                provenance: ctx.capture_provenance(),
            };
            ctx.push_statement(stmt);
            
            ctx.skip_to_recovery_point(&[Token::Def, Token::Meta, Token::RBrace]);
            return;
        }
    };
    
    // ENTER CONTEXT: Now parsing def 'name'
    ctx.enter_context(ParseContext::Def {
        name: name.value.to_string(),
        loc: loc_start..ctx.current_location(),
    });
    
    // Continue parsing (provenance stack now includes this def)
    ctx.push_state(State::DefAfterName { loc: loc_start..ctx.current_location(), name });
}

fn handle_def_finish(ctx: &mut Context, state: DefAfterValue) {
    let value = ctx.pop_expr();
    
    let def = Def::new(
        state.loc,
        state.name,
        state.bindings,
        state.ty,
        value,
    );
    
    ctx.push_statement(Statement::Def(def));
    
    // EXIT CONTEXT: Done parsing this def
    ctx.exit_context();
}
```

### Example: Parsing Function Lambda

```rust
fn handle_fun_start(ctx: &mut Context) {
    let loc_start = ctx.current_location();
    ctx.consume(Token::Fun);
    
    // ENTER CONTEXT
    ctx.enter_context(ParseContext::FunLambda {
        loc: loc_start..ctx.current_location(),
    });
    
    // Parse bindings
    let bindings = ctx.parse_bindings();
    
    // Expect =>
    if !ctx.consume_if(Token::FatArrow).is_some() {
        ctx.emit_error_at(
            ctx.current_location(),
            "Expected '=>' after function bindings"
        );
        
        // Create error expression WITH PROVENANCE
        let error_expr = ctx.make_error_expr();
        ctx.push_expr(error_expr);
        
        ctx.exit_context();
        return;
    }
    
    // Parse body expression
    ctx.push_state(State::FunFinish { loc: loc_start..ctx.current_location(), bindings });
    ctx.push_state(State::ExprStart { min_prec: Precedence::Lowest });
}

fn handle_fun_finish(ctx: &mut Context, state: FunFinish) {
    let body = ctx.pop_expr();
    
    let fun = Fun::new(state.loc, state.bindings, body);
    ctx.push_expr(Box::new(Expression::Fun(fun)));
    
    // EXIT CONTEXT
    ctx.exit_context();
}
```

---

## Provenance in Error Messages

### During Elaboration

When the elaborator encounters an error node:

```rust
// In elaborator
fn elab_expr(&mut self, expr: &Expression) -> Result<core::Expr, ElabError> {
    match expr {
        Expression::Error { loc, provenance } => {
            // Use provenance to give context!
            let mut msg = format!("Parse error at {}", format_loc(loc));
            
            for ctx in provenance.contexts.iter().rev() {
                msg.push_str(&format!("\n  while parsing {}", format_context(ctx)));
            }
            
            if let Some(expected) = &provenance.expected {
                msg.push_str(&format!("\n  expected one of: {:?}", expected));
            }
            
            if let Some(found) = &provenance.found {
                msg.push_str(&format!("\n  found: {:?}", found));
            }
            
            Err(ElabError::ParseError {
                message: msg,
                provenance: provenance.clone(),
            })
        }
        // ... other cases
    }
}

fn format_context(ctx: &ParseContext) -> String {
    match ctx {
        ParseContext::Def { name, .. } => format!("definition '{}'", name),
        ParseContext::Namespace { name, .. } => format!("namespace '{}'", name),
        ParseContext::FunLambda { .. } => "function lambda".to_string(),
        ParseContext::MatchClause { .. } => "match clause".to_string(),
        // ... other cases
    }
}
```

**Output:**
```
Parse error at line 10, column 5
  while parsing function lambda
    in definition 'compute'
      in namespace 'Math.Vector'
  expected one of: [FatArrow]
  found: Colon
```

---

## Scoped Context Management

Use RAII-style guards to ensure contexts are properly exited:

```rust
/// RAII guard for provenance context
pub struct ProvenanceGuard<'ctx> {
    ctx: &'ctx mut Context<'ctx>,
}

impl<'ctx> ProvenanceGuard<'ctx> {
    pub fn new(ctx: &'ctx mut Context<'ctx>, parse_ctx: ParseContext) -> Self {
        ctx.enter_context(parse_ctx);
        ProvenanceGuard { ctx }
    }
}

impl<'ctx> Drop for ProvenanceGuard<'ctx> {
    fn drop(&mut self) {
        self.ctx.exit_context();
    }
}

// Usage in handler:
fn handle_def_start(ctx: &mut Context) {
    let _guard = ProvenanceGuard::new(ctx, ParseContext::Def {
        name: name.value.to_string(),
        loc: loc_start..ctx.current_location(),
    });
    
    // Parse def body...
    // guard automatically exits context when function returns (even on error!)
}
```

---

## Integration with Diagnostic Framework

Provenance feeds into the diagnostic system (see DIAGNOSTIC-FRAMEWORK-SUMMARY):

```rust
// In diagnostic emission
impl Context<'_> {
    pub fn emit_error_with_provenance(&mut self, msg: impl Into<String>) {
        let provenance = self.capture_provenance();
        
        let mut diagnostic = Diagnostic::error(msg)
            .with_location(provenance.error_loc.clone());
        
        // Add notes for each context
        for ctx in provenance.contexts.iter().rev() {
            diagnostic = diagnostic.with_note(
                format!("while parsing {}", format_context(ctx)),
                ctx.location(),
            );
        }
        
        self.errors.push(diagnostic);
    }
}
```

---

## Benefits

### 1. Better Error Messages

**Before:**
```
Error: Expected '=>' 
  at line 15, column 10
```

**After:**
```
Error: Expected '=>' after function bindings
  at line 15, column 10
  while parsing function lambda
    in let binding 'compute_norm'
      in definition 'normalize'
        in namespace 'Math.Vector'
```

### 2. Elaborator Context

When elaborator hits `Expression::Error`, it knows exactly where in the parse tree it came from.

### 3. IDE Support

LSP can show full context on hover over error nodes.

### 4. Debugging

Print provenance stack when debugging parser issues.

---

## Implementation Cost

**Timeline Addition:** +1 day

**Phases Affected:**
- Phase 1 (Foundation): Add provenance types
- All handler phases: Wrap operations in `enter_context`/`exit_context`

**Total Timeline:** 3.5 weeks → **3.75 weeks** (still under 4 weeks)

---

## Summary

| **Aspect** | **Without Provenance** | **With Provenance** |
|------------|----------------------|-------------------|
| **Error nodes** | `Error(Range<usize>)` | `Error { loc, provenance }` |
| **Context tracking** | None | Stack of `ParseContext` |
| **Error messages** | "Expected X" | "Expected X while parsing Y in Z" |
| **Elaborator** | Blind to parse context | Sees full parse path |
| **Cost** | 0 | +1 day implementation |

---

## References

- [[TOP-DOWN-PARSER-REVISION-TYPE-SAFETY]] - Base parser design
- [[provenance-deep-dive]] - Elaborator provenance (complementary system)
- [[DIAGNOSTIC-FRAMEWORK-SUMMARY]] - How provenance feeds diagnostics

**Status:** Ready to integrate with parser design  
**Next Step:** Add `provenance_stack` to `Context` struct in Phase 1
