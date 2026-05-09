# Phase 4.0: Source Tracking via Context

**Date:** 2026-05-08  
**Approach:** Context-based source tracking (Solution 2 from critical issue analysis)  
**Effort:** 1-2 days  
**Status:** Detailed implementation plan

---

## Overview

**Goal:** Pass the current file's `Source<'db>` through `ElabContext` so all errors get real file locations instead of "synthetic".

**Strategy:** 
1. Intern file information once at file elaboration entry point
2. Store `Source<'db>` in `ElabContext`
3. All error locations automatically use the real source
4. Trace guards can update source when crossing file boundaries

---

## Architecture

### Current vs. New

**Current (Phase 3):**
```rust
pub struct ElabContext<'db> {
    trace_stack: Vec<ElabFrame<'db>>,
    current_location: Option<SourceRange<'db>>,
}

// Errors get synthetic sources
let word = Word::new(db, "universe");
let source = Source::new(db, SourceInfo::Synthetic(word));  // ❌
let span = SourceRange::new(source, id.loc.clone());
```

**Phase 4.0 (New):**
```rust
pub struct ElabContext<'db> {
    trace_stack: Vec<ElabFrame<'db>>,
    current_source: Source<'db>,                    // NEW!
    current_byte_range: Option<Range<usize>>,       // NEW!
}

// Errors get real file sources
let span = elab.context.current_location();  // ✅ Uses current_source!
```

---

## Detailed Design

### 1. Update ElabContext

**File:** `crates/hwml-elab/src/context.rs` (new)

```rust
use hwml_core::{Source, SourceRange};
use std::ops::Range;

pub struct ElabContext<'db> {
    /// Stack of elaboration frames for backtrace
    trace_stack: Vec<ElabFrame<'db>>,
    
    /// Current source file being elaborated
    /// Updated when crossing file boundaries (imports, etc.)
    current_source: Source<'db>,
    
    /// Current byte range within the source file
    /// Updated by trace guards
    current_byte_range: Option<Range<usize>>,
}

pub struct ElabFrame<'db> {
    pub description: String,
    pub location: SourceRange<'db>,
    pub kind: ElabFrameKind,
}

#[derive(Debug, Clone)]
pub enum ElabFrameKind {
    CheckingExpression,
    SynthesizingType,
    CheckingDefinition { name: String },
    CheckingFunctionApplication,
    CheckingReturnType,
    SolvingConstraints,
    CheckingConstructor { name: String },
    ElaboratingFile { path: String },  // NEW! For file-level frames
}

pub struct TraceGuard<'a, 'db> {
    context: &'a mut ElabContext<'db>,
}

impl<'a, 'db> Drop for TraceGuard<'a, 'db> {
    fn drop(&mut self) {
        self.context.trace_stack.pop();
    }
}

impl<'db> ElabContext<'db> {
    /// Create new context for a file
    pub fn new(source: Source<'db>) -> Self {
        ElabContext {
            trace_stack: Vec::new(),
            current_source: source,
            current_byte_range: None,
        }
    }
    
    /// Push a trace frame with byte range
    pub fn trace<'a>(
        &'a mut self,
        desc: impl Into<String>,
        byte_range: Range<usize>,
        kind: ElabFrameKind,
    ) -> TraceGuard<'a, 'db> {
        // Create SourceRange using current source
        let location = SourceRange::new(self.current_source, byte_range.clone());
        
        // Update current byte range
        self.current_byte_range = Some(byte_range);
        
        self.trace_stack.push(ElabFrame {
            description: desc.into(),
            location,
            kind,
        });
        
        TraceGuard { context: self }
    }
    
    /// Push a trace frame with pre-built SourceRange
    /// (for when crossing file boundaries)
    pub fn trace_with_source<'a>(
        &'a mut self,
        desc: impl Into<String>,
        location: SourceRange<'db>,
        kind: ElabFrameKind,
    ) -> TraceGuard<'a, 'db> {
        // Update current source to match the new location
        self.current_source = location.source;
        self.current_byte_range = Some(location.range.clone());
        
        self.trace_stack.push(ElabFrame {
            description: desc.into(),
            location,
            kind,
        });
        
        TraceGuard { context: self }
    }
    
    /// Get current location (source + byte range)
    pub fn current_location(&self) -> Option<SourceRange<'db>> {
        self.current_byte_range.as_ref().map(|range| {
            SourceRange::new(self.current_source, range.clone())
        })
    }
    
    /// Get backtrace snapshot
    pub fn snapshot(&self) -> Vec<ElabFrame<'db>> {
        self.trace_stack.clone()
    }
    
    /// Temporarily change source (for imports/cross-file operations)
    pub fn with_source<R>(
        &mut self,
        source: Source<'db>,
        f: impl FnOnce(&mut Self) -> R,
    ) -> R {
        let old_source = self.current_source;
        self.current_source = source;
        let result = f(self);
        self.current_source = old_source;
        result
    }
}
```

---

### 2. Update Elaborator

**File:** `crates/hwml-elab/src/elab/mod.rs`

```rust
use crate::context::ElabContext;

pub struct Elaborator<'a, 'db> {
    pub kernel: Kernel<'a, 'db>,
    pub context: ElabContext<'db>,  // NEW!
}

impl<'a, 'db> Elaborator<'a, 'db> {
    pub fn new(
        global: &'a GlobalEnv<'db>,
        ctx: ElabCtx<'db>,
        state: &'a mut SolverState<'db>,
        resolver: &'a Resolver<'db>,
        stub_table: &'a StubTable<'db>,
        source: Source<'db>,  // NEW! Required parameter
    ) -> Self {
        Elaborator {
            kernel: Kernel::new(global, ctx, state, resolver, stub_table),
            context: ElabContext::new(source),  // NEW!
        }
    }
    
    // Error helpers will use context.current_location()
    pub fn error_not_in_scope(&self, name: String) -> ElabError<'db> {
        ElabError::NotInScope {
            name,
            span: self.context.current_location(),  // ✅ Real source!
            elab_backtrace: self.context.snapshot(),
        }
    }
    
    // ... other error helpers ...
}
```

---

### 3. Update File Elaboration Entry Points

**File:** `crates/hwml-elab/src/program.rs` or wherever files are elaborated

```rust
use hwml_core::{Source, SourceInfo, SourceFileId, Word};

/// Elaborate a file
pub fn elaborate_file<'db>(
    db: &'db dyn salsa::Database,
    library_name: &str,
    file_path: &str,
    file_content: &str,
    // ... other params
) -> Result<...> {
    // 1. Create Source for this file
    let lib_word = Word::new(db, library_name);
    let path_word = Word::new(db, file_path);
    let file_id = SourceFileId::new(db, lib_word, path_word);
    let source = Source::new(db, SourceInfo::File(file_id));
    
    // 2. Create elaborator with source
    let mut elab = Elaborator::new(
        global,
        ctx,
        state,
        resolver,
        stub_table,
        source,  // ✅ Pass source!
    );
    
    // 3. Add file-level trace frame
    let _file_guard = elab.context.trace(
        format!("elaborating file '{}'", file_path),
        0..file_content.len(),  // Whole file
        ElabFrameKind::ElaboratingFile { 
            path: file_path.to_string() 
        },
    );
    
    // 4. Elaborate definitions
    for def in definitions {
        elaborate_definition(db, &mut elab, def)?;
    }
    
    Ok(...)
}
```

---

### 4. Update Expression Elaboration

**File:** `crates/hwml-elab/src/elab/expr.rs`

**OLD CODE (Many instances like this):**
```rust
Expression::Universe(u) => {
    let word = Word::new(db, "universe");
    let source = Source::new(db, SourceInfo::Synthetic(word));  // ❌ REMOVE
    let span = SourceRange::new(source, u.loc.clone());
    elab.kernel.synth_universe(db, None, Some(span))
}
```

**NEW CODE:**
```rust
pub fn synth<'a, 'db, Db>(
    db: &'db Db,
    elab: &mut Elaborator<'a, 'db>,
    expr: &Expression,
) -> Result<Checked<(RcSyntax<'db>, RcTy<'db>)>, ElabError<'db>>
where
    Db: salsa::Database,
{
    // Add trace guard with byte range from expression
    let byte_range = expr_byte_range(expr);
    let _guard = elab.context.trace(
        "synthesizing type",
        byte_range,  // ✅ Uses current_source automatically!
        ElabFrameKind::SynthesizingType,
    );
    
    match expr {
        Expression::Universe(u) => {
            // Just use current location - no manual source creation!
            let span = elab.context.current_location();
            elab.kernel.synth_universe(db, None, span)
        },
        
        Expression::Id(id) => {
            // ... lookup logic ...
            
            // Error uses current location automatically
            Err(elab.error_not_in_scope(id.value.to_string()))
            // ^^^ This gets the real file source from context!
        },
        
        // ... other cases
    }
}
```

**Helper function:**
```rust
/// Extract byte range from surface expression
fn expr_byte_range(expr: &Expression) -> Range<usize> {
    match expr {
        Expression::Pi(x) => x.loc.clone(),
        Expression::Arrow(x) => x.loc.clone(),
        Expression::App(x) => x.loc.clone(),
        Expression::Id(x) => x.loc.clone(),
        Expression::Universe(x) => x.loc.clone(),
        // ... all other cases
        Expression::Paren(x) => expr_byte_range(&x.expr),  // Recurse for paren
        Expression::Match(x) => expr_byte_range(&x.scrutinee),
        Expression::Str(_) => 0..0,  // Synthetic
    }
}
```

---

### 5. Clean Up Synthetic Source Creation

**Search and destroy pattern:**

```bash
# Find all synthetic source creations
rg "Source::new.*Synthetic" crates/hwml-elab --type rust

# Replace each with current_location()
```

**Before:**
```rust
let word = Word::new(db, "description");
let source = Source::new(db, SourceInfo::Synthetic(word));
let span = SourceRange::new(source, range);
```

**After:**
```rust
// Just use trace guard or current_location()
let span = elab.context.current_location();
```

**Legitimate uses of Synthetic (keep these):**
- Compiler-generated code (type inference internals)
- Metaprogramming expansion
- Truly synthetic terms with no source location

---

## Implementation Checklist

### Day 1: Infrastructure

- [ ] **Task 1.1:** Create `context.rs`
  - [ ] Define `ElabContext` with `current_source` field
  - [ ] Implement `trace()` method (uses current source)
  - [ ] Implement `trace_with_source()` (for file boundaries)
  - [ ] Implement `current_location()` helper
  - [ ] Implement `with_source()` for temporary source changes
  - [ ] Add unit tests

- [ ] **Task 1.2:** Update `Elaborator`
  - [ ] Add `context: ElabContext<'db>` field
  - [ ] Update `new()` to take `source: Source<'db>` parameter
  - [ ] Fix compilation errors (all Elaborator::new call sites)

- [ ] **Task 1.3:** Add `expr_byte_range` helper
  - [ ] Create helper function in `elab/expr.rs`
  - [ ] Handle all expression variants
  - [ ] Add tests

**Estimated Time:** 4 hours

---

### Day 2: Integration

- [ ] **Task 2.1:** Update file elaboration entry points
  - [ ] `program.rs`: Create Source from file info
  - [ ] `scc_elab.rs`: Pass source to Elaborator
  - [ ] Any other file-level elaboration sites
  - [ ] Add file-level trace guards

- [ ] **Task 2.2:** Update `synth()` and `check()`
  - [ ] Add trace guards using `expr_byte_range`
  - [ ] Remove synthetic source creation
  - [ ] Use `elab.context.current_location()` for errors

- [ ] **Task 2.3:** Clean up synthetic sources
  - [ ] Search for `Source::new.*Synthetic` in elab code
  - [ ] Replace with `current_location()` where appropriate
  - [ ] Keep only legitimate synthetic cases

- [ ] **Task 2.4:** Fix definition elaboration
  - [ ] `elab/decl.rs`: Add trace guards with byte ranges
  - [ ] Pass source through to nested elaboration

**Estimated Time:** 4 hours

---

### Testing & Verification

- [ ] **Single-file error locations**
  ```rust
  #[test]
  fn test_error_shows_real_file() {
      let source = create_test_source(db, "test.hwml", "def foo: Nat = true");
      let err = elaborate(db, source).unwrap_err();
      
      match err {
          ElabError::TypeMismatch { span: Some(span), .. } => {
              assert_eq!(span.source.title(db), "/path/to/test.hwml");  // ✅ Real file!
              assert!(!span.source.title(db).contains("synthetic"));    // ✅ Not synthetic!
          }
          _ => panic!("Wrong error type"),
      }
  }
  ```

- [ ] **Backtrace shows file names**
  ```rust
  #[test]
  fn test_backtrace_has_file_info() {
      let err = elaborate_with_error(db, "test.hwml");
      
      match err {
          ElabError::NotInScope { elab_backtrace, .. } => {
              assert!(!elab_backtrace.is_empty());
              for frame in elab_backtrace {
                  // Every frame should have real file source
                  assert_eq!(frame.location.source.title(db), "/path/to/test.hwml");
              }
          }
          _ => panic!(),
      }
  }
  ```

- [ ] **Error display shows file path**
  ```rust
  #[test]
  fn test_display_includes_filename() {
      let err = elaborate_with_error(db, "main.hwml");
      let display = format!("{}", err);
      
      assert!(display.contains("main.hwml"));  // ✅ File in output
      assert!(!display.contains("synthetic")); // ✅ No synthetic
  }
  ```

**Estimated Time:** 2 hours

---

## Migration Strategy

### Incremental Approach

**Phase 1: Infrastructure (No Breakage)**
- Add `context` field to Elaborator with `source` parameter
- Update call sites to pass a default source initially
- System compiles and runs (no behavior change yet)

**Phase 2: Instrumentation (Gradual Improvement)**
- Add trace guards to `synth()`/`check()` one at a time
- Each guard starts using real source
- Test after each change

**Phase 3: Cleanup (Remove Dead Code)**
- Remove synthetic source creation
- Clean up temporary workarounds
- Final testing

---

## Cross-File Support (Future)

For imports/multi-file:

```rust
pub fn elaborate_import<'db>(
    db: &'db dyn salsa::Database,
    elab: &mut Elaborator<'db>,
    import_path: &str,
) -> Result<...> {
    // 1. Get source for imported file
    let imported_source = resolve_import_source(db, import_path)?;
    
    // 2. Temporarily switch source
    elab.context.with_source(imported_source, |ctx| {
        // 3. Elaborate imported definitions
        // Errors will now show the imported file's location!
        elaborate_imported_defs(db, elab)?;
    });
    
    // 4. Source automatically restored
    Ok(())
}
```

---

## Summary

**Timeline:** 1-2 days
- Day 1: Infrastructure (4h) + Integration (4h)
- Day 2: Testing (2h) + Buffer (2h)

**Files Changed:**
- `context.rs` (new, ~200 lines)
- `elab/mod.rs` (+5 lines for context field)
- `elab/expr.rs` (+30 lines for trace guards, -50 lines removing synthetic)
- `program.rs` or file entry points (+20 lines)
- Test files (+50 lines)

**Result:**
- ✅ All errors show real file paths
- ✅ Backtraces include file information
- ✅ Ready for multi-file diagnostics
- ✅ Foundation for Ariadne integration (Phase 5)

**Risk:** Low - incremental changes, compiler catches breaking changes

**Next:** Phase 4.1 (Infrastructure) builds on this foundation
