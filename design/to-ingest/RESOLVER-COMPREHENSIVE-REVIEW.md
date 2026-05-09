# Comprehensive Review: Resolver Usage in Elaboration

## Executive Summary

**Issue**: When elaborating definitions, if something is not resolved to a local variable, we must use the resolver to look it up. The resolver is correctly updated when entering namespaces or lexical scopes and when processing `open` statements during inductive definition elaboration, but **NOT** during regular constant (def) elaboration.

## Architecture Overview

### Key Components

1. **`Resolver<'db>`** (`crates/hwml-elab/src/resolver.rs`)
   - Tracks current namespace: `Option<QualifiedName<'db>>`
   - Stack of scopes (outermost to innermost): `Vec<Scope<'db>>`
   - Two scope types:
     - `Scope::Lexical(LexicalScope)`: Open statements without namespace
     - `Scope::Namespace(QualifiedName, LexicalScope)`: New namespace + opens

2. **`resolve_path()`** function
   - Takes: `db`, `stub_table`, `resolver`, `path: &[Name]`
   - Returns: `Vec<QualifiedName>` of all matching qualified names in scope
   - Algorithm: Walks scopes from innermost to outermost, trying:
     1. Namespace qualification (if in namespace scope)
     2. Each open directive's alias rewriting
     3. Returns first scope that yields candidates

3. **`Kernel::synth_global_by_path()`** 
   - Entry point for global name lookup
   - Calls `resolve_path()` using `self.resolver`
   - Handles ambiguity and lookup errors

4. **Expression elaboration** (`crates/hwml-elab/src/elab/expr.rs`)
   - `synth()` for identifiers:
     1. Try local context lookup
     2. If not found, try `kernel.synth_global_by_path()` with current resolver
     3. Handle dotted identifiers

## Current Resolver Usage Patterns

### ✅ CORRECT: Inductive Definitions

**Location**: `crates/hwml-elab/src/elab/decl.rs:191-291` (`elab_inductive_impl`)

```rust
// Push a namespace scope for the inductive type
let ind_resolver = elab.kernel.resolver.push_namespace(db, &ind_path);

// Elaborate parameters in the inductive's namespace
let (params, param_ctx) = {
    let mut inner = Elaborator {
        kernel: Kernel::new(
            elab.kernel.global,
            elab.kernel.ctx.clone(),
            elab.kernel.state,
            &ind_resolver,  // ✅ Uses updated resolver!
            elab.kernel.stub_table,
        ),
    };
    elab_telescope(db, &mut inner, &ind.parameters.groups)?
};

// Elaborate indices in extended context (still in inductive's namespace)
let (indices, _idx_ctx) = {
    let mut inner = Elaborator {
        kernel: Kernel::new(
            elab.kernel.global,
            param_ctx.clone(),
            elab.kernel.state,
            &ind_resolver,  // ✅ Uses updated resolver!
            elab.kernel.stub_table,
        ),
    };
    elab_telescope(db, &mut inner, &ind.indices.groups)?
};

// Similar for universe and constructors...
```

**Why this works**: The inductive's namespace is pushed onto the resolver, so when elaborating parameters, indices, universe, and constructor types, any identifiers are resolved in the context of that namespace.

### ❌ PROBLEM: Regular Constants (def)

**Location**: `crates/hwml-elab/src/elab/decl.rs:87-161` (`elab_constant_impl`)

```rust
fn elab_constant_impl<'a, 'db, Db>(
    db: &'db Db,
    elab: &mut Elaborator<'a, 'db>,
    def: &Def,
    lenient: bool,
) -> Result<ElaboratedConstant<'db>, ElabError<'db>>
where
    Db: salsa::Database,
{
    let name = def.id.value.to_vec();

    // Build type and value directly using `elab` parameter
    let (ty_syn, value_syn) = if def.bindings.groups.is_empty() {
        // ... elaborate type and value ...
        let ty_syn = /* ... */;
        let val_syn = elab::expr::check(db, elab, &def.value, /* ... */)?;
        (ty_syn, val_syn)
    } else {
        // ... elaborate with bindings ...
    };
    
    // ❌ Problem: `elab` uses the CALLER's resolver throughout!
    // No namespace is pushed for the constant's body
```

**Why this is broken**: Constants are top-level declarations that should have their own namespace context (similar to inductives), but the code doesn't push any namespace scope before elaborating the type or value.

## Lexical Scope Updates

### ✅ Pi Binders / Arrow / Let

**Locations**:
- `crates/hwml-elab/src/elab/expr.rs:255-302` (synth_pi_binders)
- `crates/hwml-elab/src/elab/expr.rs:306-336` (synth_arrow)
- `crates/hwml-elab/src/elab/expr.rs:340-380` (synth_let_in)

```rust
// Example from synth_pi_binders
let ext_ctx = elab.kernel.ctx.push_bound(name, dom_ty, var);

let cod_checked = {
    let mut inner = Elaborator {
        kernel: Kernel {
            global: elab.kernel.global,
            ctx: ext_ctx,              // ✅ Extended ElabCtx
            state: elab.kernel.state,
            resolver: elab.kernel.resolver,  // ⚠️ Same resolver (OK for binders)
            stub_table: elab.kernel.stub_table,
        },
    };
    synth_pi_binders(db, &mut inner, &binders[1..], ...)
};
```

**Analysis**: This is correct for lexical binders because:
1. The `ElabCtx` is extended with the new binding
2. Name lookup tries local context FIRST (line 92 in `elab/expr.rs`)
3. Only if not found locally does it try global resolution via resolver

**The resolver doesn't need to change** for lambda/pi/let binders because these are purely local bindings.

## Resolution Flow

### Current Name Resolution Algorithm (in `synth()` for identifiers)

```rust
Expression::Id(id) => {
    let name = String::from_utf8_lossy(&id.value).to_string();

    // STEP 1: Try local context first
    if let Some((idx, _)) = elab.kernel.ctx.lookup(&name) {
        return elab.kernel.synth_var(idx);  // ✅ Found locally
    }

    // STEP 2: Try global resolution
    let path = bytes_to_path(db, &id.value);
    match elab.kernel.synth_global_by_path(db, &path) {
        Ok(result) => return Ok(result),  // ✅ Found globally via resolver
        Err(_) => {}
    }

    // STEP 3: Error - not found
    Err(ElabError::NotInScope { name, span: None })
}
```

### `Kernel::synth_global_by_path()` flow

```rust
pub fn synth_global_by_path<Db>(&self, db: &'db Db, path: &[Name<'db>])
    -> Result<Checked<(RcSyntax<'db>, RcTy<'db>)>, ElabError<'db>>
{
    // Use resolver to find all matching qualified names in scope
    let candidates = resolve_path(db, self.stub_table, self.resolver, path);

    if candidates.is_empty() {
        return Err(ElabError::NotInScope { ... });
    }

    if candidates.len() > 1 {
        return Err(ElabError::NotInScope { name: "Ambiguous", ... });
    }

    let qname = candidates[0];

    // Look up in stub table, then synthesize based on kind
    // (Constant, Primitive, TypeConstructor, DataConstructor)
}
```

## The Core Issue

**Problem Statement**: When elaborating a constant definition body, the resolver is not updated to reflect the constant's namespace context. This means:

1. ❌ References to names in the same namespace require full qualification
2. ❌ `open` statements in the constant's scope are not processed
3. ❌ The constant cannot have its own namespace-local opens

**Example**:
```hwml
namespace Foo {
  def helper : Type = ...

  def myFunc : Type = helper  -- ❌ Might fail, needs Foo.helper
}
```

In contrast, inductive definitions work correctly:
```hwml
namespace Foo {
  inductive MyType : Type {
    constructor : helper -> MyType  -- ✅ Works, resolves to Foo.helper
  }
}
```

## Where Resolver Updates Are Needed

### Current State

| Context | Resolver Updated? | ElabCtx Updated? | Notes |
|---------|------------------|------------------|-------|
| Inductive params | ✅ Yes (namespace) | ✅ Yes (telescope) | Correct |
| Inductive indices | ✅ Yes (namespace) | ✅ Yes (telescope) | Correct |
| Inductive constructors | ✅ Yes (namespace) | ✅ Yes (params) | Correct |
| **Constant type** | ❌ No | ❌ No | **BUG** |
| **Constant value** | ❌ No | ✅ Yes (bindings) | **BUG** |
| Pi binder bodies | ⚠️ No (not needed) | ✅ Yes | Correct - local only |
| Arrow codomain | ⚠️ No (not needed) | ✅ Yes | Correct - local only |
| Let-in body | ⚠️ No (not needed) | ✅ Yes | Correct - local only |

## Proposed Fix

Constants should follow the same pattern as inductives:

```rust
fn elab_constant_impl<'a, 'db, Db>(
    db: &'db Db,
    elab: &mut Elaborator<'a, 'db>,
    def: &Def,
    lenient: bool,
) -> Result<ElaboratedConstant<'db>, ElabError<'db>>
{
    let name = def.id.value.to_vec();

    // NEW: Push a namespace scope for the constant
    let const_path = util::surface_id_to_path(db, &def.id)
        .ok_or(ElabError::NotInScope { ... })?;
    let const_resolver = elab.kernel.resolver.push_namespace(db, &const_path);

    // Elaborate type and value using the updated resolver
    let (ty_syn, value_syn) = if def.bindings.groups.is_empty() {
        let mut inner = Elaborator::new(
            elab.kernel.global,
            ElabCtx::empty(),
            elab.kernel.state,
            &const_resolver,  // ✅ Use updated resolver
            elab.kernel.stub_table,
        );
        // ... elaborate with inner ...
    } else {
        // Similar for functions with bindings
    };
}
```

## Additional Considerations

1. **Lexical scopes for `open`**: If constants can have `open` statements in their bodies (like in a let-in or do-block), we'd need `resolver.push_scope()` as well.

2. **Namespace vs Lexical**:
   - `push_namespace()` creates a new namespace and implicitly opens it
   - `push_scope()` creates a new lexical scope without changing namespace
   - Constants likely need `push_namespace()` since they're top-level declarations

3. **SCC elaboration**: The fix also applies to `crates/hwml-elab/src/scc_elab.rs` where constants are elaborated in Phase 3.

## Critical Observation: The Call Site

Looking at `elab_def_statement` in `crates/hwml-elab/src/program.rs:276-308`:

```rust
fn elab_def_statement<'db, Db>(
    db: &'db Db,
    global: &mut GlobalEnv<'db>,
    def: &hwml_surface::Def,
    resolver: &Resolver<'db>,  // ⚠️ Resolver passed from caller
    stub_table: &StubTable<'db>,
    decls: &mut Vec<ElaboratedDecl<'db>>,
    errors: &mut Vec<ElabError<'db>>,
) {
    let qname = bytes_to_simple_qname(db, resolver.namespace(), &def.id.value);

    let result: Result<ConstantInfo<'db>, ElabError<'db>> = {
        let mut state = SolverState::new();
        // ❌ BUG: Passes resolver directly without pushing namespace
        let mut elab = Elaborator::new(global, ElabCtx::empty(), &mut state, resolver, stub_table);
        elab::decl::elab_constant(db, &mut elab, def).and_then(|elaborated| {
            // ...
        })
    };
}
```

The bug exists at **TWO** levels:

1. **`elab_def_statement`** doesn't push the constant's namespace before creating the `Elaborator`
2. **`elab_constant_impl`** doesn't push the constant's namespace either

Compare with inductive elaboration in `elab_inductive_statement` (lines 310-450):

```rust
fn elab_inductive_statement<'db, Db>(
    db: &'db Db,
    global: &mut GlobalEnv<'db>,
    ind: &hwml_surface::Inductive,
    resolver: &Resolver<'db>,
    stub_table: &StubTable<'db>,
    decls: &mut Vec<ElaboratedDecl<'db>>,
    errors: &mut Vec<ElabError<'db>>,
) {
    // ✅ Push namespace BEFORE creating elaborator
    let ind_path = util::surface_id_to_path(db, &ind.name).ok_or(...)?;
    let ind_resolver = resolver.push_namespace(db, &ind_path);

    // Phase 1: Elaborate header with updated resolver
    let header_result: Result<...> = {
        let mut header_state = SolverState::new();
        let mut elab = Elaborator::new(
            global,
            ElabCtx::empty(),
            &mut header_state,
            &ind_resolver,  // ✅ Uses updated resolver
            stub_table,
        );
        // ...
    };
}
```

## Conclusion

The resolver is correctly threaded through inductive elaboration (parameters, indices, constructors) but NOT through constant elaboration. The fix is to push a namespace scope before elaborating constant types and values, matching the pattern used for inductives.

**The fix must be applied at the call site** (`elab_def_statement`) to match how `elab_inductive_statement` works.
