# HWML Elaborator Progress Report

**Date:** 2026-03-21  
**Status:** In Development - Core Infrastructure Complete

## Overview

The HWML elaborator translates surface syntax (human-readable code) into core syntax (machine-verifiable IR). The elaborator is currently in active development with foundational infrastructure in place.

## Architecture

The elaborator follows a three-phase design:

1. **Lowering & Scheduling (Async):** Translates surface AST into unresolved core IR with metavariables, spawning async unification tasks
2. **Zonking (Sync):** Replaces all solved metavariables with their definitive values
3. **Final Verification (Core):** Hands zonked AST to `hwml-core` typechecker for validation

## Completed Components

### 1. Unification Engine (`crates/hwml-elab/src/unify.rs`)
**Status:** ✅ Complete (~2,500 lines)

- **Pattern unification** with full support for:
  - Structural equality (constants, universes, primitives)
  - Injectivity rules (Pi, Lambda, TypeConstructor, DataConstructor)
  - Eta-expansion for Lambda and Module terms
  - Flex-flex intersection (Pientka's algorithm)
  - Flex-rigid solving with occurs check and scope checking
  - Lowering for flexible terms with non-empty spines
- **Hardware-specific unification:**
  - HArrow, Module, HApplication
  - Lift, SLift, MLift types
  - Bit, Zero, One values
- **Error handling:** Poisoned metavariables prevent error cascades
- **Comprehensive test suite:** 50+ tests covering all unification scenarios

### 2. Solver Infrastructure (`crates/hwml-elab/src/engine.rs`)
**Status:** ✅ Complete (~750 lines)

- **SolverEnvironment:** Manages metavariable state, type-checking context, and async task spawning
- **SolverState:** Tracks metavariable solutions, poisoned metas, and blocking relationships
- **SingleThreadedExecutor:** Runs async constraint solving tasks to completion or deadlock
- **TaskSpawner:** Spawns concurrent unification tasks
- **Metavariable management:** Fresh meta creation, solving, forcing, zonking

### 3. Zonking Pass (`crates/hwml-elab/src/zonk.rs`)
**Status:** ✅ Complete (~280 lines)

- Total, non-failable pass that replaces solved metavariables
- Handles unsolved and poisoned metavariables gracefully
- Caching to avoid redundant work
- Full structural recursion over all syntax forms

### 4. Expression Elaboration (`crates/hwml-elab/src/expr.rs`)
**Status:** 🚧 Partial (~120 lines)

**Implemented:**
- `check_expr`: Type-directed checking for expressions
- `synth_expr`: Type synthesis for expressions
- `check_fun`: Lambda/function elaboration with typed binders
- `synth_id`: Identifier synthesis
- `annotate`: Annotation-based synthesis

**Missing:**
- Let expressions
- Match expressions
- Application elaboration
- Pi type elaboration
- Hardware-specific constructs (HArrow, Module, etc.)
- Inductive type elaboration

### 5. LCF-Style Kernel (`crates/hwml-elab/src/kernel/`)
**Status:** 🚧 Partial

**Implemented Rules:**
- `annotate`: Type annotation
- `application`: Function application
- `lambda`: Lambda introduction
- `name`: Name resolution
- `pi`: Pi type formation
- `switch`: Bidirectional mode switching
- `decode`: (stub)

**Architecture:**
- `TrustedSyntax<'db>`: Newtype wrapper ensuring only kernel can construct core syntax
- `TrustedTypedSyntax<'db>`: Syntax with synthesized type
- Kernel rules are the only way to construct trusted syntax

### 6. Supporting Modules
**Status:** ✅ Complete

- **Renaming** (`renaming.rs`): Substitution inversion for pattern unification
- **Force** (`force.rs`): Weak-head normalization with metavariable forcing
- **Dubbing** (`dubbing.rs`): Maps user names to core terms
- **Diagnostics** (`diagnostic/`): Error reporting infrastructure
- **Stub Table** (`stub_table.rs`): Harvests declarations from surface syntax

## Integration Status

### CLI Integration (`crates/hwml/src/main.rs`)
**Status:** 🚧 Partial

**Surface Mode (Default):**
- ✅ Parses surface syntax
- ✅ Creates Salsa database
- ✅ Creates source file for location tracking
- 🚧 Elaborates definitions (basic synth_expr only)
- ❌ No full program elaboration
- ❌ No error reporting to user

**Core Mode (`--core` flag):**
- ✅ Parses core syntax modules
- ✅ Type-checks modules
- ✅ Displays parsed declarations
- ✅ CIRCT emission (MLIR/Verilog) with `--emit-mlir`/`--emit-verilog`

## Missing Components

### High Priority

1. **Full Expression Elaboration**
   - Let expressions
   - Match/case expressions  
   - Application with implicit arguments
   - Hardware constructs (HArrow, Module, HApplication)

2. **Statement Elaboration**
   - Top-level definitions
   - Inductive type declarations
   - Primitive declarations
   - Namespace management

3. **Program Elaboration**
   - Module-level elaboration
   - Dependency ordering
   - Mutual recursion support

4. **Error Reporting**
   - Rich diagnostics with source locations
   - Error recovery
   - Suggestions and fixes

### Medium Priority

5. **Instance Resolution**
   - Type class instances
   - Implicit argument solving

6. **Totality Checking**
   - Termination checking
   - Coverage checking for pattern matches

### Low Priority

7. **Optimization**
   - Constraint solving optimization
   - Incremental elaboration

## Testing Status

- ✅ Unification: 50+ unit tests
- ✅ Zonking: 3 unit tests
- ✅ Force: 5 unit tests
- 🚧 Expression elaboration: No tests yet
- ❌ Integration tests: None
- ❌ End-to-end tests: None

## Next Steps

1. **Complete expression elaboration** - Implement missing expression forms
2. **Add statement elaboration** - Handle top-level definitions and declarations
3. **Integrate with CLI** - Wire up full elaboration pipeline in hwml CLI
4. **Add comprehensive tests** - Integration and end-to-end testing
5. **Implement error reporting** - Rich diagnostics with source locations

## References

- Design document: `design/elaboration.md`
- Implementation plan: `design/implementation-plan-lcf.md`
- System context: `docs/system-context-report.md`

