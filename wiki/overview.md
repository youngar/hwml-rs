# HWML Overview

**Last Updated:** 2026-05-02  
**Type:** Synthesis  
**Purpose:** High-level introduction to HWML for new contributors and stakeholders

---

## What is HWML?

HWML is an **in-development hardware description language** with a powerful metaprogramming layer based on dependent types. It aims to bring the precision of formal verification and the expressiveness of modern type theory to hardware design.

### Key Features

1. **Dependent Types** - Use types that depend on values to ensure hardware correctness at compile time
2. **Staged Metaprogramming** - Generate hardware at compile time using the same language
3. **Type-Safe Hardware** - Catch errors before synthesis that other HDLs only find during simulation
4. **CIRCT Backend** - Compile to Verilog via MLIR/CIRCT for industry-standard toolchain integration

### Example

```hwml
meta def option.map (f : ^a -> ^b) (x : ^(option a)) : ^(option b) :=
  [
    x match {
      | some v => f v
      | none   => none
    }
  ]
```

This shows HWML's meta-level programming: compile-time functions that generate hardware.

---

## Architecture

### Three-Layer Design

HWML follows a classic compiler architecture with a trusted kernel:

```
┌─────────────────────────────────────────┐
│  Surface Language (hwml-surface)        │ ← What users write
│  - User-friendly syntax                  │
│  - Pattern matching                      │
│  - Type inference                        │
└─────────────────────────────────────────┘
                ↓ elaboration
┌─────────────────────────────────────────┐
│  Core Language (hwml-core)              │ ← Internal representation
│  - Simple, primitive constructs          │
│  - De Bruijn indices                     │
│  - Fully type-annotated                  │
└─────────────────────────────────────────┘
                ↓ evaluation/quotation
┌─────────────────────────────────────────┐
│  Semantic Domain (NbE)                  │ ← Runtime values
│  - Normalization by Evaluation           │
│  - Type checking                         │
│  - Unification                           │
└─────────────────────────────────────────┘
```

**Key Insight:** The core language has a [[components/kernel|trusted kernel]] that enforces type safety. Only the kernel can construct well-typed terms.

---

## Core Concepts

### Dependent Types
Types can depend on values. Example: `Vec A n` is a vector of `A` elements with length `n`, where `n` is a value, not a type.

### Bidirectional Typing
The type checker operates in two modes:
- **Check mode (⇐):** Given a type, verify a term has that type
- **Synth mode (⇒):** Given a term, synthesize its type

See: [[entities/bidirectional-typing]]

### Normalization by Evaluation (NbE)
Terms are evaluated to semantic values and quoted back to normalized syntax. This enables efficient type checking and comparison.

See: [[entities/nbe]]

### LCF-Style Kernel
Only the kernel module can construct typed terms. This creates a small trusted computing base for type safety.

See: [[decisions/ADR-001-lcf-kernel]], [[entities/lcf-pattern]]

---

## Major Components

### [[components/kernel|Kernel]] (hwml-core)
The trusted core that enforces type safety through bidirectional typing rules.

### [[components/elaborator|Elaborator]] (hwml-elab)
Transforms surface syntax to core language:
- Name resolution
- Type inference
- Implicit argument insertion
- Pattern matching compilation
- Metavariable solving

### [[components/package-manager|Package Manager]] (hwml-workspace)
Multi-library compilation with:
- Dependency resolution (MVS)
- Compilation caching (.hwmli artifacts)
- Content-addressed storage

### Surface Parser (hwml-surface)
LALRPOP-based parser for user-facing syntax.

### CIRCT Backend (hwml-circt)
Compiles elaborated hardware to Verilog via MLIR/CIRCT.

---

## Design Principles

### Type Safety First
**Decision:** [[decisions/ADR-001-lcf-kernel]]  
Type safety is enforced at compile time by Rust's type system. Impossible to construct ill-typed terms.

### Reproducible Builds
**Decision:** [[decisions/ADR-004-mvs-package-manager]], [[decisions/ADR-005-content-addressed-artifacts]]  
Builds are deterministic and reproducible across machines.

### Staged Computation
Hardware generation happens at compile time (meta-level), hardware execution happens at runtime (object-level).

### Async Elaboration
**Decision:** [[decisions/ADR-003-async-elaboration]]  
Type checking can await on unsolved metavariables, enabling cooperative constraint solving.

---

## Implementation Status

**Current Phase:** 1.5 (See [[research/implementation-phases]])

- [x] **Phase 1 Complete:** Core kernel, NbE, basic elaboration
- [/] **Phase 1.5 In Progress:** LET expressions, improved elaboration
- [ ] **Phase 2 Planned:** Multi-file compilation, package manager
- [ ] **Phase 3 Planned:** Full CIRCT integration, LSP server

---

## Key Technologies

### Language & Tools
- **Rust** - Implementation language (type safety, performance)
- **Salsa** - Incremental computation framework
- **LALRPOP** - Parser generator for surface syntax
- **CIRCT/MLIR** - Backend for Verilog generation

### Theoretical Foundations
- **Dependent Type Theory** - Foundation for type system
- **Bidirectional Typing** - Type checking algorithm
- **Normalization by Evaluation** - Efficient term normalization
- **LCF Architecture** - Trusted kernel pattern from theorem provers

See: [[research/type-theory-foundations]]

---

## Getting Started

### For New Contributors
1. Read this overview
2. Follow [[onboarding/new-contributor-guide]]
3. Explore [[onboarding/codebase-map]]
4. Pick a component to dive deep

### For Understanding the Type System
1. Read [[entities/bidirectional-typing]]
2. Read [[entities/nbe]]
3. Study [[decisions/ADR-001-lcf-kernel]]
4. Explore [[components/kernel]]

### For Contributing to Implementation
1. Check [[onboarding/contributing-to-elaborator]]
2. Review current [[research/implementation-phases|implementation phase]]
3. Look at open issues in relevant component

---

## Related Documents

- **Architecture:** `design/ARCHITECTURE.md`
- **Package Manager:** `design/package-manager.md`
- **Language Design:** `design/hwml.md`
- **Core Decisions:** See [[decisions/]] directory

---

## Questions?

Common questions are answered in component and entity pages. For specific topics:
- Type system: [[entities/bidirectional-typing]], [[entities/nbe]]
- Architecture: [[decisions/ADR-001-lcf-kernel]]
- Package management: [[decisions/ADR-004-mvs-package-manager]]
- Implementation: [[components/]] directory
