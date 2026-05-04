# Implementation Guides

This directory contains **detailed implementation guides** that translate architectural decisions (ADRs) into concrete, actionable development plans.

---

## Purpose

While `wiki/decisions/` contains **architectural decisions** (the "what" and "why"), this directory contains **implementation plans** (the "how"):

- **ADRs** are relatively stable, document architectural choices
- **Implementation Guides** are working documents with detailed code examples, migration steps, and task breakdowns

---

## Structure

```
implementation/
├── vfs/                          # VFS implementation guides
│   ├── quickstart.md            # Quick reference for developers
│   ├── phase1-fix-anti-pattern.md
│   ├── phase2-vfs-foundation.md
│   ├── phase3-migration.md
│   └── phase4-5-testing-lsp.md
└── (future implementation guides)
```

---

## Current Implementation Guides

### VFS (Virtual File System)

**Related ADR:** [[decisions/ADR-008-vfs-abstraction]]  
**High-level Plan:** [[VFS-IMPLEMENTATION-PLAN]]  
**Review Summary:** [[VFS-REVIEW-SUMMARY]]

Detailed implementation guides for building a Salsa-native VFS:
- [[implementation/vfs/quickstart]] - Quick start guide
- [[implementation/vfs/phase1-fix-anti-pattern]] - Fix critical database anti-pattern
- [[implementation/vfs/phase2-vfs-foundation]] - Create VFS trait and implementations
- [[implementation/vfs/phase3-migration]] - Migrate existing code
- [[implementation/vfs/phase4-5-testing-lsp]] - Testing infrastructure and LSP integration

---

## How to Use

1. **Start with the ADR** in `wiki/decisions/` to understand the architectural decision
2. **Read the high-level plan** in `wiki/` (e.g., `VFS-IMPLEMENTATION-PLAN.md`)
3. **Follow the phase guides** in this directory for detailed code examples
4. **Use the quickstart** for quick reference during development

---

## Contributing Implementation Guides

When creating new implementation guides:

1. **Keep ADRs separate**: Architectural decisions go in `wiki/decisions/`
2. **Create a top-level plan**: High-level plans go in `wiki/` (use `UPPERCASE-NAMES.md`)
3. **Add detailed guides here**: Phase-by-phase implementation with code examples
4. **Link everything**: Use wiki-style links to connect ADRs, plans, and implementation guides

**Example structure for a new feature:**
```
wiki/
├── MY-FEATURE-IMPLEMENTATION-PLAN.md    # High-level plan
├── decisions/
│   └── ADR-XXX-my-feature.md            # Architectural decision
└── implementation/
    └── my-feature/
        ├── quickstart.md
        ├── phase1-foundation.md
        └── phase2-integration.md
```
