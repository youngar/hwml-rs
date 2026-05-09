# Provenance Tracking Architecture Diagram

## System Overview

```
┌─────────────────────────────────────────────────────────────────────┐
│                        ELABORATOR                                   │
│                                                                     │
│  ┌──────────────┐                                                  │
│  │ synth_expr() │                                                  │
│  │   (Phase 1)  │                                                  │
│  └──────┬───────┘                                                  │
│         │ creates meta with origin                                │
│         ▼                                                          │
│  ┌─────────────────────────────────────────────────────┐          │
│  │  SolverState::fresh_meta_with_trace()               │          │
│  │                                                     │          │
│  │  1. Create MetaEntry (unchanged, 40 bytes)          │          │
│  │  2. Store MetaProvenance in side-table              │          │
│  │  3. Emit Trace constraint (Phase 2)                 │          │
│  └─────────────────────────────────────────────────────┘          │
│         │                                                          │
│         │ stores in two places                                    │
│         ▼                                                          │
└─────────────────────────────────────────────────────────────────────┘
         │
         │
    ┌────┴─────┐
    │          │
    ▼          ▼
┌────────────────────────┐     ┌──────────────────────────────┐
│  metas: HashMap        │     │  meta_provenance: HashMap    │
│  MetaId → MetaEntry    │     │  MetaId → MetaProvenance     │
├────────────────────────┤     ├──────────────────────────────┤
│ ?0 → Entry {           │     │ ?0 → Provenance {            │
│   id: 0                │     │   created_at: loc,           │
│   ty: Type             │     │   origin: UnderscoreExpr,    │
│   arity: 0             │     │   timestamp: 0,              │
│   solution: None       │     │   parent: None               │
│   kind: Term           │     │ }                            │
│ }                      │     │                              │
│                        │     │ ?1 → Provenance { ... }      │
│ ?1 → Entry { ... }     │     │                              │
└────────────────────────┘     └──────────────────────────────┘
         │                                   │
         │                                   │
         │ Success case:                    │ Error case:
         │ Meta solves → no lookup          │ Query provenance
         ▼                                   ▼
   ┌──────────────┐                  ┌─────────────────────┐
   │ All metas    │                  │ diagnostics.rs      │
   │ solved       │                  │ render_unsolved()   │
   │ → Ship it!   │                  │                     │
   └──────────────┘                  │ Uses provenance to  │
                                     │ build Ariadne       │
                                     │ multi-span report   │
                                     └─────────────────────┘
                                              │
                                              ▼
                                     ┌─────────────────────┐
                                     │ Beautiful Error:    │
                                     │                     │
                                     │ error: ?0 unsolved  │
                                     │   ┌─ example:12:15  │
                                     │   │                 │
                                     │ 12│  let x = _      │
                                     │   │          ^      │
                                     │   = note: created   │
                                     │     for underscore  │
                                     └─────────────────────┘
```

## Data Flow: Meta Creation → Error Reporting

```
User Code                    Elaborator                    SolverState
─────────                    ──────────                    ───────────

let x = _    ──parse──>  synth_underscore()
                              │
                              │ span = SourceRange(12:15)
                              │ origin = UnderscoreExpr
                              │
                              ▼
                         fresh_meta_with_trace(
                           ty, arity, kind,
                           origin, location, parent
                         )
                              │
                              ├─────────────────┐
                              │                 │
                              ▼                 ▼
                         metas.insert()    meta_provenance.insert()
                         MetaEntry         MetaProvenance {
                         {                   created_at: SourceRange(12:15),
                           id: ?0,           origin: UnderscoreExpr { ... },
                           ty: _,            timestamp: 0,
                           arity: 0,         parent: None
                           solution: None  }
                         }
                              │
                              ▼
                         emit_trace(
                           TraceEntry {
                             kind: MetaCreated { ?0, origin },
                             location,
                             timestamp
                           }
                         )
                              │
                              ▼
                         constraints.insert(
                           ConstraintEntry {
                             constraint: Trace(...),
                             status: Solved  ← Never processed
                           }
                         )
```

## Phase Evolution

### Phase 1: Side-Table Only

```
MetaEntry (unchanged)          MetaProvenance (new side-table)
┌──────────────────┐          ┌────────────────────────────┐
│ id: MetaId       │          │ created_at: SourceRange    │
│ ty: Type         │          │ origin: String             │
│ arity: usize     │          │ timestamp: usize           │
│ solution: Option │          └────────────────────────────┘
│ kind: MetaKind   │
└──────────────────┘
```

### Phase 2-3: Rich Origins

```
MetaEntry (unchanged)          MetaProvenance (enhanced)
┌──────────────────┐          ┌─────────────────────────────────┐
│ id: MetaId       │          │ created_at: SourceRange         │
│ ty: Type         │          │ origin: MetaOrigin<'db>         │
│ arity: usize     │          │   ├─ UnderscoreExpr { span }    │
│ solution: Option │          │   ├─ ImplicitArgument { ... }   │
│ kind: MetaKind   │          │   └─ DotResolution { ... }      │
└──────────────────┘          │ timestamp: usize                │
                              │ parent: Option<MetaId>          │
                              └─────────────────────────────────┘
```

### Phase 4: Constraint Provenance

```
ConstraintEntry (enhanced)
┌───────────────────────────────────┐
│ id: ConstraintId                  │
│ constraint: Constraint            │
│ status: ConstraintStatus          │
│ created_at: SourceRange    ← NEW  │
│ origin: ConstraintOrigin   ← NEW  │
│   ├─ FunctionApplication          │
│   ├─ TypeAnnotation               │
│   └─ Decomposition                │
└───────────────────────────────────┘
```

## Memory Layout Comparison

### Before (Current)
```
Per Metavariable: 40 bytes
Total for 1000 metas: 40 KB
```

### After Phase 1 (Side-table)
```
Success case (all metas solve):
  MetaEntry: 40 bytes
  MetaProvenance: 0 bytes (GC'd when meta solves)
  TraceEntry: 64 bytes (stored as constraint)
  Total per meta: 104 bytes
  Total for 1000 metas: 104 KB

Error case (10 unsolved metas):
  990 solved × 40 bytes = 39.6 KB
  10 unsolved × (40 + 80) bytes = 1.2 KB
  Trace constraints: ~64 KB
  Total: ~105 KB
```

**Overhead:** ~2.6x memory, but only trace persists after solving.

---

## Provenance Query Flow (Error Case)

```
User elaborates file
        ↓
Solver runs, some metas unsolved
        ↓
Report errors
        ↓
   ┌────────────────────┐
   │ ElabError::        │
   │ UnsolvedMeta { ?0 }│
   └────────┬───────────┘
            │
            ▼
   ┌─────────────────────────────┐
   │ error.render(db, state)     │
   │   ↓                         │
   │ render_unsolved_meta_error()│
   └────────┬────────────────────┘
            │
            ├─→ state.provenance(?0)
            │     ↓
            │   MetaProvenance {
            │     created_at: SourceRange,
            │     origin: UnderscoreExpr { span }
            │   }
            │
            ├─→ state.constraints_involving(?0)
            │     ↓
            │   [ (c5, origin: FunctionApp),
            │     (c7, origin: TypeAnnotation) ]
            │
            ▼
   ┌──────────────────────────────┐
   │ Ariadne Report               │
   │   Primary: created_at        │
   │   Secondary: origin.span     │
   │   Notes: constraint origins  │
   └──────────────────────────────┘
```

---

**Key Architectural Principles:**

1. **Separation of Concerns:** Core solver data (MetaEntry) vs error reporting (MetaProvenance)
2. **Pay for What You Use:** Side-table only populated when provenance needed
3. **Incremental Migration:** Each phase adds value independently
4. **Zero Abstraction Cost:** No runtime overhead on success path
5. **Rich When Needed:** Full context available for error reporting
