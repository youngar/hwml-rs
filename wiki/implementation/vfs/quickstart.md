# VFS Implementation Quickstart

**For developers ready to start implementing the VFS**
**Related:** [[VFS-IMPLEMENTATION-PLAN]], [[VFS-REVIEW-SUMMARY]]

---

## TL;DR

Your ADR is ⭐ **excellent**, but the current code has a **critical anti-pattern** that will break LSP. Follow this 5-phase plan to fix it.

**Time:** 12-17 days | **Complexity:** Medium | **Impact:** High

---

## Phase Overview

```
Phase 1 (2-3 days) 🔥 CRITICAL
├─ Fix anti-pattern (files DashMap outside DB)
└─ Add set_text() for LSP

Phase 2 (2-3 days) ⚙️ FOUNDATION  
├─ Create hwml-vfs crate
└─ Implement OsVfs, MemoryVfs

Phase 3 (3-4 days) 🔄 MIGRATION
├─ Update CLI
└─ Migrate all parsers

Phase 4 (2-3 days) ✅ TESTING
├─ Fast hermetic tests
└─ Verify invalidation

Phase 5 (3-4 days) 🚀 LSP
├─ Implement LspVfs
└─ Wire up didChange events
```

---

## Quick Start (Phase 1)

### Step 1: Rename File → SourceFile

**File:** `crates/hwml-db/src/db.rs`

```rust
// Change this:
#[salsa::input]
pub struct File {
    pub text: String,
}

// To this:
#[salsa::input]
pub struct SourceFile {
    #[return_ref]
    pub path: PathBuf,
    
    #[return_ref]
    pub text: String,
}
```

### Step 2: Remove files from Database

```rust
// Change this:
#[salsa::db]
pub struct HwmlDatabase {
    storage: salsa::Storage<Self>,
    files: DashMap<PathBuf, File>,  // ❌ DELETE THIS
    logs: Arc<Mutex<Option<Vec<String>>>>,
}

// To this:
#[salsa::db]
pub struct HwmlDatabase {
    storage: salsa::Storage<Self>,
    // files removed! ✅
    logs: Arc<Mutex<Option<Vec<String>>>>,
}
```

### Step 3: Create CompilerSession

**Create:** `crates/hwml-db/src/session.rs`

```rust
use dashmap::{DashMap, Entry};
use std::path::{Path, PathBuf};
use crate::db::{HwmlDatabase, SourceFile};

pub struct CompilerSession {
    pub db: HwmlDatabase,
    file_cache: DashMap<PathBuf, SourceFile>,  // NOW OUTSIDE DB!
}

impl CompilerSession {
    pub fn new() -> Self {
        Self {
            db: HwmlDatabase::new(),
            file_cache: DashMap::new(),
        }
    }
    
    pub fn get_or_load_file(&self, path: &Path) -> Result<SourceFile, std::io::Error> {
        let canonical = path.canonicalize()?;
        
        Ok(match self.file_cache.entry(canonical.clone()) {
            Entry::Occupied(e) => *e.get(),
            Entry::Vacant(e) => {
                let text = std::fs::read_to_string(&canonical)?;
                let file = SourceFile::new(&self.db, canonical, text);
                *e.insert(file)
            }
        })
    }
    
    pub fn update_file(&mut self, path: &Path, new_text: String) -> Result<(), std::io::Error> {
        let canonical = path.canonicalize()?;
        
        if let Some(file) = self.file_cache.get(&canonical) {
            file.set_text(&mut self.db).to(new_text);  // 🔥 KEY LINE
        } else {
            let file = SourceFile::new(&mut self.db, canonical.clone(), new_text);
            self.file_cache.insert(canonical, file);
        }
        
        Ok(())
    }
}
```

### Step 4: Update lib.rs

```rust
// crates/hwml-db/src/lib.rs
pub mod db;
pub mod ir;
pub mod session;  // ADD THIS

pub use session::CompilerSession;
```

**That's it for Phase 1!** Run `cargo build -p hwml-db` to verify.

---

## Verification

After each phase, run:

```bash
# Phase 1
cargo build -p hwml-db
cargo test -p hwml-db

# Phase 2
cargo build -p hwml-vfs
cargo test -p hwml-vfs

# Phase 3
cargo build
cargo run -- -f examples/test.hwml

# Phase 4
cargo test --workspace
# Should be 2-5x faster!

# Phase 5
cargo run -p hwml-lsp-server
# Test in VSCode
```

---

## Common Pitfalls

### ❌ Don't: Store VFS inside database
```rust
pub struct HwmlDatabase {
    vfs: Arc<RwLock<Vfs>>,  // BREAKS SALSA!
}
```

### ✅ Do: Store VFS outside, feed Salsa inputs
```rust
pub struct CompilerSession {
    db: HwmlDatabase,
    vfs: Box<dyn Vfs>,  // CORRECT!
}
```

### ❌ Don't: Forget #[return_ref]
```rust
#[salsa::input]
pub struct SourceFile {
    pub text: String,  // Clones on every access!
}
```

### ✅ Do: Use #[return_ref] for strings
```rust
#[salsa::input]
pub struct SourceFile {
    #[return_ref]
    pub text: String,  // Returns &String!
}
```

---

## Resources

- **Full Plan:** [[VFS-IMPLEMENTATION-PLAN]]
- **Phase 1 Code:** [[implementation/vfs/phase1-fix-anti-pattern]]
- **Phase 2 Code:** [[implementation/vfs/phase2-vfs-foundation]]
- **Phase 3 Code:** [[implementation/vfs/phase3-migration]]
- **Phase 4-5 Code:** [[implementation/vfs/phase4-5-testing-lsp]]
- **Review Summary:** [[VFS-REVIEW-SUMMARY]]
- **Original ADR:** [[decisions/ADR-008-vfs-abstraction]]

---

## Getting Help

**Questions about:**
- Salsa integration → See ADR-008 lines 36-48 (critical pattern)
- VFS trait design → See ADR-008 lines 362-381
- LSP integration → See ADR-008 lines 447-520
- Incremental compilation → See Phase 4 examples

**Still stuck?** The ADR has complete implementations for all three VFS variants!
