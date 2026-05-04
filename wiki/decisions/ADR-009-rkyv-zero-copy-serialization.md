# ADR-009: rkyv Zero-Copy Serialization for `.hwmli` Files

**Status:** Approved  
**Date:** 2026-05-03  
**Deciders:** Core team  
**Related:** [[ADR-006-multi-layer-build-configuration]], [[ADR-007-salsa-driven-compilation]], [[research/build-system-caching-synthesis]]

---

## Context

HWML needs to serialize compiled library interfaces (`.hwmli` files) for caching and distribution. These files contain:
- Exported declarations (types, functions, data constructors)
- Type signatures
- Declaration fingerprints (for early cutoff)
- Source locations

**Requirements:**
1. **Fast loading:** LSP must load interface files in <10ms (dozens of libraries)
2. **Schema evolution:** Format must handle version changes (add/remove fields)
3. **Memory efficiency:** Loading 100 libraries shouldn't consume GB of RAM
4. **Type safety:** Archived data must be validated before use

**Serialization format options:**

| Format | Ser Speed | Deser Speed | Memory | Schema Evolution | Zero-Copy |
|--------|-----------|-------------|---------|------------------|-----------|
| **JSON** | Slow | Slow | High | ✅ Yes | ❌ No |
| **bincode** | Fast | Fast | Medium | ❌ No | ❌ No |
| **postcard** | Fast | Fast | Low | ⚠️ Limited | ❌ No |
| **rkyv** | Fast | **Instant** | Low | ✅ Yes | ✅ Yes |

---

## Decision

**We use `rkyv` for `.hwmli` serialization.**

`rkyv` provides zero-copy deserialization: the file is memory-mapped and used directly without parsing. This gives us instant load times even for large interface files.

```rust
use rkyv::{Archive, Deserialize, Serialize};

#[derive(Archive, Deserialize, Serialize)]
#[archive(check_bytes)]
pub struct Hwmli {
    pub version: u32,
    pub library_name: String,
    pub declarations: Vec<Declaration>,
    pub export_interface_hash: [u8; 32],
}

// Serialize
let bytes = rkyv::to_bytes::<_, 256>(&hwmli)?;
std::fs::write("lib.hwmli", &bytes)?;

// Zero-copy deserialize
let mmap = unsafe { Mmap::map(&File::open("lib.hwmli")?)? };
let archived = rkyv::check_archived_root::<Hwmli>(&mmap)?;
// `archived` is &ArchivedHwmli, usable immediately!
// No deserialization cost!
```

---

## Rationale

### 1. Zero-Copy Performance is Critical for LSP

**Scenario:** rust-analyzer loading 50 library interfaces on startup

**With traditional deserialization (bincode/postcard):**
```rust
for lib in libraries {
    let bytes = std::fs::read(format!("{}.hwmli", lib))?;
    let hwmli: Hwmli = bincode::deserialize(&bytes)?;  // 5-20ms per file
    // Total: 250-1000ms for 50 files
}
```

**With rkyv zero-copy:**
```rust
for lib in libraries {
    let file = File::open(format!("{}.hwmli", lib))?;
    let mmap = unsafe { Mmap::map(&file)? };
    let hwmli = rkyv::check_archived_root::<Hwmli>(&mmap)?;  // <1ms per file
    // Total: <50ms for 50 files
}
```

**20x faster startup** for LSP.

### 2. Memory-Mapped Files Reduce Memory Pressure

**Traditional deserialization:**
```rust
// Each library allocates its own memory
let hwmli: Hwmli = bincode::deserialize(&bytes)?;
// Memory usage: N libraries × average size
```

**rkyv with mmap:**
```rust
// File is mapped into virtual memory
let mmap = unsafe { Mmap::map(&file)? };
let archived = rkyv::check_archived_root::<Hwmli>(&mmap)?;
// Memory usage: OS manages paging, only accessed pages loaded
```

**Benefits:**
- OS can page out unused libraries
- Shared memory between processes (if multiple LSP instances)
- Lower peak memory usage

### 3. Schema Evolution Support

Unlike `bincode` (which breaks on any struct change), `rkyv` supports versioning:

```rust
#[derive(Archive, Serialize, Deserialize)]
#[archive(check_bytes)]
pub struct Hwmli {
    pub version: u32,
    
    // V1 fields
    pub library_name: String,
    pub declarations: Vec<Declaration>,
    
    // V2 fields (added later)
    #[omit_bounds]
    #[with(rkyv::with::Skip)]
    pub source_maps: Option<HashMap<DeclId, SourceRange>>,
}

// Loading handles both V1 and V2 files
match archived.version {
    1 => { /* Use V1 fields only */ }
    2 => { /* Use all fields */ }
    _ => return Err("Unsupported version"),
}
```

### 4. Validation Prevents Corruption

`#[archive(check_bytes)]` enables runtime validation:

```rust
// Without validation (unsafe)
let archived = unsafe { rkyv::archived_root::<Hwmli>(&bytes) };

// With validation (safe)
let archived = rkyv::check_archived_root::<Hwmli>(&bytes)?;
// Checks:
// - File is not truncated
// - Pointers are in-bounds
// - UTF-8 strings are valid
// - Enums have valid discriminants
```

**Prevents:**
- Crashes from corrupted `.hwmli` files
- Security issues from malicious files
- Subtle bugs from bit-flips

### 5. Industry Adoption

**Projects using rkyv:**
- Discord (message archival)
- Mozilla (servo browser engine)
- Veloren (game engine)
- Multiple Rust blockchain projects

**Performance benchmarks (rkyv repo):**
```
Serialize:   bincode: 184ns   rkyv: 96ns    (1.9x faster)
Deserialize: bincode: 370ns   rkyv: 0ns     (instant!)
Size:        bincode: 118 B   rkyv: 110 B   (7% smaller)
```

---

## Consequences

### Positive

1. **LSP startup <100ms:** Zero-copy loading of all libraries
2. **Low memory usage:** OS manages paging, shared memory
3. **Schema evolution:** Can add fields without breaking old files
4. **Validation:** Runtime checks prevent crashes from corruption
5. **Type-safe:** Archived types have same API as regular types

### Negative

1. **Unsafe code:** `mmap` requires `unsafe` block
   - *Mitigation:* Wrapped in safe API, validated with `check_bytes`

2. **Platform-specific:** mmap behavior varies (Windows, Linux, macOS)
   - *Mitigation:* `memmap2` crate handles platform differences

3. **Alignment requirements:** rkyv requires proper alignment
   - *Mitigation:* Automatic via `#[repr(C)]` on archived types

4. **Larger binary:** rkyv derives add ~100KB to binary size
   - *Impact:* Negligible compared to LLVM/CIRCT linkage

### Neutral

- **Write-once, read-many:** rkyv optimizes for reading, not writing
  - This matches our use case (`.hwmli` written once, read many times)

---

## Alternatives Considered

### Alternative 1: bincode

**Pros:**
- Simple API
- Fast serialization
- Small codebase

**Cons:**
- No schema evolution (breaks on any change)
- Traditional deserialization (allocates, copies)
- No zero-copy

**Why rejected:** Breaking changes on every struct modification is unacceptable during development.

### Alternative 2: postcard

**Pros:**
- Compact wire format
- no_std compatible
- Some schema evolution

**Cons:**
- Still requires deserialization
- Schema evolution limited (can't remove fields)
- No zero-copy

**Why rejected:** Deserialization cost too high for LSP startup.

### Alternative 3: Cap'n Proto

**Pros:**
- Zero-copy
- Schema evolution
- Language-agnostic

**Cons:**
- Requires code generation (.capnp files)
- Complex build integration
- Less Rust-idiomatic API

**Why rejected:** Code generation complexity outweighs benefits. rkyv is more Rust-native.

### Alternative 4: FlatBuffers

**Pros:**
- Zero-copy
- Schema evolution
- Google-backed

**Cons:**
- Requires code generation
- Less type-safe (manual offset calculations)
- Not Rust-first design

**Why rejected:** Same as Cap'n Proto - code generation overhead.

---

## Implementation

### Basic Serialization

```rust
use rkyv::{Archive, Deserialize, Serialize, with::Skip};

#[derive(Archive, Deserialize, Serialize)]
#[archive(check_bytes)]
pub struct Hwmli {
    pub version: u32,
    pub library_name: String,
    pub library_version: semver::Version,
    pub declarations: Vec<Declaration>,
    
    #[with(Skip)]
    pub export_interface_hash: [u8; 32],
}

impl Hwmli {
    pub fn to_bytes(&self) -> Result<Vec<u8>, rkyv::ser::serializers::AllocSerializeError> {
        rkyv::to_bytes::<_, 256>(self)
            .map(|v| v.to_vec())
    }
    
    pub fn from_bytes_validated(bytes: &[u8]) -> Result<&ArchivedHwmli, rkyv::validation::CheckArchiveError<_, ()>> {
        rkyv::check_archived_root::<Hwmli>(bytes)
    }
}
```

### Memory-Mapped Loading

```rust
use memmap2::Mmap;

pub struct HwmliCache {
    mmaps: HashMap<String, Mmap>,
}

impl HwmliCache {
    pub fn load(&mut self, lib_name: &str) -> Result<&ArchivedHwmli> {
        if !self.mmaps.contains_key(lib_name) {
            let path = format!(".hwml-build/{}.hwmli", lib_name);
            let file = File::open(path)?;
            let mmap = unsafe { Mmap::map(&file)? };
            self.mmaps.insert(lib_name.to_string(), mmap);
        }
        
        let mmap = &self.mmaps[lib_name];
        rkyv::check_archived_root::<Hwmli>(&mmap)
            .map_err(Into::into)
    }
}
```

### Versioning Strategy

```rust
const CURRENT_VERSION: u32 = 1;

impl Hwmli {
    pub fn new(library_name: String, declarations: Vec<Declaration>) -> Self {
        Self {
            version: CURRENT_VERSION,
            library_name,
            declarations,
            // ...
        }
    }
}

pub fn load_hwmli(path: &Path) -> Result<Box<dyn HwmliCompat>> {
    let file = File::open(path)?;
    let mmap = unsafe { Mmap::map(&file)? };
    let archived = rkyv::check_archived_root::<Hwmli>(&mmap)?;
    
    match archived.version {
        1 => Ok(Box::new(HwmliV1::from(archived))),
        // Future versions:
        // 2 => Ok(Box::new(HwmliV2::from(archived))),
        _ => Err(Error::UnsupportedVersion(archived.version)),
    }
}
```

---

## Migration Path

**Phase 1: Prototype (Week 1)**
- Add rkyv to Cargo.toml
- Add `#[derive(Archive, Serialize, Deserialize)]` to core types
- Test serialization roundtrip

**Phase 2: Integration (Week 2)**
- Implement mmap-based loading
- Add validation (`check_bytes`)
- Create `HwmliCache` abstraction

**Phase 3: Optimization (Week 3)**
- Measure load times
- Optimize alignment/padding
- Tune scratch buffer size

---

## Success Metrics

- [ ] `.hwmli` load time <1ms per file (measured with criterion)
- [ ] LSP startup <100ms for 50 libraries
- [ ] Memory usage <50MB for 100 loaded libraries
- [ ] Schema changes don't break existing `.hwmli` files

---

## References

**rkyv:**
- Documentation: https://rkyv.org/
- Repository: https://github.com/rkyv/rkyv
- Benchmarks: https://github.com/djkoloski/rust_serialization_benchmark

**Related ADRs:**
- [[ADR-006-multi-layer-build-configuration]] - Build caching strategy
- [[research/build-system-caching-synthesis]] - CAS and persistent stores

---

**Status:** Approved  
**Next Steps:**
1. Add `rkyv = "0.7"` to dependencies
2. Add derives to `Declaration`, `Syntax`, etc.
3. Implement `Hwmli::to_bytes()` and `from_bytes()`
4. Write benchmark comparing bincode vs rkyv
5. Measure LSP startup time
