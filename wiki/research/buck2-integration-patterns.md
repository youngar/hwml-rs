# Buck2 Integration Patterns for Language Compilers

**Date:** 2026-05-03  
**Status:** Design patterns from industry experience  
**Related:** [[decisions/ADR-006-multi-layer-build-configuration]], [[research/modern-build-systems]], [[research/build-system-caching-synthesis]]

---

## Executive Summary

Integrating a new language compiler with Buck2 (or Bazel) requires the compiler to meet Buck2's expectations around hermeticity, caching, and remote execution. This document synthesizes industry best practices from Rust, Hack, Zig, and Sorbet for building language tooling that works seamlessly with distributed build systems.

**Key insights:**
1. **Four-layer architecture**: Pure compiler core + interface layer + three execution frontends + build system bridge
2. **Persistent Worker Protocol**: Achieve both hermeticity (Buck2) and speed (warm daemon)
3. **BXL for LSP integration**: Generate project files from Buck2's build graph
4. **Query-based design**: Use demand-driven computation (Salsa/DICE) for incremental compilation

---

## 1. The Paradigm Shift: Make vs Buck2

### Make: Timestamp-Based Execution

**Model:** File modification times (`mtime`) and local state

**Limitations:**
- No true caching: Delete output folder → recompile everything
- Limited deduplication: No knowledge across machines or network boundaries
- False rebuilds: `mtime` change ≠ content change

### Buck2: Content-Addressable Storage (CAS)

**Model:** Mathematical determinism via cryptographic hashes

**Key features:**
1. **Absolute job deduplication** (Action Graph)
   - Actions are pure functions: `(Inputs, Compiler, Flags, Env) → Outputs`
   - Identical action inputs → identical Action Key → deduplicated execution
   - Graph-level deduplication: Same protobuf file needed by 2 projects → compile once

2. **In-flight remote deduplication**
   - Users A and B request same compilation simultaneously
   - Remote execution cluster recognizes duplicate Action Key
   - Runs once, returns cached result to both

3. **Deterministic caching**
   - Hash file contents + flags + compiler binary
   - Ask remote cache: "Has anyone ever run this exact command?"
   - If yes: Skip execution, download result

4. **Hermeticity**
   - Sandboxed builds (can't read random files or system time)
   - Trusted cache: `git clean -xfd` → `buck2 build` → seconds (all from cache)

**Analogy:**
- Make: Chef checking if soup is cold before reheating
- Buck2: Factory that hashes molecular makeup of ingredients, checks global database, materializes finished soup if already cooked

---

## 2. Compiler Requirements for Buck2 Integration

### Essential Features

**1. Dependency Emitting (`dep-files`)**
```bash
mylangc --emit-deps out.d --output out.o input.lang
```
- Machine-readable list of every file touched during compilation
- Buck2 uses this to dynamically prune action graph
- Only rebuild when *actually used* files change

**2. Response Files (`@args`)**
```bash
mylangc @args.txt
```
- Required when command lines exceed OS limits
- `args.txt` contains actual flags and paths (hundreds of dependency paths)

**3. JSON-Formatted Diagnostics**
```bash
mylangc --message-format=json input.lang
```
- Parallel remote execution → interleaved stdout/stderr unreadable
- JSON allows Buck2/LSP to cleanly parse and render errors

**4. Zero Implicit State**
- Never silently read `~/.mylangconfig` or system libraries
- All configuration via explicit command-line flags
- No hidden filesystem caches (like `ccache`)

---

## 3. The Persistent Worker Protocol

### The Problem: Speed vs Hermeticity

**Compiler wants:** Warm, long-running daemon that remembers everything
- Change one line → recompile one function in 2ms

**Buck2 demands:** Stateless, pure tools
- Compiler = mathematical function: `(Source, Flags) → Binary`
- No hidden state, no memory of previous runs

**Conflict:** If compiler relies on warm daemon, but Buck2 expects cold CLI, builds are incredibly slow (fresh boot per module)

### The Solution: Persistent Workers

Standard shared by Bazel and Buck2

**How it works:**

1. **The Flag:** Compiler accepts `--persistent_worker`
2. **The Loop:** Enters infinite loop reading from `stdin`, writing to `stdout`
3. **The Request:** Buck2 sends `WorkRequest` (JSON/Protobuf) via `stdin`
   - Exact files to compile
   - Flags to use
4. **The Cache:** Compiler processes request, **keeps parsed ASTs in memory**
5. **The Response:** Write `WorkResponse` to `stdout` (exit code, generated files)
6. **The Next Request:** Milliseconds later, next `WorkRequest` arrives
   - Compiler still alive, base ASTs in memory → blazing fast

**Benefits:**
- Buck2 maintains mathematical control over inputs/outputs
- Compiler uses fine-grained, stateful, in-memory caching
- Java and Scala achieve fast compilation under Bazel/Buck2 this way

**Example implementation:**
```rust
// Persistent worker loop
fn main() {
    if args.contains("--persistent_worker") {
        persistent_worker_loop();
    } else {
        cold_start_compile();
    }
}

fn persistent_worker_loop() {
    let mut compiler_state = CompilerState::new();

    loop {
        let request: WorkRequest = read_json_from_stdin();

        // Update VFS with new/changed files
        for file in request.files {
            compiler_state.update_file(file.path, file.content);
        }

        // Compile (reuses cached ASTs for unchanged files)
        let result = compiler_state.compile(request.inputs, request.flags);

        // Send response
        let response = WorkResponse {
            exit_code: result.exit_code,
            output: result.output_path,
            stderr: result.errors_json,
        };
        write_json_to_stdout(response);
    }
}
```

---

## 4. The Four-Layer Architecture

### Layer 1: Pure Compiler Core (`libmylang`)

**Purpose:** Heart of the language - performs no I/O

**Requirements:**
- Library, not executable
- No disk I/O, no environment variables, no stdout
- Mathematical purity: Same input → same output, always

**Query Engine:**
- Built around demand-driven query graph (like Salsa)
- Manages memoization automatically

**Stages (pure functions/queries):**
```rust
parse(FileId) -> AST
resolve_imports(AST) -> DependencyGraph
typecheck(AST, DependencyGraph) -> TypedAST
emit_binary(TypedAST) -> Bytecode/MachineCode
```

### Layer 2: Interface & State Layer

**Purpose:** Bridge pure compiler to real world

**Components:**
- **Virtual File System (VFS):** Maps file paths to file contents
  - Compiler core only knows `FileId(42)`, not `/Users/bob/code.lang`
- **Source Database:** Current state of the world
  - File changes → invalidate specific `FileId` in query engine
  - Cascades to invalidate only downstream typed ASTs that depend on it

### Layer 3: Three Execution Frontends

All depend on `libmylang` and VFS

#### A. Cold-Start CLI (`mylangc`)

**Use case:** Simple one-off usage, strict remote execution clusters

**Flow:**
1. Boot up
2. Read command line args
3. Load files from disk into VFS
4. Run `emit_binary` query
5. Write output to disk
6. Exit

**State:** Zero memory retained, completely cold start every time

#### B. Persistent Worker (`mylangc --worker`)

**Use case:** Buck2 local builds (blazing-fast)

**Flow:**
1. Boot up
2. Enter `while(true)` loop listening to `stdin`
3. Buck2 sends JSON request: "Compile B.lang"
4. Worker updates `B.lang` in VFS
5. Run query, write binary, send JSON response via `stdout`
6. Process stays alive, keeps AST cached for next request

**State:** Keeps VFS and Query Engine in memory

#### C. Language Server (`mylang-lsp`)

**Use case:** VS Code, Neovim, etc.

**Flow:**
1. Boot up
2. Listen for JSON-RPC messages (LSP protocol) over `stdin`/`stdout`
3. User types character → `textDocument/didChange` event
4. LSP updates VFS, runs `typecheck` query → red squiggly lines

**State:** Highly dynamic
- Populates VFS using unsaved text buffers from editor
- Overrides what's on physical disk

### Layer 4: Build System Bridge (Buck2 Workspace)

**Components:**

**1. The Rules (`toolchain.bzl`, `rules.bzl`)**
- Starlark scripts defining `mylang_library` and `mylang_binary`
- Instruct Buck2 to use:
  - Persistent Worker for local execution
  - Cold-Start CLI for remote execution

**2. The Project Generator (`generate_project.bxl`)**
- Buck2 BXL script
- `mylang-lsp` has no idea what external libraries exist or what flags to use
- User runs script → crawls Buck2 build graph → outputs `mylang-project.json`

**3. The Handshake**
- `mylang-lsp` reads `mylang-project.json` on startup
- Pre-populates VFS with third-party dependencies
- Understands module graph before user opens a file

---

## 5. LSP Integration: Two Paths

### Path A: BXL (Buck Extensibility Language) - Recommended

**How it works:**

1. Write BXL script: `generate_project.bxl`
2. User opens editor → extension runs `buck2 bxl //tools:generate_project.bxl`
3. BXL script traverses repository, extracts:
   - Library dependency graph
   - Compiler flags
   - Third-party library locations
4. Writes `mylang-project.json` to repo root
5. LSP watches this JSON file for changes

**Similar to:**
- C++: `compile_commands.json`
- Rust: `rust-project.json`

**Advantages:**
- Stable, proven pattern
- Meta uses this for Rust + Buck2
- Fast: Read static file vs continuous Buck2 queries

### Path B: Build Server Protocol (BSP)

**How it works:**

1. Editor talks to LSP via Language Server Protocol
2. LSP talks to Buck2 via Build Server Protocol
3. User types `import "foo"` → LSP asks Buck2 via BSP: "Where is 'foo'?"
4. Buck2 answers dynamically

**Status:** Buck2's native BSP support still maturing

**Advantages:**
- Always up-to-date (no stale project file)
- Dynamic queries

**Disadvantages:**
- Less stable
- More complex
- Higher latency

## 6. Reference Implementations: Study These Projects

### 1. Rust and `rust-analyzer` (Architectural Gold Standard)

**Why study:**
- Built from scratch using query-based architecture
- `salsa` framework: handles memoization, cache invalidation, query tracking automatically

**Buck2 Integration:**
- Meta builds Rust with Buck2 extensively
- Uses "Path A" approach
- Script traverses Buck2 graph → generates `rust-project.json`
- `rust-analyzer` reads JSON → understands workspace perfectly without `cargo`

**Key takeaway:** Salsa is the biggest "lightbulb moment" for incremental compilation

### 2. Hack and `hh_client` / `hh_server` (The Buck Native)

**Why study:**
- Developed inside Meta's monorepo alongside Buck/Buck2
- Architecture perfectly aligned with distributed, parallel builds

**Architecture:**
- `hh_server`: Background daemon holding ASTs and type graph in memory
- `hh_client`: Thin CLI/LSP wrapper
- CLI doesn't do work → sends IPC request to `hh_server`
- Server keeps ASTs warm in memory

**Advanced feature:**
- "Saved states": Pull pre-computed AST cache from remote server
- Daemon doesn't parse everything on startup

**Key takeaway:** Separation of daemon (state) from CLI (interface)

### 3. Zig (Compiler AS Build System)

**Why study:**
- `cargo build` philosophy but with Buck2-like caching properties

**Architecture:**
- Build scripts written in Zig itself (no Makefiles or Starlark)
- Compiler models compilation as Action Graph with content-addressable caching
- Enforces hermeticity: explicitly isolates dependencies, avoids system-level state

**Key takeaway:** Granular, robust cache built into language from day one

### 4. Sorbet (Bazel/Hermeticity Expert)

**Why study:**
- Fast typechecker for Ruby, built by Stripe in C++
- Designed for massive, distributed monorepos

**Architecture:**
- Built for Bazel from day one
- Accepts strictly formatted input paths
- Avoids touching local filesystem unprompted
- Daemon mode for LSP
- Achieves 100,000+ line/second typechecking via caching and strict input hashing

**Key takeaway:** Engineering blog posts on distributed typechecking speeds are required reading

---

## 7. The `ccache` Anti-Pattern: What NOT to Do

### Why `ccache` is Impure in Buck2/Nix

**The problem:**
- `ccache` intercepts compiler calls
- Looks at hidden directory (`~/.ccache`) for shortcuts
- Buck2 doesn't know about `~/.ccache`

**Consequences:**
1. Corrupted `~/.ccache` → Buck2 build broken, Buck2 has no idea why
2. Error came from outside Buck2's Action Graph
3. Alice and Bob might get different results based on hidden `ccache` state

### Design Principles for HWML

**Never:**
- Implement hidden filesystem cache
- Silently write `.mylang_cache` to user's home directory during batch build

**Always:**
- Compiler relies only on exact file paths passed to it
- Let Buck2 handle 100% of disk-based and network-based caching
- Compiler uses **in-memory caching only** (via Persistent Worker or LSP daemon)

**Goal:** Compiler runs as pure function (remote CI) AND as long-running worker (fast local builds)

---

## 8. Buck2 Rules: Starlark Integration

### Required Components

**1. Toolchain Rule**
```python
hwml_toolchain = rule(
    impl = _hwml_toolchain_impl,
    attrs = {
        "compiler": attrs.exec_dep(providers = [RunInfo]),
        "version": attrs.string(),
    },
)
```
- Points to `hwml` executable
- Allows Buck2 to download specific version depending on host OS
- Hash compiler as input to build

**2. `hwml_library` Rule**
```python
hwml_library = rule(
    impl = _hwml_library_impl,
    attrs = {
        "srcs": attrs.list(attrs.source()),
        "deps": attrs.list(attrs.dep()),
        "features": attrs.list(attrs.string(), default = []),
    },
)
```
- Takes `srcs` and `deps` (other `hwml_library` targets)
- Tells Buck2: "Run compiler on these sources, pass dependency paths, output `.hwmli`"

**3. `hwml_binary` Rule**
```python
hwml_binary = rule(
    impl = _hwml_binary_impl,
    attrs = {
        "srcs": attrs.list(attrs.source()),
        "deps": attrs.list(attrs.dep()),
        "top_module": attrs.string(),
    },
)
```
- Similar to library rule
- Includes final backend step (CIRCT → Verilog)

---

## 9. Application to HWML

### Recommended Implementation Path

**Phase 1: Core Compiler (Months 1-3)**
- Build pure compiler core with Salsa query engine
- Implement cold-start CLI
- Support basic flags: `--emit-deps`, `@args.txt`, `--message-format=json`

**Phase 2: Persistent Worker (Months 4-5)**
- Implement `--persistent_worker` mode
- stdin/stdout WorkRequest/WorkResponse protocol
- Keep VFS + Query Engine in memory between requests

**Phase 3: LSP (Months 6-8)**
- Build LSP server using same compiler core
- Implement LSP protocol (JSON-RPC)
- Read `hwml-project.json` generated by BXL

**Phase 4: Buck2 Rules (Months 9-10)**
- Write Starlark rules: `hwml_toolchain`, `hwml_library`, `hwml_binary`
- Test with Buck2 local builds
- Integrate with remote execution

**Phase 5: BXL Project Generator (Months 11-12)**
- Write `generate_project.bxl` script
- Traverse Buck2 graph → extract dependency info
- Generate `hwml-project.json` for LSP

### Integration with Existing ADR-006 Plans

**ADR-006 Layer 1 (Library Manifest):**
- `hwml.toml` → Parsed by Buck2 rules
- Used to generate Buck2 `BUCK` files via `hwml generate buck`

**ADR-006 Layer 2 (Build Configuration):**
- `hwml-build.toml` → Informs Buck2 platform properties
- Features, optimization levels passed to compiler

**ADR-006 Layer 3 (Lock File):**
- `hwml.lock` → Buck2 uses for dependency resolution
- Ensures reproducible builds

**Synergy:**
- Standalone HWML: Uses `hwml build` with three-tier CAS caching
- Buck2-integrated HWML: Uses Buck2's CAS + remote execution
- LSP works in both modes (reads `hwml-project.json` or `hwml-workspace.toml`)

---

## 10. Success Metrics

- [ ] Compiler accepts `--emit-deps`, `@args.txt`, `--message-format=json`
- [ ] Compiler has zero implicit state (no hidden caches)
- [ ] Persistent worker keeps ASTs in memory across requests
- [ ] LSP responds to edits in <100ms
- [ ] Buck2 rules can build HWML libraries and binaries
- [ ] BXL script generates `hwml-project.json` successfully
- [ ] Remote execution works (hermetic builds in sandbox)
- [ ] Cache hit rate >80% on incremental Buck2 builds
- [ ] Cross-user deduplication (multiple developers share remote cache)

---

## References

**Source Documents:**
- `design/buck2-integration.md` - Original design document

**Related Wiki Pages:**
- [[decisions/ADR-006-multi-layer-build-configuration]] - HWML's build system design
- [[research/modern-build-systems]] - Buck2, Bazel, Nix overview
- [[research/build-system-caching-synthesis]] - Caching strategies
- [[research/content-addressable-storage-systems]] - CAS implementations

**External Resources:**
- Buck2 Documentation: https://buck2.build/docs
- Buck2 Persistent Workers: https://buck2.build/docs/rule_authors/persistent_workers/
- Bazel Persistent Workers: https://bazel.build/remote/persistent
- Salsa Framework: https://github.com/salsa-rs/salsa
- rust-analyzer: https://github.com/rust-lang/rust-analyzer

---

**Next Steps:**
1. Review four-layer architecture with team
2. Prototype Salsa-based query engine for HWML
3. Implement cold-start CLI with required flags
4. Design `.hwmli` format for compilation artifacts
5. Write persistent worker protocol implementation
6. Draft initial Buck2 Starlark rules

---

**Status:** Ready for team review and implementation planning
**Confidence:** 0.95 (based on industry best practices from Meta, Stripe, and Rust community)
