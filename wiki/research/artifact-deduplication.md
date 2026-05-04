# Artifact Deduplication and Cross-User Cache Sharing

**Created:** 2026-05-03  
**Type:** Research Synthesis  
**Status:** Analysis of deduplication strategies  
**Confidence:** 0.92 (based on production systems)

---

## Summary

Effective artifact deduplication can reduce storage costs by 10-100x and dramatically improve cache hit rates. Modern systems use **content-addressable storage**, **garbage collection policies**, and **scoped sharing** to balance deduplication against isolation and trust boundaries.

---

## Deduplication Granularity

### Blob-Level Deduplication

**CAS Model:**
- Every file content → SHA-256 hash → stored once
- Multiple build outputs reference same blob
- Example: `libstd.a` appears in thousands of builds → stored once

**Compression:**
- Most systems use **zstandard** for blobs
- Bazel, Buck2, NativeLink support zstd-compressed CAS
- Trade-off: CPU (compress/decompress) vs bandwidth + storage

**Git Pack Objects:**
- Buildbarn uses Git pack-objects cache for concurrent fetches
- Same pipeline ref fetched by multiple CI jobs → deduplicated on server
- Served from cache when available

**References:**
- [GitLab CI configuration performance](https://docs.gitlab.com/16.10/ee/development/pipelines/performance.html)

---

### Chunk-Level Deduplication

**Beyond file-level:**
- Some systems (less common in build tools) use rolling hash to split files into chunks
- Useful for large files with small changes (like disk images)
- Build systems mostly stick to file-level (simpler, faster)

---

## Sharing Scopes

### 1. Instance-Wide (Maximum Deduplication)

**Bazel default:**
- All users, all projects share one CAS
- Maximum storage efficiency
- Requires trust (one user can see hashes of another's artifacts)

**Security implications:**
- Hash collision = potential cache poisoning
- Mitigation: Use strong hash (SHA-256), verify signatures
- Not suitable for multi-tenant SaaS with untrusted users

**Use case:** Internal company build system, all users trusted

---

### 2. Organization-Scoped (Balance)

**GitLab Artifact Registry:**
- CAS shared within organization, isolated between orgs
- Deduplicates common dependencies (base images, public packages)
- Prevents cross-org poisoning
- Storage overhead vs instance-wide: ~10-30% (depends on shared dependencies)

**Workflow:**
1. User uploads artifact → compute SHA-256
2. Check org-scoped CAS: already exists? → just add reference
3. Not exists? → Store blob in org CAS, add reference

**Use case:** Multi-tenant SaaS, org is trust boundary

**References:**
- [GitLab ADR-002: Storage Deduplication Scope](https://handbook.gitlab.com/handbook/engineering/architecture/design-documents/artifact_registry/decisions/002_storage_deduplication_scope/)

---

### 3. Repository-Scoped (Least Deduplication)

**GitHub Actions cache:**
- 10GB limit per repository
- Key-based (not content-addressed)
- No deduplication across repos, even in same org

**Limitation:** Popular libraries (React, Lodash) stored separately in each repo

**Enhancement services:**
- BoringCache, Depot Cache: Cross-repo, content-addressed, workspace-scoped
- Solves GitHub Actions limitation without requiring Bazel

---

### 4. Cross-Clone Deduplication (Local)

**Git worktree model:**
- Multiple checkouts of same repo share `.git` directory
- Build cache in `.git/build-cache/` shared across worktrees
- Content-addressed: Same source → same artifacts → reused across branches

**Bazel local disk cache:**
- Can use filesystem directory as remote cache
- Multiple workspaces point to same cache directory
- No garbage collection (grows unbounded without manual cleanup)

**Use case:** Single developer, multiple branches, avoid rebuilding unchanged code

**References:**
- [Bazel Remote Caching](https://docs.bazel.build/versions/3.2.0/remote-caching.html)

---

## Garbage Collection

### Challenge

CAS grows unbounded. Which artifacts to evict?

### Strategies

**1. LRU (Least Recently Used):**
- Track last access time for each blob
- Evict oldest when space limit reached
- Simple, effective for shared caches
- Used by: bazel-remote, Buildbarn

**2. Size-Based:**
- Evict largest blobs first
- Useful when large artifacts are less likely to be reused
- Combined with LRU: Evict large+old blobs preferentially

**3. TTL (Time-To-Live):**
- Delete blobs older than N days, regardless of access
- Ensures cache doesn't grow indefinitely
- Risk: Delete artifacts that might be reused (old release branches)

**4. Reference Counting:**
- Track which builds reference each blob
- Only delete when reference count = 0
- Complex: Requires tracking all builds, hard in distributed system

**5. S3-FIFO (Adaptive):**
- Hybrid eviction policy (new in 2024)
- Better hit rate than pure LRU
- Used by: Some modern caching proxies

**References:**
- [Bazel Remote Cache: Garbage Collection](https://docs.bazel.build/versions/3.2.0/remote-caching.html)

---

## Cross-User Sharing: Permission Models

### Problem

User A builds artifact X. Can user B use it?

### Models

**1. Public Cache (Trust-Based):**
- Anyone can read/write
- Works if all users trusted (internal company)
- Requires secure environment (VPN, authenticated access)

**2. Read-All, Write-Restricted:**
- All users read from cache
- Only CI or specific service accounts write
- Prevents accidental/malicious cache poisoning
- BuildBuddy supports this model

**3. Signed Artifacts:**
- Artifacts include signature (e.g., GPG)
- Users trust artifacts signed by CI key
- Nix model: Substituters signed by cache key
- Overhead: Signature verification on every access

**4. Workspace-Scoped Tokens:**
- Shared cache with API tokens
- Token grants read/write to specific workspace (project/org)
- Example: Depot Cache, BoringCache
- Easy to revoke/rotate tokens

**References:**
- [NativeLink: Glossary (CAS)](https://nativelink.com/docs/reference/glossary)

---

## Multi-Clone Deduplication

### Use Case

Developer has 3 clones of same repo (main, feature1, feature2). Avoid 3x storage.

### Solutions

**1. Shared Git Directory:**
```bash
git clone --bare repo.git .git-shared
git worktree add main
git worktree add feature1
git worktree add feature2
```
- All worktrees share `.git-shared/`
- Build cache in shared directory, content-addressed

**2. Symlink to Shared Cache:**
```bash
export BAZEL_CACHE_DIR=$HOME/.cache/bazel
```
- All projects use same cache directory
- Bazel already content-addressed, automatic dedup

**3. Remote Cache (Network):**
- All clones point to remote cache (localhost or LAN)
- Single source of truth, shared across all dev machines
- Example: Run bazel-remote on Docker on localhost

**References:**
- [Bazel: Use filesystem as remote cache](https://docs.bazel.build/versions/3.2.0/remote-caching.html)

---

## Content-Addressed Proxy Caches

### Problem

Package managers (npm, PyPI, Maven, Go) use URL-based fetching. Same package downloaded N times.

### Solution: Content-Addressed Proxy

**Example: `content-cache` (Rust):**
- Proxy for npm, PyPI, Maven, RubyGems, Git
- Stores packages by BLAKE3 hash
- Deduplicates identical content across versions
- Singleflight: Concurrent requests for same uncached resource → one upstream fetch

**Workflow:**
1. npm requests `lodash@4.17.21`
2. Proxy checks BLAKE3 hash of tarball
3. Already cached? Serve from local disk (microseconds)
4. Not cached? Fetch from npm, hash, store, serve

**Benefits:**
- Offline builds (cache persists)
- Bandwidth savings (reuse across projects)
- Speed: Local disk >> network

**References:**
- [wolfeidau/content-cache](https://github.com/wolfeidau/content-cache)

---

## Recommendations for HWML

1. **Organization-scoped CAS:**
   - Share artifacts within company/team
   - Isolate between different customers (if SaaS)

2. **Content-addressed `.hwmli` files:**
   - Hash = f(source_file_content, compiler_version, flags)
   - Store in CAS, automatic deduplication

3. **LRU + TTL garbage collection:**
   - Keep 100GB of recent artifacts (LRU)
   - Delete anything >90 days old (TTL)

4. **Local disk cache with symlinks:**
   - Developer workstation: `~/.cache/hwml-cas/`
   - All clones share this directory
   - Background GC task to keep under 50GB

5. **Remote cache for CI:**
   - S3 or GCS bucket as backing store
   - BuildBuddy/NativeLink in front for RBE support
   - Authenticated access (workspace tokens)

**See:** [[research/modern-build-systems]] for CAS implementation details

---

**Related:**
- [[research/modern-build-systems]]
- [[research/modern-incremental-compilation]]
- [[decisions/ADR-004-mvs-package-manager]]
