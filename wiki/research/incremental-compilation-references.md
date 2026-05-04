# Incremental Compilation: References & Sources

**Created:** 2026-05-03  
**Type:** Reference Index  
**Purpose:** Comprehensive list of sources consulted during research

---

## Academic Papers

### Incremental Computation

1. **Adapton: Composable, Demand-Driven Incremental Computation** (PLDI 2014)
   - Matthew A. Hammer, Yit Phang Khoo, Michael Hicks, Jeffrey S. Foster
   - [PDF](https://www.cs.umd.edu/~hammer/adapton/adapton-pldi2014.pdf)
   - Key: Demanded computation graph, memoization, change propagation

2. **Incremental Computation with Names** (OOPSLA 2015)
   - Matthew A. Hammer, et al.
   - [PDF](https://www.cs.tufts.edu/~jfoster/papers/nominal-adapton.pdf)
   - Key: Nominal memoization, first-class names

3. **Precise, Efficient, and Expressive Incremental Build Scripts with PIE** (IC 2019)
   - Gabriël Konat, Roelof Sol, Sebastian Erdweg, Eelco Visser
   - [researchr](https://researchr.org/publication/KonatSEV19)
   - Key: Sound + optimal incremental builds, dynamic dependencies

4. **Scalable Incremental Building with Dynamic Task Dependencies** (ASE 2018)
   - Gabriël Konat, et al.
   - [KIT](https://publikationen.bibliothek.kit.edu/1000188589)
   - Key: Bottom-up traversal, scalability improvements to Pluto

5. **A Sound and Optimal Incremental Build System with Dynamic Dependencies**
   - [PDF](https://www.pl.informatik.uni-mainz.de/files/2019/04/pluto-incremental-build.pdf)
   - Key: Pluto algorithm, soundness proof, optimality

### Incremental Type Checking

6. **Incremental Type-Checking for Free** (OOPSLA 2022)
   - [PDF](https://aronzwaan.github.io/assets/oopsla22-extended.pdf)
   - Key: Automatic incrementalization of Statix type-checkers, 147x speedups

7. **Incremental Computation with Names via Type-Theoretic Refinements**
   - [arXiv](https://arxiv.org/pdf/2504.08946)
   - Key: Type-theoretic foundations, order maintenance data structures

### Compiler Design

8. **Enabling Fine-Grained Incremental Builds by Making Compiler Stateful** (CGO 2024)
   - [PDF](https://drcut.github.io/assets/papers/CGO24.pdf)
   - Key: Stateful compiler, profiling history, dormant pass bypassing

---

## Industry Systems

### Rust

9. **Incremental Compilation in Detail** - Rust Compiler Development Guide
   - [rustc-dev-guide](https://rustc-dev-guide.rust-lang.org/queries/incremental-compilation-in-detail.html)
   - Key: Query system, try-mark-green, on-disk cache

10. **Rust's Incremental Compiler Architecture** - LWN
    - [LWN article](https://lwn.net/SubscriberLink/997784/)
    - Key: Query-based model vs traditional pipeline

11. **Incremental Systems Rethought** - Rust Project Goals 2026
    - [Rust goals](https://rust-lang.github.io/rust-project-goals/2026/incremental-system-rethought.html)
    - Key: Shared bases between invocations, dynamic dependencies

12. **Cargo Checksum Freshness** - Tracking Issue #14136
    - [GitHub](https://github.com/rust-lang/cargo/issues/14136)
    - Key: Content hashing vs mtimes

### Haskell GHC

13. **Separate Compilation and Recompilation** - GHC User Guide
    - [GHC 9.14](https://haskell.org/ghc/docs/latest/html/users_guide/separate_compilation.html)
    - Key: Interface files, recompilation checker

14. **Optimizing Incremental Compilation** - ezyang's blog
    - [Blog post](http://blog.ezyang.com/2016/08/optimizing-incremental-compilation/)
    - Key: Dependency on specific pieces of .hi files, inlining trade-offs

15. **Interface Files with Core Definitions** - Well-Typed
    - [Blog](http://www.well-typed.com/blog/2023/02/interface-files-with-core/)
    - Key: Storing Core in interface files, bytecode generation

### Scala

16. **Understanding Incremental Recompilation** - sbt Reference Manual
    - [sbt docs](https://scala-sbt.org/1.x/docs/Understanding-Recompilation.html)
    - Key: Name hashing, API change detection, member reference dependencies

17. **Speed up Compile Times with Zinc 1.0** - Scala Blog
    - [scala-lang.org](https://scala-lang.org/blog/2017/11/03/zinc-blog-1.0.html)
    - Key: Class-level granularity, mapping source → classes → dependencies

18. **Analysis of Zinc** - Eugene Yokota (ScalaSphere 2019)
    - [SlideShare](https://www.slideshare.net/EugeneYokota/analysis-of-zinc-scalasphere-2019)
    - Key: Preventing invalidation spread, compiler bridge

### Salsa

19. **Salsa Book: Algorithm**
    - [salsa-rs.github.io](https://salsa-rs.netlify.app/reference/algorithm.html)
    - Key: Red-green algorithm, revision tracking, durability

20. **Durable Incrementality** - rust-analyzer blog
    - [Blog](https://rust-analyzer.github.io/blog/2023/07/24/durable-incrementality.html)
    - Key: Durability optimization, stdlib vs user code

---

## Build Systems

### Bazel

21. **Remote Execution Overview** - Bazel Documentation
    - [Bazel preview](https://preview.bazel.build/remote/rbe)
    - Key: Benefits, requirements, RE API

22. **Remote Caching** - Bazel 3.2.0
    - [Bazel docs](https://docs.bazel.build/versions/3.2.0/remote-caching.html)
    - Key: Action cache, CAS, HTTP/1.1 protocol

23. **Hermeticity** - Bazel main
    - [Bazel docs](https://docs.bazel.build/versions/master/hermeticity.html)
    - Key: Definition, benefits, implementation

24. **Remote Execution API v2** - GitHub
    - [bazelbuild/remote-apis](https://github.com/bazelbuild/remote-apis/)
    - Key: Protocol specification, proto definitions

### Buck2

25. **Buck2 Architecture** - Facebook
    - [GitHub docs](https://github.com/facebook/buck2/blob/main/docs/developers/architecture/buck2.md)
    - Key: Rust core, Starlark rules, single incremental graph

26. **Build Faster with Buck2** - Meta Engineering Blog
    - [Blog](https://engineering.fb.com/2023/04/06/open-source/buck2-open-source-large-scale-build-system)
    - Key: Design principles, 2x faster, dynamic dependencies

27. **5 Things You Didn't Know About Buck2** - Meta Engineering
    - [Blog](https://engineering.fb.com/2023/10/23/developer-tools/5-things-you-didnt-know-about-buck2)
    - Key: Rust choice, Starlark optimization, unique features

### Nix

28. **Content-Addressable Derivations** - NixOS Wiki
    - [wiki.nixos.org](https://wiki.nixos.org/wiki/Ca-derivations)
    - Key: Floating CA derivations, experimental feature

29. **Reproducibility** - ners.ch
    - [ners.ch/Software/Nix](https://ners.ch/Software/Nix/Reproducibility)
    - Key: Hermetic build environment, timestamp handling

### Shake

30. **Shake Build System** - Official Site
    - [shakebuild.com](https://shakebuild.com/)
    - Key: Monadic dependencies, dynamic discovery

31. **Why Choose Shake?**
    - [shakebuild.com/why](https://shakebuild.com/why)
    - Key: More dependencies, fine-grained dependencies, early cut-off

---

## LSP & Remote Compilation

32. **How We Made the Deno Language Server 10x Faster** - Deno Blog
    - [Medium](https://denoland.medium.com/how-we-made-the-deno-language-server-ten-times-faster-62358af87d11)
    - Key: Cache layer, file version tracking

33. **clangd Remote Index**
    - [clangd.llvm.org](https://clangd.llvm.org/design/remote-index.html)
    - Key: Batch indexer, gRPC server, client integration

34. **gopls Daemon Mode** - Go Documentation
    - [go.dev](https://go.dev/gopls/daemon)
    - Key: Shared daemon, thin forwarder, warm state

35. **rust-analyzer Architecture**
    - [rust-analyzer book](https://rust-analyzer.github.io/book/contributing/architecture.html)
    - Key: VFS abstraction, Salsa database, LSP independence

---

## Remote Execution Services

36. **BuildBuddy Documentation**
    - [buildbuddy.io/docs](https://www.buildbuddy.io/docs/remote-build-execution)
    - Key: RBE features, auto-scaling, custom Docker images

37. **Buildbarn bb-remote-execution**
    - [GitHub](https://github.com/buildbarn/bb-remote-execution)
    - Key: Scheduler, worker, runner decomposition

38. **NativeLink**
    - [GitHub](https://github.com/TraceMachina/nativelink)
    - Key: Rust implementation, Nix-powered, high performance

---

**See also:**
- [[research/incremental-compilation-synthesis]] - Complete recommendations
- [[research/INCREMENTAL-COMPILATION-SUMMARY]] - Executive summary
