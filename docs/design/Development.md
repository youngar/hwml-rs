# Development

## Quick Start

Before pushing changes, run these commands locally to catch issues early:

```bash
# Check that everything compiles
cargo check --workspace

# Run all tests (core, documentation validation, etc.)
cargo test --workspace

# Run clippy for code quality
cargo clippy --workspace
```

These match exactly what CI runs. For a comprehensive check that also validates dependency separation and builds the mdBook, use:

```bash
./scripts/validate-ci.sh
```

## Getting Started with Nix

The project uses Nix for reproducible development environments. [Install direnv](https://nixos.asia/en/direnv), open in VSCode and accept the suggestions. The setup uses [crane](https://crane.dev/) via [rust-flake](https://github.com/juspay/rust-flake).

This repo uses [Flakes](https://nixos.asia/en/flakes).

```bash
# Dev shell
nix develop

# or run via cargo
nix develop -c cargo run

# build
nix build
```

We also provide a [`justfile`](https://just.systems/) for Makefile'esque commands to be run inside of the devShell.

### Tips

- Run `nix flake update` to update all flake inputs.
- Run `nix --accept-flake-config run github:juspay/omnix ci` to build _all_ outputs.

### See Also

- [nixos.wiki: Packaging Rust projects with nix](https://nixos.wiki/wiki/Rust#Packaging_Rust_projects_with_nix)

## Testing

### Snapshot/Approval Testing

We use `insta` to manage snapshot based tests. See
https://insta.rs/docs/quickstart/ for more details.

Install the tool:
``` sh
cargo install cargo-insta
```

Review snapshot updates:
```sh
cargo insta review
```

Run tests:
```sh
cargo insta test
```

### Fuzz Testing

We use `fuzz` for fuzz based testing.

Install the tool:
```sh
cargo install cargo-fuzz
```

`cd` into the `fuzz` directory and run `cargo fuzz run <fuzzer_name>`.

For example:
```sh
cd crates/hwml-core/fuzz
cargo fuzz run fuzz_core_roundtrip
```

## Documentation

The project documentation is built with mdBook and includes type-checked code snippets.

### Building Documentation Locally

Install mdBook:
```sh
cargo install mdbook
```

Build the documentation:
```sh
mdbook build docs/
```

The output will be in `docs/book/`. Open `docs/book/index.html` in your browser.

### Validating Documentation

All code snippets in the documentation are validated during CI. Run validation locally:

```sh
cargo test -p mdbook-hwml --test validate_docs
```

This test extracts all `hwml` and `hwmlc` code blocks from the documentation and type-checks them. Snippets can be marked with modifiers:

- ` ```hwml` - Surface language snippet (must type-check)
- ` ```hwmlc` - Core language snippet (must type-check)
- ` ```hwml,ignore` - Skip type-checking (for unimplemented features)
- ` ```hwml,should_fail` - Snippet should fail type-checking (for error examples)

### Documentation Structure

- `docs/src/guide/` - User-facing tutorials and guides
- `docs/src/reference/` - Language reference documentation
- `docs/src/internals/` - Compiler internals and implementation details
