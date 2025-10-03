# Development

## Getting Started with Nix

1) [install direnv](https://nixos.asia/en/direnv), open in VSCode and accept the suggestions.
  - It uses [crane](https://crane.dev/), via [rust-flake](https://github.com/juspay/rust-flake).

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

###  Fuzz Testing

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
