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

## Tips

- Run `nix flake update` to update all flake inputs.
- Run `nix --accept-flake-config run github:juspay/omnix ci` to build _all_ outputs.
- [pre-commit] hooks will automatically be setup in Nix shell. You can also run `pre-commit run -a` manually to run the hooks (e.g.: to autoformat the project tree using `rustfmt`, `nixpkgs-fmt`, etc.).

## See Also

- [nixos.wiki: Packaging Rust projects with nix](https://nixos.wiki/wiki/Rust#Packaging_Rust_projects_with_nix)
