{ inputs, ... }:
{
  perSystem = { config, self', pkgs, lib, system, ... }:
    let
      # Get CIRCT and its dependencies from circt-nix
      # Note: CIRCT has multiple outputs (out, lib, dev)
      # We need the dev outputs for headers
      circt = inputs.circt-nix.packages.${system}.circt;
      mlir = inputs.circt-nix.packages.${system}.mlir;
      libllvm = inputs.circt-nix.packages.${system}.libllvm;
    in
    {
      devShells.default = pkgs.mkShell {
        name = "hwml-shell";
        inputsFrom = [
          self'.devShells.rust
        ];
        packages = with pkgs; [
          just
          nixd # Nix language server
          bacon

          # CIRCT backend dependencies
          cmake
          ninja
          pkg-config
          clang
        ];

        # Environment variables for CIRCT backend
        shellHook = ''
          # Point to dev outputs for headers (not the default 'out' which only has binaries)
          export CIRCT_SYS_PREFIX="${circt.dev}"
          export MLIR_SYS_PREFIX="${mlir.dev}"
          export LLVM_SYS_PREFIX="${libllvm.dev}"

          # Point to lib outputs for linking (Nix separates headers and libraries)
          export CIRCT_SYS_LIB_PREFIX="${circt.lib}"
          export MLIR_SYS_LIB_PREFIX="${mlir}"
          export LLVM_SYS_LIB_PREFIX="${libllvm.lib}"

          # Melior expects MLIR_SYS_<version>_PREFIX
          # CIRCT is built with LLVM 22, so we set this
          export MLIR_SYS_220_PREFIX="${mlir.dev}"

          # Ensure bindgen can find ALL headers
          # Note: CIRCT dev has a nested include/include structure
          export BINDGEN_EXTRA_CLANG_ARGS="-I${circt.dev}/include/include -I${mlir.dev}/include -I${libllvm.dev}/include"

          # Runtime linking
          # Note: circt has separate .lib output, but mlir and libllvm use default output
          export LD_LIBRARY_PATH="${circt.lib}/lib:${mlir}/lib:${libllvm}/lib:''${LD_LIBRARY_PATH:-}"
          export DYLD_LIBRARY_PATH="${circt.lib}/lib:${mlir}/lib:${libllvm}/lib:''${DYLD_LIBRARY_PATH:-}"

          echo "╔════════════════════════════════════════════════════════════╗"
          echo "║  HWML Development Environment with CIRCT Backend           ║"
          echo "╚════════════════════════════════════════════════════════════╝"
          echo ""
          echo "✓ CIRCT dev:  ${circt.dev}"
          echo "✓ MLIR dev:   ${mlir.dev}"
          echo "✓ LLVM dev:   ${libllvm.dev}"
          echo ""
          echo "✓ CIRCT lib:  ${circt.lib}"
          echo "✓ MLIR lib:   ${mlir}"
          echo "✓ LLVM lib:   ${libllvm}"
          echo ""
          echo "Environment variables set:"
          echo "  CIRCT_SYS_PREFIX=${circt.dev}"
          echo "  CIRCT_SYS_LIB_PREFIX=${circt.lib}"
          echo "  MLIR_SYS_PREFIX=${mlir.dev}"
          echo "  MLIR_SYS_LIB_PREFIX=${mlir}"
          echo "  LLVM_SYS_PREFIX=${libllvm.dev}"
          echo "  LLVM_SYS_LIB_PREFIX=${libllvm.lib}"
          echo "  MLIR_SYS_220_PREFIX=${mlir.dev}"
          echo ""
          echo "Ready to build CIRCT backend:"
          echo "  cargo build -p hwml_circt_sys"
          echo "  cargo build -p hwml_circt"
          echo "  cargo run --example minimal_hsyntax -p hwml_circt"
          echo ""
        '';
      };
    };
}
