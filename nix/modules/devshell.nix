{ inputs, ... }:
{
  perSystem = { config, self', pkgs, lib, ... }: {
    devShells.default = pkgs.mkShell {
      name = "hwml-shell";
      inputsFrom = [
        self'.devShells.rust
      ];
      packages = with pkgs; [
        just
        nixd # Nix language server
        bacon
      ];
    };
  };
}
