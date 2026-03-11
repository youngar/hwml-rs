{ inputs, ... }:
{
  imports = [
    inputs.rust-flake.flakeModules.default
    inputs.rust-flake.flakeModules.nixpkgs
  ];
  perSystem = { config, self', pkgs, lib, ... }: {
    rust-project.crates."hwml".crane.args = {
      buildInputs = lib.optionals pkgs.stdenv.hostPlatform.isDarwin [
        pkgs.apple-sdk
      ];
    };
    packages.default = self'.packages.hwml;
  };
}
