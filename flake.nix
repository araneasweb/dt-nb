{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-25.05";
    plfa = {
      url = "github:plfa/plfa";
      flake = false;
    };
  };

  outputs =
    { nixpkgs, ... }:
    let
      eachSystem =
        f:
        nixpkgs.lib.genAttrs nixpkgs.lib.systems.flakeExposed (
          system:
          f {
            pkgs = import nixpkgs {
              inherit system;
            };
          }
        );
    in
    {
      devShells = eachSystem (
        { pkgs }:
        {
          default = pkgs.mkShell {
            packages = with pkgs; [
              (agda.withPackages (p: with p; [
                standard-library
              ]))
              haskellPackages.agda2hs
              haskell.compiler.ghc98
              racket
            ];
            env = pkgs.buildEnv {
              name = "agda-plfa-env";
              paths = [ pkgs.agda ];
            };
            shellHook = /* bash */ ''
              set -euo pipefail
              export PLTUSERHOME="$PWD/.racket"
              export PLTADDONDIR="$PWD/.racket"
              mkdir -p "$PLTUSERHOME"
              raco pkg install --auto --skip-installed \
                fixw rackcheck racket-langserver pie
            '';
          };
        }
      );
    };
}
