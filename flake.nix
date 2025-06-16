{
  inputs = {
    nixpkgs.url        = github:nixos/nixpkgs;
    flake-utils.url    = github:numtide/flake-utils;
  };
  outputs = { self, nixpkgs, flake-utils }:
    let
      ssprovePkg = { lib, mkCoqDerivation, coq
                  , equations, extructures, deriving
                  , mathcomp-analysis, mathcomp-ssreflect
                  , mathcomp-experimental-reals
                  , mathcomp-word}:
        mkCoqDerivation {
          pname = "ssprove";
          owner = "SSProve";
          version = "0.2.0";
          src = ./.;
          propagatedBuildInputs = [
            equations
            mathcomp-analysis
            mathcomp-experimental-reals
            mathcomp-ssreflect
            mathcomp-word
            deriving
            extructures
          ];
          meta = {
            description = "A foundational framework for modular cryptographic proofs in Coq ";
            license = lib.licenses.mit;
          };
        };
    in {
      overlays.default = final: prev: {
        coqPackages_8_20 = prev.coqPackages_8_20.overrideScope (self: super: {
          ssprove  = self.callPackage ssprovePkg {};
        });
      };
    } // flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [ self.overlays.default ];
        };
      in {
        packages.default = pkgs.coqPackages_8_20.ssprove;
        devShells.default = self.packages.${system}.default;
      });
}
