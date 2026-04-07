{
  inputs = {
    nixpkgs.url        = github:nixos/nixpkgs;
    flake-utils.url    = github:numtide/flake-utils;
  };
  outputs = { self, nixpkgs, flake-utils }:
    let
      ssprovePkg = { lib, mkCoqDerivation, coq
                  , equations, extructures, deriving
                  , mathcomp-analysis, mathcomp-boot
                  , mathcomp-experimental-reals
                  , mathcomp-word}:
        mkCoqDerivation {
          pname = "ssprove";
          owner = "SSProve";
          opam-name = "rocq-ssprove";
          version = "0.3.1";
          src = ./.;
          useDune = true;
          propagatedBuildInputs = [
            equations
            mathcomp-boot
            mathcomp-analysis
            mathcomp-experimental-reals
            extructures
            deriving
            mathcomp-word
          ];
          meta = {
            description = "A foundational framework for modular cryptographic proofs in Rocq ";
            license = lib.licenses.mit;
          };
        };
    in {
      overlays.default = final: prev: {
        coqPackages_9_0 = prev.coqPackages_9_0.overrideScope (self: super: {
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
        packages.default = pkgs.coqPackages_9_0.ssprove;
        devShells.default = self.packages.${system}.default;
      });
}
