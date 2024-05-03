{
  inputs = {
    nixpkgs.url        = github:nixos/nixpkgs/release-23.11;
    flake-utils.url    = github:numtide/flake-utils;
  };
  outputs = { self, nixpkgs, flake-utils }:
    let
      ssprovePkg = { lib, mkCoqDerivation, coq
                  , equations, extructures, deriving
                  , mathcomp-analysis, mathcomp-ssreflect }:
        mkCoqDerivation {
          pname = "ssprove";
          owner = "SSProve";
          version = "0.2.0";
          src = ./.;
          propagatedBuildInputs = [
            coq
            equations
            mathcomp-analysis
            mathcomp-ssreflect
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
        coqPackages_8_18 = prev.coqPackages_8_18.overrideScope (self: super: {
          extructures       = super.extructures.override { version = "0.4.0"; };
          mathcomp          = super.mathcomp.override { version = "2.1.0"; };
          mathcomp-analysis = super.mathcomp-analysis.override { version = "1.0.0"; };
          ssprove           = self.callPackage ssprovePkg {};
        });
      };
    } // flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [ self.overlays.default ];
        };
      in {
        packages.default = pkgs.coqPackages_8_18.ssprove;
        devShells.default = self.packages.${system}.default;
      });
}
