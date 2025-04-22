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
        coqPackages_8_19 = prev.coqPackages_8_19.overrideScope (self: super: {
          # mathcomp-ssreflect inherits this version
          # setting it to mathcomp-ssreflect does not work.
          # see my question on Zulip:
          # https://coq.zulipchat.com/#narrow/stream/290990-Nix-toolbox-devs-.26-users/topic/Loading.20inconsistency.20in.20mathcomp.20dependencies
          mathcomp = super.mathcomp.override { version = "2.2.0"; };
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
        packages.default = pkgs.coqPackages_8_19.ssprove;
        devShells.default = self.packages.${system}.default;
      });
}
