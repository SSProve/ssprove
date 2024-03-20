{
  inputs = {
    nixpkgs.url        = github:nixos/nixpkgs;
    flake-utils.url    = github:numtide/flake-utils;
  };
  outputs = { self, nixpkgs, flake-utils }:
    let
      mkDrv = { stdenv, which, coqPackages, coq } :
           let
             extructures' = coqPackages.extructures.override { version = "0.4.0"; };
             d = coqPackages.mkCoqDerivation {
              pname = "ssprove";
              owner = "SSProve";
              version = "0.0.1";
              propagatedBuildInputs =
                [ coq ]
                ++
                (with coqPackages; [equations
                                    mathcomp-analysis
                                    mathcomp-ssreflect
                                    deriving])
                ++ [extructures'];
                meta = {
                 description = "A foundational framework for modular cryptographic proofs in Coq ";
                 license = coqPackages.lib.licenses.mit;
                 };
               };
             in
               # getting this the flake-style means the code is already there
               d.overrideAttrs (oldAttrs: {
                 src = ./.;
               });
    in { inherit mkDrv; } //
      flake-utils.lib.eachDefaultSystem (system:
        let
          pkgs = nixpkgs.legacyPackages.${system};
        in
         rec {
            devShell =
              let
                args = {
                  inherit (pkgs) stdenv which;
                  coqPackages = pkgs.coqPackages_8_18.overrideScope
                    (self: super: {
                      mathcomp = super.mathcomp.override { version = "2.1.0"; };
                      mathcomp-analysis = super.mathcomp-analysis.override { version = "1.0.0"; };
                    });
                  coq = pkgs.coq_8_18;
                };
                ssprove' = mkDrv args;
              in
                pkgs.mkShell {
                  packages =
                    (with pkgs; [ gnumake ])
                    ++
                    (with ssprove';  propagatedBuildInputs);
                };
         });
}
