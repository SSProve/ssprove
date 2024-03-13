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
           in
            coqPackages.mkCoqDerivation {
              pname = "ssprove";
              owner = "SSProve";
              version = "0.0.1";
              propagatedBuildInputs = (with coqPackages; [
                                    equations
                                    mathcomp-analysis
                                    mathcomp-ssreflect
                                    deriving
                                  ])
                                  ++ [extructures'];
               meta = {
                 description = "A foundational framework for modular cryptographic proofs in Coq ";
            #     license = licenses.mit; TODO load lib
               };
            };
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
                  coq = pkgs.coq_8_18;
                  coqPackages = pkgs.coqPackages_8_18.overrideScope
                    (self: super: {
                      mathcomp = super.mathcomp.override { version = "2.1.0"; };
                      mathcomp-analysis = super.mathcomp-analysis.override { version = "1.0.0"; };
                    });
                };
                ssprove' = mkDrv args;
              in
                pkgs.mkShell {
                  packages =
                    (with pkgs; [ coq gnumake ])
                    ++
                    (with ssprove';  nativeBuildInputs);
                };
         });
}
