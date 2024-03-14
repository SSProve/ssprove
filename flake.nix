{
  inputs = {
    nixpkgs.url        = github:nixos/nixpkgs;
    flake-utils.url    = github:numtide/flake-utils;
  };
  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
      in
       rec {
         mkDrv = { stdenv, which, coqPackages, coq } :
           let
             extructures' = coqPackages.extructures.override { version = "0.4.0"; };
           in
            stdenv.mkDerivation {
              pname = "ssprove";
              version = "0.0.1";
              src = ./.;
              nativeBuildInputs = [ which coq.ocamlPackages.findlib ] ++
                                  (with coqPackages; [
                                    equations
                                    mathcomp-analysis
                                    mathcomp-ssreflect
                                    deriving
                                  ])
                                  ++ [extructures'];
              buildInputs = [ coq ];
            };

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
