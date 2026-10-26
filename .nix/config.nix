{
  ## DO NOT CHANGE THIS
  format = "1.0.0";

  attribute = "ssprove";

  default-bundle = "9.1";

  bundles."9.0" = {
    coqPackages = {
      coq.override.version = "9.0";
    }; rocqPackages = {
      rocq-core.override.version = "9.0";
    };
    push-branches = [ "main" ];
  };
  bundles."9.1" = {
    coqPackages = {
      coq.override.version = "9.1";
    }; rocqPackages = {
      rocq-core.override.version = "9.1";
    };
    push-branches = [ "main" ];
  };
  bundles."9.2" = {
    coqPackages = {
      coq.override.version = "9.2";
    }; rocqPackages = {
      rocq-core.override.version = "9.2";
    };
    push-branches = [ "main" ];
  };
  bundles."MC-dev" = {
    coqPackages = {
      coq.override.version = "9.1";
      mathcomp.job = false;
      mathcomp.override.version = "master";
      mathcomp-analysis.job = false;
      mathcomp-analysis.override.version = "master";
      mathcomp-real-closed.job = false;
      mathcomp-real-closed.override.version = "master";
      mathcomp-finmap.job = false;
      mathcomp-finmap.override.version = "master";
      mathcomp-word.job = false;
      mathcomp-word.override.version = "main";
      extructures.job = false;
      extructures.override.version = "master";
      deriving.job = false;
      deriving.override.version = "master";
      mathcomp-bigenough.job = false;
      mathcomp-bigenough.override.version = "master";
    }; rocqPackages = {
      rocq-core.override.version = "9.1";
      mathcomp.job = false;
      mathcomp.override.version = "master";
      mathcomp-real-closed.job = false;
      mathcomp-real-closed.override.version = "master";
      mathcomp-finmap.job = false;
      mathcomp-finmap.override.version = "master";
      mathcomp-bigenough.job = false;
      mathcomp-bigenough.override.version = "master";
      mathcomp-analysis.job = false;
      mathcomp-analysis.override.version = "master";
    };
    push-branches = [ "main" ];
  };

  cachix.coq = {};
  cachix.math-comp = {};
  cachix.coq-community = {};
  cachix.ssprove.authToken = "CACHIX_AUTH_TOKEN";
}
