{
  description = "A very basic flake";

  inputs = {
    nixpkgs.url = "nixpkgs/nixos-23.11";
    flake-utils.url = "github:numtide/flake-utils";
    refinedrust.url = "/home/shinaikakishita/projects/tlsf-verif/refinedrust-dev";
  };

  outputs = { self, nixpkgs, refinedrust, flake-utils }: 
    flake-utils.lib.eachDefaultSystem (system: let
      ocamlFlambda = _: prev: rec {
        ocamlPackages_4_14 = prev.ocamlPackages.overrideScope' (_: prev: {
          ocaml = prev.ocaml.override {flambdaSupport = true;};
        });
        coqPackages_8_17 = prev.coqPackages_8_17.overrideScope' (_: prev: {
          coq = prev.coq.override {
            ocamlPackages_4_14 = ocamlPackages_4_14;
          };
        });
      };
      overlays = [#fenix.overlays.default
        ocamlFlambda];
      pkgs = import nixpkgs {inherit overlays system;};

      coq = {
        pkgs = pkgs.coqPackages_8_17;
        toolchain = [coq.pkgs.coq] ++ coq.pkgs.coq.nativeBuildInputs;
        version = coq.pkgs.coq.coq-version;

        stdpp = {
          version = "4be5fd62ddbd5359f912e2cebb415b015c37e565";
          sha256 = "sha256-9pNWjPy1l1EovcKZchC/23FwlllD/Oa3jEOtN5tDzik=";
        };

        iris = {
          version = "1de1b3112754e14a4968534572e118a23344eafe";
          sha256 = "sha256-Cimb3XxnchPSWVGMSyWmJdLQqHMilw11o2hq/4h8dVQ=";
        };

        lambda-rust = {
          version = "4ec2733cce240e3595c37cb926eb000455be77a4";
          sha256 = "sha256-kX9NIPPOoajuJDVly9qGUCCd3lt8Da2k0dZnDY2zKbY=";
        };
      };
  in
  {
    devShells.default = pkgs.mkShell {
      inputsFrom = [ refinedrust ];
      #dontDetectOcamlConflicts = true;
      packages = with pkgs; [gnumake gnupatch gnused coq.pkgs.QuickChick];
      buildInputs = [
        coq.pkgs.coq
        coq.pkgs.QuickChick
        pkgs.dune_3
        pkgs.asciidoctor
      ];
      propagatedBuildInputs = [ coq.pkgs.QuickChick refinedrust.packages.x86_64-linux.theories ];
    };
  });
}
