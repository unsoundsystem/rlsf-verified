{
  description = "A very basic flake";

  inputs = {
    nixpkgs.url = "nixpkgs/nixos-23.11";
    flake-utils.url = "github:numtide/flake-utils";
    refinedrust.url = "/home/shinaikakishita/projects/tlsf-verif/refinedrust-dev";
  };

  outputs = { self, nixpkgs, refinedrust, flake-utils }: flake-utils.lib.eachDefaultSystem (system: let
      pkgs = import nixpkgs {inherit system;};
  in
  {
    devShells.default = pkgs.mkShell {
      #inputsFrom = [ refinedrust ];
      dontDetectOcamlConflicts = true;
      packages = with pkgs; [gnumake gnupatch gnused dune_3]
        ++ (with pkgs.coqPackages_8_17; [ QuickChick ]) ++ refinedrust.packages.x86_64-linux.theories.buildInputs;
        propagatedBuildInputs = [ refinedrust.packages.x86_64-linux.theories ];
    };
  });
}
