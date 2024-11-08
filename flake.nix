{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = {
    self,
    nixpkgs,
    flake-utils,
  }:
    flake-utils.lib.eachDefaultSystem (
      system: let
        pkgs = nixpkgs.legacyPackages.${system};
      in {
        devShells.default = pkgs.mkShell {
          buildInputs = with pkgs; [
            (agda.withPackages
              (ps: [
                ps.standard-library
                # ps.agda-categories
                (ps.agda-categories.overrideAttrs (oldAttrs: {
                  version = "local version";
                  src = /Users/Brasolin/pb/agda-categories;
                  # version = "bleeding edge";
                  # src = fetchFromGitHub {
                  #   repo = "agda-stdlib";
                  #   owner = "agda";
                  #   rev = "master";
                  #   hash = "sha256-DfA1xE1ylk2O9Y9sE7fnK3T9/Zr2GMfmnzr9MHR5oHE=";
                  # };
                }))
              ]))
          ];
        };
      }
    );
}
