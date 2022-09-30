{
  description = "nix flake for building wasp";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { nixpkgs, flake-utils, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
      in {
        # TODO: make this actually pure instead of using an environment
        devShell = pkgs.mkShell {
          nativeBuildInputs = with pkgs; [
            gnumake
            opam
            python27Full
            python39Full
            python39Packages.pycparser
            python39Packages.lxml
            libcxx
            gmp
            clang_10
            llvmPackages_10.bintools-unwrapped
            wabt
          ];
          shellHook = ''
          export LD_LIBRARY_PATH="$HOME/.opam/4.08.1/lib/z3/:$LD_LIBRARY_PATH"
          export PATH="$PATH:$PWD/wasp"
          # export PATH="$PATH:$PWD/wasp-c/bin"
          eval $(opam env)
          '';
        };
      }
      );
}
