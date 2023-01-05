{
  description = "nix flake for building wasp";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = {
    nixpkgs,
    flake-utils,
    ...
  }:
    flake-utils.lib.eachDefaultSystem (
      system: let
        pkgs = import nixpkgs {inherit system;};

        my_python3_packages = p: [
          # wasp-c
          p.pycparser
          # data wrangling
          p.pandas
          p.numpy
        ];

        my_python3 = pkgs.python39.withPackages my_python3_packages;
      in {
        # TODO: make this actually pure instead of using an environment
        devShell = pkgs.mkShell {
          nativeBuildInputs = with pkgs; [
            gnumake
            opam
            python27Full
            my_python3
            libcxx
            gmp
            clang_10
            llvmPackages_10.bintools-unwrapped
            wabt
          ];
          shellHook = ''
            export LD_LIBRARY_PATH="$HOME/.opam/wasp/lib/z3/:$LD_LIBRARY_PATH"
            export PATH="$PWD/wasp/_build/install/default/bin:$PATH"
            # export PATH="$PATH:$PWD/wasp-c/bin"
            eval $(opam env)
          '';
        };
      }
    );
}
