{
  # This is based on an example, if more is required of the flake
  # look at the [source](https://github.com/brendanzab/ocaml-flake-example)
  description = "nix flake for building wasp";

  # Flake dependency specification
  #
  # To update all flake inputs:
  #
  #     $ nix flake update --commit-lockfile
  #
  # To update individual flake inputs:
  #
  #     $ nix flake lock --update-input <input> ... --commit-lockfile
  #
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs";
    # Convenience functions for writing flakes
    flake-utils.url = "github:numtide/flake-utils";
    # Precisely filter files copied to the nix store
    nix-filter.url = "github:numtide/nix-filter";
  };

  outputs = { self, nixpkgs, flake-utils, nix-filter }:
    # Construct an output set that supports a number of default systems
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {inherit system;};
        # OCaml packages available on nixpkgs
        # This functions as a switch
        ocamlPackages = pkgs.ocaml-ng.ocamlPackages_4_14;
        # Library functions from nixpkgs
        lib = pkgs.lib;

        my_python3_packages = p: [
          # wasp-c
          p.pycparser
          # data wrangling
          p.pandas
          p.numpy
        ];
        my_python3 = pkgs.python310.withPackages my_python3_packages;

        # Filtered sources (prevents unecessary rebuilds)
        sources = {
          ocaml = nix-filter.lib {
            root = ./.;
            include = [
              ".ocamlformat"
              "dune-project"
              (nix-filter.lib.inDirectory "wasp")
            ];
          };
        };
      in
      {
        # Exposed packages that can be built or run with `nix build` or
        # `nix run` respectively:
        #
        #     $ nix build .#<name>
        #     $ nix run .#<name> -- <args?>
        #
        packages = {
          # The package that will be built or run by default. For example:
          #
          #     $ nix build
          #     $ nix run -- <args?>
          #
          default = self.packages.${system}.wasp;

          wasp = ocamlPackages.buildDunePackage {
            pname = "wasp";
            version = "0.2.0";
            duneVersion = "3";
            src = sources.ocaml;

            strictDeps = true;

            nativeBuildInputs = [
              (pkgs.z3.override {
                ocamlBindings = true;
                ocaml = ocamlPackages.ocaml;
                findlib = ocamlPackages.findlib;
                zarith = ocamlPackages.zarith;
              })
            ];

            buildInputs = [
              ocamlPackages.z3
              ocamlPackages.batteries
              ocamlPackages.base
            ];

            preBuild = ''
              cd wasp
            '';
          };
        };

        # Development shells
        #
        #    $ nix develop .#<name>
        #    $ nix develop .#<name> --command dune build @test
        #
        # [Direnv](https://direnv.net/) is recommended for automatically loading
        # development environments in your shell. For example:
        #
        #    $ echo "use flake" > .envrc && direnv allow
        #    $ dune build @test
        #
        devShells = {
          default = pkgs.mkShell {
            # Development tools
            packages = with pkgs; [
              # Source file formatting
              nixpkgs-fmt
              ocamlformat
              # For `dune build --watch ...`
              fswatch
              # For `dune build @doc`
              ocamlPackages.odoc
              # OCaml editor support
              ocamlPackages.ocaml-lsp
              # Nicely formatted types on hover
              ocamlPackages.ocamlformat-rpc-lib
              # Fancy REPL thing
              ocamlPackages.utop
              # wasp and wasp-c stuff
              gnumake
              # TODO: Do I need it? python27Full
              my_python3
              libcxx
              gmp
              clang_10
              llvmPackages_10.bintools-unwrapped
              wabt
            ];

            # Tools from packages
            inputsFrom = [
              self.packages.${system}.wasp
            ];
            shellHook = ''
# To allow executing wasp wihtout specifying full path
export PATH="$PWD/wasp/_build/install/default/bin:$PATH"
# To allow executing wasp-c wihtout specifying full path
# libc.a breakes some things
# export PATH="$PATH:$PWD/wasp-c/bin"
            '';
          };
        };
      });
}
