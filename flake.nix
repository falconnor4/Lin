{
  description = "Lin - Pure untyped lambda calculus on interaction nets";

  inputs = {
    nixpkgs.url = "nixpkgs";
  };

  outputs = { self, nixpkgs }:
    let
      supportedSystems = [ "x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin" ];
      forAllSystems = f: nixpkgs.lib.genAttrs supportedSystems (system: f system (import nixpkgs { inherit system; }));
    in {
      packages = forAllSystems (system: pkgs:
        let
          # One build recipe, shared with shell.nix and `nix-build default.nix`.  It used to be a
          # second copy here, and the copies had drifted (this one built the Vulkan shader, that one
          # set NIX_CFLAGS_COMPILE); see the comment in default.nix.
          lin = import ./default.nix { inherit pkgs; };

          # The suite definition lives in test/run_tests.sh, which is the single source of truth
          # for this CI path, for `make test` and for the examples sweep.  It used to be
          # copy-pasted here, and the copy had drifted in two ways that mattered: it ran 46 suites
          # where test/run_tests.sh ran 57, so a test added to run_tests.sh alone never reached CI;
          # and it asserted a container shebang (`#!/usr/bin/env lin`) that the engine does not
          # write -- it writes `#!<realpath argv[0]>` -- which turned a real container bug into an
          # apparently cosmetic test failure.  Delegating makes the two paths measure the same
          # thing by construction instead of by discipline.
          testRunner = pkgs.writeShellScriptBin "lin-test" ''
            set -e
            export LIN_BIN="${lin}/bin/lin"
            export LIN_STD="${lin}/share/lin/std/std.lin"
            export LIN_STD_DIR="${lin}/share/lin/std"
            # Both are passed through: the packaged std is where the driver plugins live, and
            # run_tests.sh needs the directory rather than just the prelude path.
            exec bash test/run_tests.sh "$LIN_BIN" "$LIN_STD_DIR"
          '';

          testCheck = pkgs.stdenv.mkDerivation {
            pname = "lin-test";
            version = "0.1.0";
            src = ./.;

            buildInputs = [ lin pkgs.python3 ];   # test/soundness_enum.py is invoked as `python3`

            buildPhase = ''
              ${testRunner}/bin/lin-test
              mkdir -p $out
              echo "All tests passed successfully" > $out/test-results.txt
            '';

            dontInstall = true;

            meta = {
              description = "Lin test suite";
            };
          };
        in {
          default = lin;
          lin = lin;
          testRunner = testRunner;
          test = testCheck;
        }
      );

      checks = forAllSystems (system: pkgs: {
        default = self.packages.${system}.test;
        test = self.packages.${system}.test;
      });

      apps = forAllSystems (system: pkgs:
        let
          lin = self.packages.${system}.lin;
          testRunner = self.packages.${system}.testRunner;

          # Lin against C (bench/run.sh): the packaged lin, its std and drivers, against clang-level C.
          benchRunner = pkgs.writeShellScriptBin "lin-bench" ''
            export PATH="${pkgs.stdenv.cc}/bin:${pkgs.gawk}/bin:${pkgs.coreutils}/bin:$PATH"
            export LIN_STD="${lin}/share/lin/std/std.lin" LIN_STD_DIR="${lin}/share/lin/std"
            exec bash ${./bench}/run.sh "${lin}/bin/lin"
          '';
        in {
          default = {
            type = "app";
            program = "${lin}/bin/lin";
            meta.description = "Lin interpreter";
          };
          test = {
            type = "app";
            program = "${testRunner}/bin/lin-test";
            meta.description = "Run Lin test suite";
          };
          bench = {
            type = "app";
            program = "${benchRunner}/bin/lin-bench";
            meta.description = "Lin against C (bench/run.sh)";
          };
        }
      );

      devShells = forAllSystems (system: pkgs: {
        default = pkgs.mkShell {
          # The toolchain the package builds with -- NOT the package itself: listing it here rebuilt
          # lin on every edit just to enter the shell, and put a stale `lin` first on PATH.
          inputsFrom = [ self.packages.${system}.lin ];
          packages = [ pkgs.gnumake pkgs.gdb pkgs.valgrind pkgs.python3 ];
          shellHook = ''
            nix() {
              if [ "$1" = "test" ]; then
                shift
                command nix flake check "$@"
              else
                command nix "$@"
              fi
            }
            export -f nix
          '';
        };
      });
    };
}
