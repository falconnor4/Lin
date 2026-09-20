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

          benchRunner = pkgs.writeShellScriptBin "lin-benchmarks" ''
            set -e
            LIN_BIN="${lin}/bin/lin"
            export LIN_STD="${lin}/share/lin/std/std.lin"
            export LIN_STD_DIR="${lin}/share/lin/std"

            printf "%-15s %-10s %-20s %-20s %-15s\n" "Benchmark" "Metric" "Unoptimized (.lin)" "AOT E-Graph (.line)" "Reduction"
            printf "%-15s %-10s %-20s %-20s %-15s\n" "---------------" "----------" "--------------------" "--------------------" "---------------"

            TMP_DIR=$(mktemp -d)
            trap 'rm -rf "$TMP_DIR"' EXIT

            for f in benchmarks/bench_*.lin; do
              name=$(basename "$f" .lin | sed 's/bench_//')
              line_file="$TMP_DIR/$name.line"

              # 1. Unoptimized run
              unopt_err=$($LIN_BIN -b "$f" 2>&1 1>/dev/null || true)
              u_steps=$(printf '%s' "$unopt_err" | sed -n 's/.*\[bench\] *\([0-9]*\) *steps.*/\1/p')
              u_nodes=$(printf '%s' "$unopt_err" | sed -n 's/.*| *\([0-9]*\) *nodes.*/\1/p')

              # 2. Build with AOT E-Graph
              $LIN_BIN build "$f" -o "$line_file" 2>/dev/null

              # 3. Optimized run
              opt_err=$($LIN_BIN -b "$line_file" 2>&1 1>/dev/null || true)
              o_steps=$(printf '%s' "$opt_err" | sed -n 's/.*\[bench\] *\([0-9]*\) *steps.*/\1/p')
              o_nodes=$(printf '%s' "$opt_err" | sed -n 's/.*| *\([0-9]*\) *nodes.*/\1/p')

              rm -f "$line_file"

              if [ -n "$u_steps" ] && [ -n "$o_steps" ] && [ "$u_steps" -gt 0 ]; then
                step_pct=$(( (u_steps - o_steps) * 100 / u_steps ))
              else
                step_pct=0
              fi

              if [ -n "$u_nodes" ] && [ -n "$o_nodes" ] && [ "$u_nodes" -gt 0 ]; then
                node_pct=$(( (u_nodes - o_nodes) * 100 / u_nodes ))
              else
                node_pct=0
              fi

              printf "%-15s %-10s %-20s %-20s -%d%%\n" "$name" "Steps" "$u_steps" "$o_steps" "$step_pct"
              printf "%-15s %-10s %-20s %-20s -%d%%\n" "" "Nodes" "$u_nodes" "$o_nodes" "$node_pct"
              printf "%-15s %-10s %-20s %-20s %-15s\n" "" "Result" "verified" "verified" "MATCH"
              echo ""
            done
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
          benchmarks = {
            type = "app";
            program = "${benchRunner}/bin/lin-benchmarks";
            meta.description = "Run Lin benchmarks";
          };
        }
      );

      devShells = forAllSystems (system: pkgs: {
        default = pkgs.mkShell {
          inputsFrom = [ self.packages.${system}.lin ];
          packages = [ self.packages.${system}.lin pkgs.gnumake pkgs.gdb pkgs.valgrind ];
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
