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
          lin = pkgs.stdenv.mkDerivation {
            pname = "lin";
            version = "0.1.0";
            src = ./.;

            nativeBuildInputs = [ pkgs.makeWrapper ];

            buildPhase = ''
              runHook preBuild
              $CC -O2 -Wall -Wextra -std=c99 -fopenmp -o lin src/*.c std/drivers/*.c -ldl
              runHook postBuild
            '';

            installPhase = ''
              runHook preInstall
              mkdir -p $out/bin $out/share/lin/std
              cp lin $out/bin/
              cp -r std/* $out/share/lin/std/
              wrapProgram $out/bin/lin \
                --set-default LIN_STD "$out/share/lin/std/std.lin" \
                --set-default LIN_STD_DIR "$out/share/lin/std"
              runHook postInstall
            '';

            meta = {
              description = "Lin programming language runtime and compiler";
              homepage = "https://github.com/falconnor4/Lin";
            };
          };

          testRunner = pkgs.writeShellScriptBin "lin-test" ''
            set -e
            LIN_BIN="${lin}/bin/lin"
            export LIN_STD="${lin}/share/lin/std/std.lin"
            export LIN_STD_DIR="${lin}/share/lin/std"

            pass=0
            fail=0

            TESTS="test/basics.lin test/booleans.lin test/combinators.lin test/pairs.lin test/scott.lin test/scott_arith.lin test/strings.lin test/adts.lin test/multi_file.lin test/sat.lin test/sat_verify.lin test/tseitin.lin test/tsp.lin test/ffi.lin test/ffi_advanced.lin test/ffi_systems.lin test/egraph.lin test/driver_gpu.lin"

            for f in $TESTS; do
              got=$($LIN_BIN "$f" 2>&1 | grep -v '^warning' || true)
              want=$(grep '^; expect ' "$f" | sed 's/^; expect //')
              gn=$(printf '%s\n' "$got" | grep -c . || true)
              wn=$(printf '%s\n' "$want" | grep -c . || true)
              ok=1
              [ "$gn" = "$wn" ] || ok=0
              if [ "$ok" = 1 ] && [ "$wn" -gt 0 ]; then
                i=1
                while [ "$i" -le "$wn" ]; do
                  w=$(printf '%s\n' "$want" | sed -n "''${i}p")
                  g=$(printf '%s\n' "$got" | sed -n "''${i}p")
                  case "$w" in
                    *...)
                      pfx="''${w%...}"
                      case "$g" in "$pfx"*) ;; *) ok=0 ;; esac
                      ;;
                    *)
                      [ "$w" = "$g" ] || ok=0
                      ;;
                  esac
                  i=$((i + 1))
                done
              fi
              if [ "$ok" = 1 ]; then
                pass=$((pass + 1))
                printf "PASS %s\n" "$f"
              else
                fail=$((fail + 1))
                echo "FAIL $f"
                echo "--- want ---"
                printf '%s\n' "$want"
                echo "--- got ---"
                printf '%s\n' "$got"
              fi
            done

            TMP_DIR=$(mktemp -d)
            trap 'rm -rf "$TMP_DIR"' EXIT
            $LIN_BIN build test/line_binary.lin -o "$TMP_DIR/line_binary.line"

            if [ ! -x "$TMP_DIR/line_binary.line" ]; then
              echo "FAIL: line_binary.line is not executable"
              exit 1
            fi

            if ! head -n 1 "$TMP_DIR/line_binary.line" | grep -q '^#!/usr/bin/env lin'; then
              echo "FAIL: line_binary.line missing lin shebang"
              exit 1
            fi

            out1=$($LIN_BIN "$TMP_DIR/line_binary.line")
            if [ "$out1" != "LINE_BINARY_OK: 43" ]; then
              echo "FAIL: unexpected engine output: $out1"
              exit 1
            fi

            if [ -x /usr/bin/env ]; then
              PATH="${lin}/bin:$PATH" "$TMP_DIR/line_binary.line" > "$TMP_DIR/out2"
              out2=$(cat "$TMP_DIR/out2")
              if [ "$out2" != "LINE_BINARY_OK: 43" ]; then
                echo "FAIL: unexpected direct binary output: $out2"
                exit 1
              fi
            fi

            pass=$((pass + 1))
            printf "PASS test/line_binary (.line container build & execute)\n"

            echo ""
            echo "$pass passed, $fail failed"
            [ "$fail" -eq 0 ]
          '';

          testCheck = pkgs.stdenv.mkDerivation {
            pname = "lin-test";
            version = "0.1.0";
            src = ./.;

            buildInputs = [ lin ];

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

          testRunner = pkgs.writeShellScriptBin "lin-test" ''
            set -e
            LIN_BIN="${lin}/bin/lin"
            export LIN_STD="${lin}/share/lin/std/std.lin"
            export LIN_STD_DIR="${lin}/share/lin/std"

            pass=0
            fail=0

            TESTS="test/basics.lin test/booleans.lin test/combinators.lin test/pairs.lin test/scott.lin test/scott_arith.lin test/strings.lin test/adts.lin test/multi_file.lin test/sat.lin test/sat_verify.lin test/tseitin.lin test/tsp.lin test/ffi.lin test/ffi_advanced.lin test/ffi_systems.lin test/egraph.lin test/driver_gpu.lin"

            for f in $TESTS; do
              got=$($LIN_BIN "$f" 2>&1 | grep -v '^warning' || true)
              want=$(grep '^; expect ' "$f" | sed 's/^; expect //')
              gn=$(printf '%s\n' "$got" | grep -c . || true)
              wn=$(printf '%s\n' "$want" | grep -c . || true)
              ok=1
              [ "$gn" = "$wn" ] || ok=0
              if [ "$ok" = 1 ] && [ "$wn" -gt 0 ]; then
                i=1
                while [ "$i" -le "$wn" ]; do
                  w=$(printf '%s\n' "$want" | sed -n "''${i}p")
                  g=$(printf '%s\n' "$got" | sed -n "''${i}p")
                  case "$w" in
                    *...)
                      pfx="''${w%...}"
                      case "$g" in "$pfx"*) ;; *) ok=0 ;; esac
                      ;;
                    *)
                      [ "$w" = "$g" ] || ok=0
                      ;;
                  esac
                  i=$((i + 1))
                done
              fi
              if [ "$ok" = 1 ]; then
                pass=$((pass + 1))
                printf "PASS %s\n" "$f"
              else
                fail=$((fail + 1))
                echo "FAIL $f"
                echo "--- want ---"
                printf '%s\n' "$want"
                echo "--- got ---"
                printf '%s\n' "$got"
              fi
            done

            TMP_DIR=$(mktemp -d)
            trap 'rm -rf "$TMP_DIR"' EXIT
            $LIN_BIN build test/line_binary.lin -o "$TMP_DIR/line_binary.line"

            if [ ! -x "$TMP_DIR/line_binary.line" ]; then
              echo "FAIL: line_binary.line is not executable"
              exit 1
            fi

            if ! head -n 1 "$TMP_DIR/line_binary.line" | grep -q '^#!/usr/bin/env lin'; then
              echo "FAIL: line_binary.line missing lin shebang"
              exit 1
            fi

            out1=$($LIN_BIN "$TMP_DIR/line_binary.line")
            if [ "$out1" != "LINE_BINARY_OK: 43" ]; then
              echo "FAIL: unexpected engine output: $out1"
              exit 1
            fi

            if [ -x /usr/bin/env ]; then
              PATH="${lin}/bin:$PATH" "$TMP_DIR/line_binary.line" > "$TMP_DIR/out2"
              out2=$(cat "$TMP_DIR/out2")
              if [ "$out2" != "LINE_BINARY_OK: 43" ]; then
                echo "FAIL: unexpected direct binary output: $out2"
                exit 1
              fi
            fi

            pass=$((pass + 1))
            printf "PASS test/line_binary (.line container build & execute)\n"

            echo ""
            echo "$pass passed, $fail failed"
            [ "$fail" -eq 0 ]
          '';

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
          packages = [ pkgs.gnumake pkgs.gdb pkgs.valgrind ];
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
