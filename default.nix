{ pkgs ? import <nixpkgs> {} }:

# The ONE build recipe for Lin.  flake.nix, shell.nix and `nix-build default.nix` all come through
# here, and that is deliberate: the flake used to carry its own copy, and the two had drifted --
# the flake built the Vulkan shader (reduce.spv is gitignored, so it must be regenerated) while this
# file did not, and this file set NIX_CFLAGS_COMPILE while the flake did not.  Same source, two
# different artifacts, depending on which entry point you used.  Anything that builds Lin goes
# through this file; adding a build step in only one place is the bug this prevents.
pkgs.stdenv.mkDerivation {
  pname = "lin";
  version = "0.1.0";
  src = ./.;

  nativeBuildInputs = [ pkgs.makeWrapper pkgs.vulkan-headers pkgs.vulkan-loader pkgs.glslang ];

  # Vulkan headers + loader so the gpu/simd driver plugins (std/drivers/*.so)
  # compile against the real ABI rather than hand-rolled structs.
  NIX_CFLAGS_COMPILE = "-I${pkgs.vulkan-headers}/include";

  # NOTE: this recipe is deliberately NOT delegated to the Makefile, which spells the same commands
  # out for `make all` / `make test`.  It was tried and reverted on a measurement: `make lin plugins`
  # builds a binary that links libgomp but leaves libgomp.so.1 out of the derivation's closure, so the
  # artifact dies at startup with "error while loading shared libraries: libgomp.so.1" and every suite
  # reports 0 of N assertions.  Invoking $CC directly is what makes the Nix gcc wrapper register the
  # OpenMP runtime as a runtime dependency.  Deduplicating two copies of a flag list is not worth a
  # binary that cannot start; a future attempt has to solve the closure question first.
  buildPhase = ''
    runHook preBuild
    # src/*.c is the core.  src/egraph.inc is the e-graph AOT pass, `#include`d by compile.c: it
    # is part of that translation unit, and -- being neither .c nor .h -- outside the core line
    # budget test/run_tests.sh enforces.
    $CC -O2 -Wall -Wextra -std=c99 -fopenmp -rdynamic -o lin src/*.c -ldl -lm
    for d in std/drivers/*.c; do
      $CC -O2 -Wall -Wextra -std=c99 -fopenmp -fPIC -shared \
        -I${pkgs.vulkan-headers}/include \
        -o "''${d%.c}.so" "$d" -ldl -lm -L${pkgs.vulkan-loader}/lib
    done
    # reduce.spv is a build artifact and gitignored, so it must be regenerated here rather than
    # staged; it is what the gpu driver dispatches to.
    ${pkgs.glslang}/bin/glslangValidator -V std/drivers/reduce.comp -o std/drivers/reduce.spv
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
}
