{ pkgs ? import <nixpkgs> {} }:

pkgs.stdenv.mkDerivation {
  pname = "lin";
  version = "0.1.0";
  src = ./.;

  nativeBuildInputs = [ pkgs.makeWrapper pkgs.vulkan-headers pkgs.vulkan-loader pkgs.glslang ];

  # Vulkan headers + loader so the gpu/simd driver plugins (std/drivers/*.so)
  # compile against the real ABI rather than hand-rolled structs.
  NIX_CFLAGS_COMPILE = "-I${pkgs.vulkan-headers}/include";

  buildPhase = ''
    runHook preBuild
    $CC -O2 -Wall -Wextra -std=c99 -fopenmp -rdynamic -o lin src/*.c -ldl
    for d in std/drivers/*.c; do
      $CC -O2 -Wall -Wextra -std=c99 -fopenmp -fPIC -shared \
        -I${pkgs.vulkan-headers}/include \
        -o "''${d%.c}.so" "$d" -ldl -L${pkgs.vulkan-loader}/lib
    done
    runHook postBuild
  '';

  installPhase = ''
    runHook preInstall
    mkdir -p $out/bin $out/share/lin/std $out/share/lin/std/drivers
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
