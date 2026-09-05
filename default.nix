{ pkgs ? import <nixpkgs> {} }:

pkgs.stdenv.mkDerivation {
  pname = "lin";
  version = "0.1.0";
  src = ./.;

  nativeBuildInputs = [ pkgs.makeWrapper ];

  buildPhase = ''
    runHook preBuild
    $CC -O2 -Wall -Wextra -std=c99 -fopenmp -o lin src/*.c -ldl
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
