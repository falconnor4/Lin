{ pkgs ? import <nixpkgs> {} }:

let
  lin = import ./default.nix { inherit pkgs; };
in
pkgs.mkShell {
  inputsFrom = [ lin ];
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
}
