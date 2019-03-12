let
  pkgs = import ./nix/nixpkgs {};

  idris = pkgs.idrisPackages.with-packages (with pkgs.idrisPackages; [
    prelude
    base
    contrib
  ]);
in
  pkgs.stdenv.mkDerivation {
    name = "idris-sandbox";

    buildInputs = [
      idris
      pkgs.ncurses
      pkgs.gmp
    ];

    shellHook = builtins.readFile ./nix/bash-prompt.sh;
  }
