{ compiler ? "ghc844"
, config ? import ./config.nix
, overlays ? import ./overlays.nix { inherit compiler; }
}:

let
  nixpkgs-args = builtins.fromJSON (builtins.readFile ./nixpkgs.json);

  nixpkgs = with nixpkgs-args; builtins.fetchTarball {
    url = "https://github.com/${owner}/${repo}/archive/${rev}.tar.gz";
    inherit sha256;
  };

  pkgs = import nixpkgs { inherit config overlays; };
in
  pkgs
