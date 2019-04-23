#!/usr/bin/env nix-shell
#! nix-shell -i bash ../shell.nix

set -eu

name="${1%.*}"

idris --partial-eval "${name}.idr"
