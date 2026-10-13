#!/usr/bin/env bash
# Build the backend `geng` the way a release is built: the cabal file's own
# `-O2`, with `-Werror`. This is what `devbox run build` makes, so it is what
# the gates and a user's `geng make` run (geng-lang D691). The `-O0` binary of
# `build_dev_bin.sh`, `devbox run build-dev`, builds faster and runs 5 to 7
# times slower (`m3-sweep.md` §SW40.1).
#
# Cabal builds both into the same place, so changing from one to the other
# rebuilds the whole package.
set -e

cabal build
cp `cabal list-bin .` .
