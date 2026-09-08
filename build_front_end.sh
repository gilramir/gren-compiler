#!/usr/bin/env bash
# Build the front-end bundle `app` — the Gren half of the compiler, which is
# where `geng fmt` lives and what `harness/fmt.py` drives.
#
# It is built by the fork's OWN backend (D134). `gren.json` takes
# `gren-lang/core` as a `local:` path, and `core` on the `geng` branch declares
# classes and writes instances, so no stock compiler can parse it any more:
# `npx gren-lang@0.6.3 gren make` fails with "PROBLEM BUILDING DEPENDENCIES"
# and no detail. The front-end therefore builds itself, with the backend
# `build_dev_bin.sh` has just produced.
#
# That makes this step a bootstrap: it needs an `app` to build the next `app`.
# A checkout with none can produce the first one with stock Gren against `core`
# at the last commit before class syntax landed there.
set -e

cd "$(dirname "$(realpath "$0")")"

if [ ! -x gren ]; then
  echo "build_front_end.sh: no ./gren — run ./build_dev_bin.sh first" >&2
  exit 1
fi

if [ ! -f app ]; then
  echo "build_front_end.sh: no ./app to bootstrap from; see the comment in this script" >&2
  exit 1
fi

GREN_BIN="$PWD/gren" node app make Main --output=app.new
mv app.new app
