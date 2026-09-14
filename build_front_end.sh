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
# at the last commit before class syntax landed there. An `app` from before the
# command was renamed (D174) reads `GREN_BIN` rather than `GENG_BIN`; give it
# that name for the first build, and the self-check below still applies.
set -e

cd "$(dirname "$(realpath "$0")")"

if [ ! -x geng ]; then
  echo "build_front_end.sh: no ./geng — run ./build_dev_bin.sh first" >&2
  exit 1
fi

if [ ! -f app ]; then
  echo "build_front_end.sh: no ./app to bootstrap from; see the comment in this script" >&2
  exit 1
fi

GENG_BIN="$PWD/geng" node app make Main --output=app.new

# A bootstrap is one bad bundle away from having nothing to build with: an `app`
# that cannot find `gren.json` cannot build its own fix, and it happened once
# (`docs/m1b-classes.md` §G49.2 in geng-lang). So the new bundle has to build
# `Main` itself -- from the artifacts just cached, so this is quick -- and agree
# byte for byte with what the old one built, before it replaces it. The old one
# is kept as `app.prev` either way.
if ! GENG_BIN="$PWD/geng" node app.new make Main --output=app.check >/dev/null 2>&1; then
  echo "build_front_end.sh: the new app.new cannot build Main; app is unchanged" >&2
  exit 1
fi
if ! cmp -s app.new app.check; then
  echo "build_front_end.sh: app.new builds a different bundle than itself; app is unchanged" >&2
  exit 1
fi
rm app.check
cp app app.prev
mv app.new app
