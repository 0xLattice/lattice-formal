#!/usr/bin/env bash
# Run TLC on one model: scripts/tlc.sh <config> [spec-dir]
# <Module>_<name>.cfg checks <Module>.tla; any other <name>.cfg checks MC.tla.
# Fetches the pinned tla2tools.jar on first use and verifies its hash.
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
cfg="$1"
dir="${2:-$root/specs}"
jar="$root/.tools/tla2tools.jar"
version="v1.7.4"
sha="936a262061c914694dfd669a543be24573c45d5aa0ff20a8b96b23d01e050e88"
if [[ ! -f "$jar" ]]; then
  mkdir -p "$root/.tools"
  curl -sSfL -o "$jar" "https://github.com/tlaplus/tlaplus/releases/download/$version/tla2tools.jar"
fi
echo "$sha  $jar" | shasum -a 256 -c - >/dev/null
java="${JAVA:-java}"
meta="$(mktemp -d)"
trap 'rm -rf "$meta"' EXIT
module="MC"
[[ "$cfg" == *_* ]] && module="${cfg%%_*}"
cd "$dir"
# Models end in quiescent states, so deadlock checking is off by default.
# Trace checks set TLC_CHECK_DEADLOCK=1: there a deadlock is an event the
# spec does not allow.
deadlock="-deadlock"
[[ "${TLC_CHECK_DEADLOCK:-}" == 1 ]] && deadlock=""
# $deadlock is deliberately unquoted: empty means no flag.
"$java" -XX:+UseParallelGC -cp "$jar" tlc2.TLC -workers auto $deadlock \
  -metadir "$meta" -config "$cfg" "$module.tla"
