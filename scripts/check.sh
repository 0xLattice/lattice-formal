#!/usr/bin/env bash
# Model-check every model that must pass, then every planted bug that must fail.
set -uo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
failures=0
for cfg in MCMain.cfg MCGap.cfg MCTie.cfg \
           MCHierarchy_Main.cfg MCHierarchy_P2Bad.cfg MCHierarchy_P1Gap.cfg; do
  out="$("$root/scripts/tlc.sh" "$cfg" 2>&1)"
  if grep -q "No error has been found" <<<"$out"; then
    echo "MODEL $cfg: pass ($(grep -o '[0-9,]* distinct states found, 0 states left' <<<"$out" | tail -1 | cut -d' ' -f1) distinct states)"
  else
    echo "MODEL $cfg: FAIL"; grep -E -A30 "violated|Error" <<<"$out" | head -60; failures=$((failures + 1))
  fi
done
python3 "$root/scripts/mutants.py" || failures=$((failures + 1))
exit $((failures > 0))
