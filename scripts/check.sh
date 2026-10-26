#!/usr/bin/env bash
# Model-check every model that must pass, then every planted bug that must fail.
set -uo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
failures=0
for cfg in MCMain.cfg MCGap.cfg MCTie.cfg \
           MCHierarchy_Main.cfg MCHierarchy_ParentBad.cfg MCHierarchy_P1Gap.cfg MCHierarchy_HeldInvalid.cfg MCHierarchy_HeaderBad.cfg \
           MCHierarchy3_Main.cfg MCHierarchyFork_Main.cfg \
           MCSwapReorg_Main.cfg MCSwapReorg_Replay.cfg \
           MCRecovery_Main.cfg MCRecovery_Node.cfg; do
  out="$("$root/scripts/tlc.sh" "$cfg" 2>&1)"
  if grep -q "No error has been found" <<<"$out"; then
    echo "MODEL $cfg: pass ($(grep -o '[0-9,]* distinct states found, 0 states left' <<<"$out" | tail -1 | cut -d' ' -f1) distinct states)"
  else
    echo "MODEL $cfg: FAIL"; grep -E -A30 "violated|Error" <<<"$out" | head -60; failures=$((failures + 1))
  fi
done
# Witnesses: each must FAIL, showing the scenario a property quantifies over
# is reachable, so the property is not vacuous.
for pair in "MCHierarchyFork_W.cfg NoBackedFork" "MCHierarchyFork_WG.cfg NoBackedGrandchildFork" \
            "MCSwapReorg_WParentReorg.cfg NaiveCanonicalBacking" "MCSwapReorg_WChildReorg.cfg PaidImpliesReleased" \
            "MCSwapReorg_WTwoBranches.cfg ReleasedOnOneBranch" "MCSwapReorg_WRedeem.cfg NoRedeemAfterReorg" \
            "MCSwapReorg_WDemanderSafe.cfg NoSafeReleaseBesideParentFork" \
            "MCRecovery_WLost.cfg NoLostBatchRecovered" "MCRecovery_WConflict.cfg NoConflictRefused" \
            "MCRecovery_WOrder.cfg RevisionMonotone" "MCRecovery_RevisionProbe.cfg RevisionMonotone"; do
  set -- $pair
  out="$("$root/scripts/tlc.sh" "$1" 2>&1)"
  if grep -q "Invariant $2 is violated" <<<"$out"; then
    echo "WITNESS $1: reached ($2 violated, as required)"
  else
    echo "WITNESS $1: NOT reached"; failures=$((failures + 1))
  fi
done
python3 "$root/scripts/mutants.py" || failures=$((failures + 1))
exit $((failures > 0))
