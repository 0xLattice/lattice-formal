#!/usr/bin/env bash
# Planted bugs.  Each mutant breaks one rule of the spec; the model check must
# then FAIL on the named property.  A mutant that passes means the properties
# do not pin that rule.
set -uo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
failures=0

# name | expected violated property | config | sed expression on ForkChoice.tla
mutants=(
  "exclusion-removes-weight|WorkMonotone|MCMain.cfg|s/^Subtree(n, b) == {x \\\\in weighed\[n\]/Subtree(n, b) == {x \\\\in {y \\\\in weighed[n] : AncOrSelf(y) \\\\cap excluded[n] = {}}/"
  "last-observation-wins|Convergence|MCMain.cfg|s/IF o.q > @ THEN o.q ELSE @/o.q/"
  "execute-without-parent|NothingValidatedBelowExcluded|MCMain.cfg|/Parent\[b\] \\\\in validated\[n\] \\\\cup {None}$/d"
  "descend-into-excluded|TipsWellFormed|MCMain.cfg|s/^CanonicalTip(n) == TipOver(n, Selectable(n))/CanonicalTip(n) == TipOver(n, weighed[n])/"
  "tie-breaks-larger-cid|ExpectedAnswer|MCTie.cfg|s/CidRank\[x\] < CidRank\[y\]/CidRank[x] > CidRank[y]/"
  "conflicting-location-accepted-by-arrival|Convergence|MCProbeConflict.cfg|"
)

for m in "${mutants[@]}"; do
  IFS='|' read -r name expect cfg expr <<<"$m"
  work="$(mktemp -d)"
  cp "$root"/specs/*.tla "$root"/specs/*.cfg "$work"/
  if [[ -n "$expr" ]]; then
    sed -i.bak "$expr" "$work/ForkChoice.tla"
    if cmp -s "$work/ForkChoice.tla" "$work/ForkChoice.tla.bak"; then
      echo "MUTANT $name: sed did not apply"; failures=$((failures + 1)); rm -rf "$work"; continue
    fi
  fi
  # Check only the expected property, so another violation found first
  # cannot mask whether this one goes red.
  case "$expect" in
    WorkMonotone|VerdictsPermanent|CatchesUp) kind=PROPERTY ;;
    *) kind=INVARIANT ;;
  esac
  grep -v -E '^(INVARIANTS|PROPERTIES)' "$work/$cfg" > "$work/Mutant.cfg"
  echo "$kind $expect" >> "$work/Mutant.cfg"
  out="$("$root/scripts/tlc.sh" Mutant.cfg "$work" 2>&1)"
  if grep -q -E "(Invariant|Temporal property|Action property) $expect .*violated|$expect is violated" <<<"$out"; then
    echo "MUTANT $name: killed by $expect"
  else
    echo "MUTANT $name: SURVIVED (expected $expect)"; failures=$((failures + 1))
    grep -E "violated|Error|No error" <<<"$out" | head -5
  fi
  rm -rf "$work"
done
exit $((failures > 0))
