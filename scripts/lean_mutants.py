#!/usr/bin/env python3
"""Planted bugs for the Lean model.

    scripts/lean_mutants.py [value-trace-dir...]

Each mutant breaks one rule of the model (lean/LatticeProofs/Model.lean) and
must be killed by what it names:
- "proofs": the proofs must then fail to build, so the theorems depend on
  that rule;
- "traces": the model must then disagree with the implementation on some
  case of the value-transition traces, so the traces pin that rule down.
Rules no theorem states (an action-shape rule, netting) can only be killed by
the traces. With no trace directory, only the proof kills are checked.
"""
import pathlib
import re
import shutil
import subprocess
import sys
import tempfile

LEAN = pathlib.Path(__file__).resolve().parent.parent / "lean"

SEQUENTIAL_BALANCES = """  ds.foldlM
    (fun acc (o, d) =>
      let v : Int := ((acc.get? o).getD 0 : Int) + d
      if v < 0 then none
      else if v = 0 then some (acc.erase o)
      else some (acc.set o v.toNat))
    m"""

# (name, killed by, old text in Model.lean, new text)
MUTANTS = [
    ("withdrawal-leaves-no-spent-marker", {"proofs", "traces"},
     "applyWithdrawals dir parentReceipts (m.set k 0) as",
     "applyWithdrawals dir parentReceipts m as"),
    ("coinbase-pays-reward-without-fees", {"proofs", "traces"},
     "| some r => [(r, (b.reward : Int) + fee b.actions)]",
     "| some r => [(r, (b.reward : Int))]"),
    ("no-fee-rule", {"proofs", "traces"},
     """  guard (totalCredits b.actions + totalDeposited b.actions ≤
         totalDebits b.actions + totalWithdrawn b.actions)
""", ""),
    ("withdrawal-ignores-parent-receipt", {"proofs", "traces"},
     """if m.get? k = some amtW ∧ amtW ≠ 0 ∧
          parentReceipts.get? ⟨dir, dm, amtD, n⟩ = some w then""",
     "if m.get? k = some amtW ∧ amtW ≠ 0 then"),
    ("over-withdrawal", {"proofs", "traces"},
     "if m.get? k = some amtW ∧ amtW ≠ 0 ∧",
     "if (m.get? k).isSome ∧ amtW ≠ 0 ∧"),
    ("deposit-overwrites", {"proofs", "traces"},
     "if m.get? k = none ∧ amt ≠ 0 ∧ amtD ≠ 0 then applyDeposits (m.set k amt) as",
     "if amt ≠ 0 ∧ amtD ≠ 0 then applyDeposits (m.set k amt) as"),
    ("negative-balance-clamped", {"proofs", "traces"},
     "if v < 0 then none",
     "if v < 0 then some (acc.erase o)"),
    ("coinbase-unbounded", {"proofs", "traces"},
     "  guard (coinbaseFits b)\n", ""),
    ("balance-beyond-uint64", {"proofs", "traces"},
     "  guard (balances.all (·.2 ≤ uint64Max))\n", ""),
    # Rules no theorem states: only the implementation traces pin them down.
    ("delta-int64-min-accepted", {"traces"},
     "d != 0 && decide (-int64Max ≤ d) && decide (d ≤ int64Max) && accountActionsValid as",
     "d != 0 && decide (d ≤ int64Max) && accountActionsValid as"),
    ("receipt-zero-demand-accepted", {"traces"},
     "if m.get? k = none ∧ amtD ≠ 0 then applyReceipts (m.set k w) as else none",
     "if m.get? k = none then applyReceipts (m.set k w) as else none"),
    ("deposits-before-withdrawals", {"traces"},
     """  let afterW ← applyWithdrawals dir parentReceipts s.deposits b.actions
  let deposits ← applyDeposits afterW b.actions""",
     """  let afterD ← applyDeposits s.deposits b.actions
  let deposits ← applyWithdrawals dir parentReceipts afterD b.actions"""),
    ("balances-applied-in-sequence", {"traces"},
     """  (ds.map (·.1)).eraseDups.foldlM
    (fun acc o =>
      let v : Int := ((m.get? o).getD 0 : Int) + netDelta ds o
      if v < 0 then none
      else if v = 0 then some (acc.erase o)
      else some (acc.set o v.toNat))
    m""", SEQUENTIAL_BALANCES),
]


def proofs_break(work):
    r = subprocess.run(["lake", "build"], cwd=work, capture_output=True, text=True)
    broken = sorted(set(re.findall(r"^error: (LatticeProofs/\w+\.lean)", r.stdout, re.M)))
    if r.returncode != 0 and "LatticeProofs/Model.lean" in broken:
        return None  # the mutant itself does not compile
    return r.returncode != 0


def traces_disagree(work, traces):
    r = subprocess.run(["lake", "build", "tracecheck"], cwd=work, capture_output=True, text=True)
    if r.returncode != 0:
        return None
    r = subprocess.run([str(work / ".lake/build/bin/tracecheck"), *map(str, traces)],
                       capture_output=True, text=True)
    return r.returncode == 1 and "FAIL" in r.stdout


def main():
    traces = sorted(t for d in sys.argv[1:] for t in pathlib.Path(d).glob("*.json"))
    failures = 0
    for name, killers, old, new in MUTANTS:
        with tempfile.TemporaryDirectory() as d:
            work = pathlib.Path(d) / "lean"
            shutil.copytree(LEAN, work, ignore=shutil.ignore_patterns(".lake"))
            model = work / "LatticeProofs" / "Model.lean"
            text = model.read_text()
            if text.count(old) != 1:
                print(f"MUTANT {name}: replacement matched {text.count(old)} times")
                failures += 1
                continue
            model.write_text(text.replace(old, new))
            results = {}
            if "proofs" in killers:
                results["proofs"] = proofs_break(work)
            if traces and "traces" in killers:
                results["traces"] = traces_disagree(work, traces)
            if not results:
                print(f"MUTANT {name}: skipped (needs traces)")
                continue
            bad = [k for k, v in results.items() if v is not True]
            if any(v is None for v in results.values()):
                print(f"MUTANT {name}: the mutated model does not compile")
                failures += 1
            elif bad:
                print(f"MUTANT {name}: SURVIVED the {', '.join(bad)}")
                failures += 1
            else:
                print(f"MUTANT {name}: killed by the {' and the '.join(sorted(results))}")
    sys.exit(1 if failures else 0)


if __name__ == "__main__":
    main()
