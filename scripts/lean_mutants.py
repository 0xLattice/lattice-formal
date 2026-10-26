#!/usr/bin/env python3
"""Planted bugs for the Lean proofs.

Each mutant breaks one rule of the model (lean/LatticeProofs/Model.lean).
The proofs must then fail to build; a mutant that still builds means the
theorems do not depend on that rule.
"""
import pathlib
import re
import shutil
import subprocess
import sys
import tempfile

LEAN = pathlib.Path(__file__).resolve().parent.parent / "lean"

# (name, old text in Model.lean, new text)
MUTANTS = [
    ("withdrawal-leaves-no-spent-marker",
     "applyWithdrawals dir parentReceipts (m.set k 0) as",
     "applyWithdrawals dir parentReceipts m as"),
    ("coinbase-pays-reward-without-fees",
     "| some r => [(r, (b.reward : Int) + fee b.actions)]",
     "| some r => [(r, (b.reward : Int))]"),
    ("no-fee-rule",
     """  guard (totalCredits b.actions + totalDeposited b.actions ≤
         totalDebits b.actions + totalWithdrawn b.actions)
""", ""),
    ("withdrawal-ignores-parent-receipt",
     """if m.get? k = some amtW ∧ amtW ≠ 0 ∧
          parentReceipts.get? ⟨dir, dm, amtD, n⟩ = some w then""",
     "if m.get? k = some amtW ∧ amtW ≠ 0 then"),
    ("over-withdrawal",
     "if m.get? k = some amtW ∧ amtW ≠ 0 ∧",
     "if (m.get? k).isSome ∧ amtW ≠ 0 ∧"),
    ("deposit-overwrites",
     "if m.get? k = none ∧ amt ≠ 0 ∧ amtD ≠ 0 then applyDeposits (m.set k amt) as",
     "if amt ≠ 0 ∧ amtD ≠ 0 then applyDeposits (m.set k amt) as"),
    ("negative-balance-clamped",
     "if v < 0 then none",
     "if v < 0 then some (acc.erase o)"),
]


def main():
    failures = 0
    for name, old, new in MUTANTS:
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
            r = subprocess.run(["lake", "build"], cwd=work, capture_output=True, text=True)
            broken = sorted(set(re.findall(r"^error: (LatticeProofs/\w+\.lean)", r.stdout, re.M)))
            if r.returncode != 0 and broken and "LatticeProofs/Model.lean" not in broken:
                print(f"MUTANT {name}: killed ({', '.join(broken)} no longer builds)")
            elif r.returncode != 0:
                print(f"MUTANT {name}: model itself fails to build: {broken}")
                failures += 1
            else:
                print(f"MUTANT {name}: SURVIVED (proofs still build)")
                failures += 1
    sys.exit(1 if failures else 0)


if __name__ == "__main__":
    main()
