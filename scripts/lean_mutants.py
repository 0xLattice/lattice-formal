#!/usr/bin/env python3
"""Planted bugs for the Lean model.

    scripts/lean_mutants.py [value-trace-dir...]

Each mutant breaks one rule of the value model (lean/LatticeProofs/Model.lean)
or of the Merkle trie model (lean/LatticeProofs/Merkle.lean) and must be
killed by what it names:
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

# (name, killed by, old text, new text[, model file, Model.lean by default])
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
    # Cross-chain swaps (Swap.lean).
    ("withdrawal-checks-own-receipts", {"proofs", "traces"},
     "let afterW ← applyWithdrawals dir parentReceipts s.deposits b.actions",
     "let afterW ← applyWithdrawals dir s.receipts s.deposits b.actions"),
    ("receipt-key-drops-directory", {"proofs", "traces"},
     "      let k : ReceiptKey := ⟨d, dm, amtD, n⟩",
     "      let k : ReceiptKey := ⟨\"\", dm, amtD, n⟩"),
    ("receipt-overwrites", {"proofs", "traces"},
     "if m.get? k = none ∧ amtD ≠ 0 then applyReceipts (m.set k w) as else none",
     "if amtD ≠ 0 then applyReceipts (m.set k w) as else none"),
    ("receipt-credits-no-demander", {"proofs", "traces"},
     "(w, -(amt : Int)) :: (dm, (amt : Int)) :: accountActions as",
     "(w, -(amt : Int)) :: accountActions as"),
    ("withdrawal-ignores-receipt-withdrawer", {"proofs", "traces"},
     "parentReceipts.get? ⟨dir, dm, amtD, n⟩ = some w then",
     "(parentReceipts.get? ⟨dir, dm, amtD, n⟩).isSome then"),
    ("deposits-before-withdrawals", {"proofs", "traces"},
     """  let afterW ← applyWithdrawals dir parentReceipts s.deposits b.actions
  let deposits ← applyDeposits afterW b.actions""",
     """  let afterD ← applyDeposits s.deposits b.actions
  let deposits ← applyWithdrawals dir parentReceipts afterD b.actions"""),
    # Rules no theorem states: only the implementation traces pin them down.
    ("burned-coinbase-bounded", {"traces"},
     "  | none => true\n",
     "  | none => decide ((b.reward : Int) + fee b.actions ≤ int64Max)\n"),
    ("delta-int64-min-accepted", {"traces"},
     "d != 0 && decide (-int64Max ≤ d) && decide (d ≤ int64Max) && accountActionsValid as",
     "d != 0 && decide (d ≤ int64Max) && accountActionsValid as"),
    ("receipt-zero-demand-accepted", {"traces"},
     "if m.get? k = none ∧ amtD ≠ 0 then applyReceipts (m.set k w) as else none",
     "if m.get? k = none then applyReceipts (m.set k w) as else none"),
    ("balances-applied-in-sequence", {"traces"},
     """  (ds.map (·.1)).eraseDups.foldlM
    (fun acc o =>
      let v : Int := ((m.get? o).getD 0 : Int) + netDelta ds o
      if v < 0 then none
      else if v = 0 then some (acc.erase o)
      else some (acc.set o v.toNat))
    m""", SEQUENTIAL_BALANCES),
    # The Merkle trie (cashew's radix trie): only the proofs pin these down.
    ("delete-skips-collapse", {"proofs"},
     "      | .delete, some _ => collapse p ks",
     "      | .delete, some _ => some (some (.node p none ks))", "Merkle.lean"),
    ("digest-ignores-prefix", {"proofs"},
     "  | .node p v ks => H (.node p v (ks.digests H))",
     "  | .node _ v ks => H (.node [] v (ks.digests H))", "Merkle.lean"),
    ("stub-read-as-absent-on-insert", {"proofs"},
     """    if c' = c then
      match t.apply o (c :: r) with""",
     """    if c' = c then
      match t with
      | .stub _ => .missing
      | t =>
      match t.apply o (c :: r) with""", "Merkle.lean"),
    ("split-keeps-old-prefix", {"proofs"},
     "(.cons c (.node (c :: r) val ks) .nil)",
     "(.cons c (.node (k ++ c :: r) val ks) .nil)", "Merkle.lean"),
    ("root-count-not-moved", {"proofs"},
     "some ⟨s.count + o.delta, ks⟩",
     "some ⟨s.count, ks⟩", "Merkle.lean"),
    ("children-not-sorted", {"proofs"},
     "if c < c' then .cons c t (.cons c' t' rest) else .cons c' t' (rest.ins c t)",
     ".cons c t (.cons c' t' rest)", "Merkle.lean"),
    ("insert-overwrites", {"proofs"},
     "      | .insert v, none => some (some (.node p (some v) ks))",
     "      | .insert v, _ => some (some (.node p (some v) ks))", "Merkle.lean"),
    ("delete-at-absent-key-succeeds", {"proofs"},
     "      | .delete, some _ => collapse p ks",
     "      | .delete, _ => collapse p ks", "Merkle.lean"),
    ("collapse-merges-a-stub", {"proofs"},
     "    | .stub _ => none\n    | .node p' v' ks' => some (some (.node (p ++ p') v' ks'))",
     "    | .stub d => some (some (.stub d))\n    | .node p' v' ks' => some (some (.node (p ++ p') v' ks'))",
     "Merkle.lean"),
    ("digest-ignores-count", {"proofs"},
     "  H (.root s.count (s.kids.digests H))",
     "  H (.root 0 (s.kids.digests H))", "Merkle.lean"),
    # Work from targets (Work.lean): only the proofs pin these down.
    ("work-exclusive-form", {"proofs"},
     "  else (N - 1 - t) / (t + 1) + 1\n\n/-- `workForHash",
     "  else (N - 1) / t\n\n/-- `workForHash", "Work.lean"),
    ("work-target-zero-credited-floor", {"proofs"},
     "  if t = 0 then 0\n  else if N - 1 ≤ t then 1\n  else (N - 1 - t) / (t + 1) + 1\n\n/-- `workForHash",
     "  if t = 0 then N\n  else if N - 1 ≤ t then 1\n  else (N - 1 - t) / (t + 1) + 1\n\n/-- `workForHash",
     "Work.lean"),
    ("pow-target-zero-met", {"proofs"},
     "def Meets (t h : Nat) : Prop := 0 < t ∧ h ≤ t",
     "def Meets (t h : Nat) : Prop := True ∧ h ≤ t", "Work.lean"),
    ("ladder-terminal-target-unchecked", {"proofs"},
     "  if Meets tT h then max (rootMost N cs h) (workForTarget N tT) else 0",
     "  max (rootMost N cs h) (workForTarget N tT)", "Work.lean"),
    ("ladder-max-over-beaten", {"proofs"},
     "  | t :: cs, h => if Meets t h then workForTarget N t else rootMost N cs h",
     "  | t :: cs, h => if Meets t h then max (workForTarget N t) (rootMost N cs h) else rootMost N cs h",
     "Work.lean"),
    # Encodings (Keys.lean): only the proofs pin these down.
    ("pow-recipient-untagged", {"proofs"},
     "  | some r => '\\x01' :: r", "  | some r => r", "Keys.lean"),
    ("pow-height-timestamp-unseparated", {"proofs"},
     "B.children, decimal B.height, decimalInt B.timestamp, recipientField",
     "B.children, decimal B.height ++ decimalInt B.timestamp, recipientField", "Keys.lean"),
    ("deposit-key-amount-nonce-unseparated", {"proofs"},
     "  k.demander.toList ++ '/' :: (decimal k.amountDemanded ++ '/' :: decimal k.nonce)",
     "  k.demander.toList ++ '/' :: (decimal k.amountDemanded ++ decimal k.nonce)", "Keys.lean"),
    ("directory-may-contain-slash", {"proofs"},
     "def ValidDirectory (s : Text) : Prop := VisibleAscii s ∧ '/' ∉ s",
     "def ValidDirectory (s : Text) : Prop := VisibleAscii s", "Keys.lean"),
    ("receipt-domain-dropped", {"proofs"},
     "def receiptPreimage (k : ReceiptKey) : Text := receiptDomain ++ receiptText k",
     "def receiptPreimage (k : ReceiptKey) : Text := receiptText k", "Keys.lean"),
    ("receipt-path-hashes-deposit-text", {"proofs"},
     "def receiptPreimage (k : ReceiptKey) : Text := receiptDomain ++ receiptText k",
     "def receiptPreimage (k : ReceiptKey) : Text :=\n  receiptDomain ++ depositText ⟨k.demander, k.amountDemanded, k.nonce⟩",
     "Keys.lean"),
    ("cid-padding-unchecked", {"proofs"},
     "        if valR 32 ds.reverse % 4 = 0 ∧ valR 32 ds.reverse / 4 / 2 ^ 256 = cidPrefix then",
     "        if valR 32 ds.reverse / 4 / 2 ^ 256 = cidPrefix then", "Keys.lean"),
]


def proofs_break(work, file):
    r = subprocess.run(["lake", "build"], cwd=work, capture_output=True, text=True)
    broken = sorted(set(re.findall(r"^error: (LatticeProofs/\w+\.lean)", r.stdout, re.M)))
    if r.returncode != 0 and f"LatticeProofs/{file}" in broken:
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
    for name, killers, old, new, *file in MUTANTS:
        file = file[0] if file else "Model.lean"
        with tempfile.TemporaryDirectory() as d:
            work = pathlib.Path(d) / "lean"
            shutil.copytree(LEAN, work, ignore=shutil.ignore_patterns(".lake"))
            model = work / "LatticeProofs" / file
            text = model.read_text()
            if text.count(old) != 1:
                print(f"MUTANT {name}: replacement matched {text.count(old)} times")
                failures += 1
                continue
            model.write_text(text.replace(old, new))
            results = {}
            if "proofs" in killers:
                results["proofs"] = proofs_break(work, file)
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
