#!/usr/bin/env python3
"""Planted bugs.

Each mutant breaks one rule of the spec by replacing exactly one piece of a
spec file. The model check must then FAIL on the named property, checked
alone so another violation found first cannot mask it. A mutant that passes
means the properties do not pin that rule.
"""
import pathlib
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
TEMPORAL = {"WorkMonotone", "VerdictsPermanent", "CatchesUp"}

# (name, property that must go red, config, file, old text, new text)
MUTANTS = [
    # Single-chain fork choice (ForkChoice.tla)
    ("exclusion-removes-weight", "WorkMonotone", "MCMain.cfg", "ForkChoice.tla",
     r"Subtree(n, b) == {x \in weighed[n] :",
     r"Subtree(n, b) == {x \in {y \in weighed[n] : AncOrSelf(y) \cap excluded[n] = {}} :"),
    ("last-observation-wins", "Convergence", "MCMain.cfg", "ForkChoice.tla",
     "IF o.q > @ THEN o.q ELSE @", "o.q"),
    ("execute-without-parent", "NothingValidatedBelowExcluded", "MCMain.cfg", "ForkChoice.tla",
     r"    /\ Parent[b] \in validated[n] \cup {None}" + "\n", ""),
    ("descend-into-excluded", "TipsWellFormed", "MCMain.cfg", "ForkChoice.tla",
     "CanonicalTip(n) == TipOver(n, Selectable(n))",
     "CanonicalTip(n) == TipOver(n, weighed[n])"),
    ("tie-breaks-larger-cid", "ExpectedAnswer", "MCTie.cfg", "ForkChoice.tla",
     "CidRank[x] < CidRank[y]", "CidRank[x] > CidRank[y]"),
    # Assumption probe: needs a SHA-256 collision; no spec change.
    ("conflicting-location-accepted-by-arrival", "Convergence", "MCProbeConflict.cfg", None,
     None, None),

    # Hierarchy (Hierarchy.tla)
    ("run-counts-carrier-grind-twice", "PhysicalWorkOnce", "MCHierarchy_Main.cfg", "Hierarchy.tla",
     "Attributed(ch, p) == RunWork(ch, p) - GrindWork(ch, p)", "Attributed(ch, p) == RunWork(ch, p)"),
    ("no-run-attribution", "ExpectedAnswer", "MCHierarchy_Main.cfg", "Hierarchy.tla",
     r"IN  grinds + Sum(cs, [pc \in cs |-> Attributed(Up(ch), pc[1])])", "IN  grinds"),
    ("runs-follow-parent-canonicity", "ExpectedAnswer", "MCHierarchy_ParentBad.cfg", "Hierarchy.tla",
     r'Run(ch, p) == {q \in weighed[ch] :',
     r'Run(ch, p) == {q \in {y \in weighed[ch] : AncOrSelf(y) \cap excluded[ch] = {}} :'),
    ("continuity-requires-canonical-anchor", "ExpectedAnswer", "MCHierarchy_Main.cfg", "Hierarchy.tla",
     r'        ELSE IF /\ new \in validated[Up(ChainOf(b))]',
     r'        ELSE IF /\ new \in validated[Up(ChainOf(b))] /\ new \in AncOrSelf(CanonicalTip(Up(ChainOf(b))))'),
    ("continuity-accepts-unexecuted-anchor", "AnchoredAtExecuted", "MCHierarchy_P1Gap.cfg", "Hierarchy.tla",
     r'        ELSE IF /\ new \in validated[Up(ChainOf(b))]', r'        ELSE IF /\ new \in weighed[Up(ChainOf(b))]'),
    ("continuity-allows-sideways", "AnchorsAdvance", "MCHierarchy_Main.cfg", "Hierarchy.tla",
     r"""        ELSE IF /\ new \in validated[Up(ChainOf(b))]
                /\ old \in AncOrSelf(new) \cup {None}""",
     r"""        ELSE IF /\ new \in validated[Up(ChainOf(b))]"""),
    ("continuity-before-transition", "ExpectedAnswer", "MCHierarchy_HeldInvalid.cfg", "Hierarchy.tla",
     '    IF ~Valid[b] THEN "invalid"\n'
     '    ELSE IF ch = "P" THEN "valid"\n'
     '    ELSE CASE Continuity(b) = "invalid" -> "invalid"\n'
     '           [] Continuity(b) = "held"    -> "held"\n'
     '           [] OTHER -> "valid"',
     '    IF ch = "P" THEN IF Valid[b] THEN "valid" ELSE "invalid"\n'
     '    ELSE CASE Continuity(b) = "invalid" -> "invalid"\n'
     '           [] Continuity(b) = "held"    -> "held"\n'
     '           [] OTHER -> IF Valid[b] THEN "valid" ELSE "invalid"'),
    ("child-genesis-may-anchor-empty", "AnchoredAtExecuted", "MCHierarchy_Main.cfg", "Hierarchy.tla",
     r"THEN IF Parent[b] # None /\ old = None THEN", "THEN IF old = None THEN"),
    ("nearest-carrier-skips-itself", "PhysicalWorkOnce", "MCHierarchy_Main.cfg", "Hierarchy.tla",
     r"""    IF Commits1(ch, q) THEN q
    ELSE IF Parent[q] = None THEN None""",
     r"""    IF Parent[q] = None THEN None
    ELSE IF Commits1(ch, Parent[q]) THEN Parent[q]"""),

    ("header-exclusion-waits-for-execution", "HeaderExcludedOnAdmission", "MCHierarchy_HeaderBad.cfg", "Hierarchy.tla",
     """    /\\ excluded' = IF o.b \\in HeaderBad""", """    /\\ excluded' = IF FALSE"""),
    ("header-violation-dropped-not-weighed", "NothingStuck", "MCHierarchy_HeaderBad.cfg", "Hierarchy.tla",
     "    /\\ weighed' = [weighed EXCEPT ![o.ch] = @ \\cup {o.b}]\n    /\\ excluded' = IF o.b \\in HeaderBad",
     "    /\\ weighed' = IF o.b \\in HeaderBad THEN weighed ELSE [weighed EXCEPT ![o.ch] = @ \\cup {o.b}]\n    /\\ excluded' = IF FALSE"),

    # Three levels (MCHierarchy3): caught only with a grandchild.
    ("runs-drop-attributed-work", "ExpectedAnswer", "MCHierarchy3_Main.cfg", "Hierarchy.tla",
     '    + IF ch = "P" THEN 0\n', '    + IF TRUE THEN 0\n'),
    ("run-credits-attributed-only-at-carrier", "PhysicalWorkOnce", "MCHierarchy3_Main.cfg", "Hierarchy.tla",
     "RunWork(ch, p) == Sum(Run(ch, p), [q \\in Run(ch, p) |-> Credited(ch, q)])",
     "RunWork(ch, p) == Sum(Run(ch, p), [q \\in Run(ch, p) |-> IF q = p THEN Credited(ch, q) ELSE GrindWork(ch, q)])"),
    ("grandchild-run-counts-carrier-grind-twice", "PhysicalWorkOnce", "MCHierarchy3_Main.cfg", "Hierarchy.tla",
     "Attributed(ch, p) == RunWork(ch, p) - GrindWork(ch, p)",
     'Attributed(ch, p) == RunWork(ch, p) - IF ch = "C" THEN 0 ELSE GrindWork(ch, p)'),
]


def run(name, expect, cfg, file, old, new):
    with tempfile.TemporaryDirectory() as work:
        work = pathlib.Path(work)
        for f in (ROOT / "specs").iterdir():
            if f.suffix in (".tla", ".cfg"):
                shutil.copy(f, work)
        if file is not None:
            path = work / file
            text = path.read_text()
            if text.count(old) != 1:
                return f"MUTANT {name}: replacement matched {text.count(old)} times", False
            path.write_text(text.replace(old, new))
        kind = "PROPERTY" if expect in TEMPORAL else "INVARIANT"
        base = (work / cfg).read_text().splitlines()
        body = [l for l in base if not re.match(r"^(INVARIANTS|PROPERTIES)", l)]
        module = cfg.split("_")[0] if "_" in cfg else "MC"
        mutant_cfg = f"{module}_Mutant.cfg"
        (work / mutant_cfg).write_text("\n".join(body + [f"{kind} {expect}"]) + "\n")
        out = subprocess.run([str(ROOT / "scripts" / "tlc.sh"), mutant_cfg, str(work)],
                             capture_output=True, text=True).stdout
        if "Parsing or semantic analysis failed" in out:
            return f"MUTANT {name}: does not parse", False
        if re.search(rf"(Invariant|Temporal property|Action property) {expect} .*violated"
                     rf"|{expect} is violated", out):
            return f"MUTANT {name}: killed by {expect}", True
        detail = "\n".join(l for l in out.splitlines()
                           if re.search("violated|Error|No error", l))
        return f"MUTANT {name}: SURVIVED (expected {expect})\n{detail}", False


def main():
    failures = 0
    for m in MUTANTS:
        line, ok = run(*m)
        print(line, flush=True)
        failures += not ok
    sys.exit(1 if failures else 0)


if __name__ == "__main__":
    main()
