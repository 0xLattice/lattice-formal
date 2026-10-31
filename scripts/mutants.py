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
TEMPORAL = {"WorkMonotone", "VerdictsPermanent", "CatchesUp", "NothingPruned",
            "RevisionAdvances", "FailureLeavesGraphUnchanged", "StagedBecomesVisible",
            "Converges", "PeerConverges"}

# (name, property that must go red, config, file, old text, new text[, witness])
DCG = "DerivedChildGrinds.tla"
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

    # Cross-chain fork choice (HierarchyProps.tla), each checked alone.
    ("carrier-runs-count-once-validated", "WeightIgnoresVerdicts", "MCHierarchy_Main.cfg", "Hierarchy.tla",
     r"CarriersOf(ch, q) == {u \in weighed[Up(ch)] :", r"CarriersOf(ch, q) == {u \in validated[Up(ch)] :"),
    ("child-credits-only-selectable-carriers", "ParentCanonicityIrrelevant", "MCHierarchyFork_Main.cfg", "Hierarchy.tla",
     r"CarriersOf(ch, q) == {u \in weighed[Up(ch)] : <<u, q>> \in Commits}",
     r"CarriersOf(ch, q) == {u \in weighed[Up(ch)] : <<u, q>> \in Commits /\ AncOrSelf(u) \cap excluded[Up(ch)] = {}}"),
    ("child-validity-follows-parent-validated-chain", "ParentCanonicityIrrelevant", "MCHierarchyFork_Main.cfg", "Hierarchy.tla",
     r'        ELSE IF /\ new \in validated[Up(ChainOf(b))]',
     r'        ELSE IF /\ new \in validated[Up(ChainOf(b))] /\ new \in AncOrSelf(ValidatedTip(Up(ChainOf(b))))'),
    ("grandchild-credits-every-committing-carrier", "NoDoubleBacking", "MCHierarchyFork_Main.cfg", "Hierarchy.tla",
     r"CarriersOf(ch, q) == {u \in weighed[Up(ch)] : <<u, q>> \in Commits}",
     r'CarriersOf(ch, q) == {u \in weighed[Up(ch)] : \E l \in ChainBlocks(ch) : <<u, l>> \in Commits /\ (ch = "G" \/ l = q)}'),
    ("carrier-credited-child-work-it-commits", "ChildrenCannotMoveParent", "MCHierarchyFork_Main.cfg", "Hierarchy.tla",
     r"    IN  grinds + Sum(cs, [pc \in cs |-> Attributed(Up(ch), pc[1])])",
     r"    IN  grinds + Sum(cs, [pc \in cs |-> Attributed(Up(ch), pc[1])])"
     r' + IF ch = "P" THEN Sum({g \in Grinds : \E x \in Subtree(ch, b) : <<x, loc["C"][g]>> \in Commits}, qty["C"]) ELSE 0'),
    ("held-anchor-excludes", "ExcludedHasCause", "MCHierarchy_Main.cfg", "Hierarchy.tla",
     '           [] Continuity(b) = "held"    -> "held"\n',
     '           [] Continuity(b) = "held"    -> "invalid"\n'),
    ("fork-choice-by-own-work-not-subtree", "HeaviestAtEveryFork", "MCHierarchy_Main.cfg", "Hierarchy.tla",
     r"    LET W == [x \in ChainBlocks(ch) |-> TrueCumWork(ch, x)]",
     r"    LET W == [x \in ChainBlocks(ch) |-> Credited(ch, x)]"),
    ("exclusion-prunes-block", "NothingPruned", "MCHierarchy_HeldInvalid.cfg", "Hierarchy.tla",
     "    /\\ excluded' = [excluded EXCEPT ![ch] = @ \\cup {b}]\n    /\\ UNCHANGED <<delivered, loc, qty, weighed, validated>>",
     "    /\\ excluded' = [excluded EXCEPT ![ch] = @ \\cup {b}]\n"
     "    /\\ weighed' = [weighed EXCEPT ![ch] = @ \\ {b}]\n"
     "    /\\ UNCHANGED <<delivered, loc, qty, validated>>"),

    # Three levels (MCHierarchy3): caught only with a grandchild.
    ("runs-drop-attributed-work", "ExpectedAnswer", "MCHierarchy3_Main.cfg", "Hierarchy.tla",
     '    + IF ch = "P" THEN 0\n', '    + IF TRUE THEN 0\n'),
    ("run-credits-attributed-only-at-carrier", "PhysicalWorkOnce", "MCHierarchy3_Main.cfg", "Hierarchy.tla",
     "RunWork(ch, p) == Sum(Run(ch, p), [q \\in Run(ch, p) |-> Credited(ch, q)])",
     "RunWork(ch, p) == Sum(Run(ch, p), [q \\in Run(ch, p) |-> IF q = p THEN Credited(ch, q) ELSE GrindWork(ch, q)])"),
    ("grandchild-run-counts-carrier-grind-twice", "PhysicalWorkOnce", "MCHierarchy3_Main.cfg", "Hierarchy.tla",
     "Attributed(ch, p) == RunWork(ch, p) - GrindWork(ch, p)",
     'Attributed(ch, p) == RunWork(ch, p) - IF ch = "C" THEN 0 ELSE GrindWork(ch, p)'),

    # Swaps under forks and reorgs (SwapReorg.tla)
    ("withdrawal-reads-any-known-receipt", "WithdrawalBackedOnAnchorBranch", "MCSwapReorg_Main.cfg", "SwapReorg.tla",
     r"    /\ s \in ReceiptsAt(a)", r"    /\ s \in UNION {pRc[q] : q \in pMade}"),
    ("withdrawal-reads-parent-canonical-tip", "WithdrawalBackedOnAnchorBranch", "MCSwapReorg_Main.cfg", "SwapReorg.tla",
     r"    /\ s \in ReceiptsAt(a)", r"    /\ s \in ReceiptsAt(tipP)"),
    ("anchor-weighed-not-executed", "WithdrawalBackedOnAnchorBranch", "MCSwapReorg_Main.cfg", "SwapReorg.tla",
     r"    /\ a \in Frontier", r"    /\ a \in pMade"),
    ("anchor-executed-off-frontier", "WithdrawalBackedOnAnchorBranch", "MCSwapReorg_Main.cfg", "SwapReorg.tla",
     r"    /\ a \in Frontier", r"    /\ a \in pExec"),
    ("anchor-moves-sideways", "DemanderSafeIfAnchorCanonical", "MCSwapReorg_Main.cfg", "SwapReorg.tla",
     r"    /\ cAnc[c] \in PLine(a)", r"    /\ cAnc[c] \in pMade"),
    ("replay-drops-spent-marker", "NoDoubleRelease", "MCSwapReorg_Replay.cfg", "SwapReorg.tla",
     '[s \\in Swaps |-> IF s \\in wd THEN "spent"', '[s \\in Swaps |-> IF s \\in wd THEN "none"'),
    ("withdrawal-accepts-spent-marker", "NoDoubleRelease", "MCSwapReorg_Main.cfg", "SwapReorg.tla",
     '    /\\ StateAt(c)[s] = "live"\n    /\\ s \\in ReceiptsAt(a)', '    /\\ StateAt(c)[s] # "none"\n    /\\ s \\in ReceiptsAt(a)'),
    ("withdrawal-skips-deposit-proof", "ReleaseHasDeposit", "MCSwapReorg_Main.cfg", "SwapReorg.tla",
     '    /\\ StateAt(c)[s] = "live"\n    /\\ s \\in ReceiptsAt(a)', '    /\\ StateAt(c)[s] # "spent"\n    /\\ s \\in ReceiptsAt(a)'),
    ("receipt-only-in-anchor-block", "WithdrawerCanRedeem", "MCSwapReorg_Main.cfg", "SwapReorg.tla",
     r"    /\ s \in ReceiptsAt(a)", r"    /\ s \in pRc[a]"),

    # Import, durability and recovery (Recovery.tla)
    ("apply-before-durable", "VisibleImpliesDurable", "MCRecovery_Main.cfg", "Recovery.tla",
     "    /\\ up /\\ cur.p = \"durable\"\n    /\\ LET H == Apply(mem, cur.x)",
     "    /\\ up /\\ cur.p \\in {\"checked\", \"durable\"}\n    /\\ LET H == Apply(mem, cur.x)"),
    ("live-import-rebuilds-batch", "RecoveredEqualsLive", "MCRecovery_Main.cfg", "Recovery.tla",
     "    /\\ LET H == Apply(mem, cur.x)", "    /\\ LET H == Apply(mem, Rebuild[cur.x])"),
    ("strengthening-double-counted", "ReplayIdempotent", "MCRecovery_Main.cfg", "Recovery.tla",
     "            [G EXCEPT !.loc[x.g] = x.b,\n                      !.qty[x.g] = IF x.q > @ THEN x.q ELSE @]",
     "            [G EXCEPT !.loc[x.g] = x.b,\n                      !.qty[x.g] = IF G.loc[x.g] = x.b THEN @ + x.q ELSE x.q]"),
    ("restore-uses-persisted-tip", "RecoveredEqualsLive", "MCRecovery_Main.cfg", "Recovery.tla",
     "    /\\ tip' = CanonicalTip(mem)\n", "    /\\ tip' = ptip\n"),
    ("revision-reset-on-recovery", "RevisionMonotone", "MCRecovery_Main.cfg", "Recovery.tla",
     "    /\\ rev' = Max(rev, floor)\n", "    /\\ rev' = 0\n"),
    ("floor-is-pre-stage-revision", "RevisionMonotone", "MCRecovery_Main.cfg", "Recovery.tla",
     "    /\\ floor' = IF FloorPersisted THEN rev + 1 ELSE floor\n", "    /\\ floor' = IF FloorPersisted THEN rev ELSE floor\n"),
    ("revision-only-for-new-blocks", "RevisionAdvances", "MCRecovery_Main.cfg", "Recovery.tla",
     "           /\\ rev' = IF Mutates(mem, H) THEN rev + 1 ELSE rev\n           /\\ tip' = CanonicalTip(H)",
     "           /\\ rev' = IF H.held # mem.held THEN rev + 1 ELSE rev\n           /\\ tip' = CanonicalTip(H)"),
    ("store-accepts-conflicting-metadata", "ConflictRejected", "MCRecovery_Main.cfg", "Recovery.tla",
     "    /\\ StoreAccepts(cur.x)\n", ""),
    ("failed-write-keeps-applied-batch", "FailureLeavesGraphUnchanged", "MCRecovery_Main.cfg", "Recovery.tla",
     "    /\\ UNCHANGED <<log, floor, ptip, mem, tip, rev, up, rec, crashes, seen, lost>>",
     "    /\\ mem' = Apply(mem, cur.x)\n    /\\ UNCHANGED <<log, floor, ptip, tip, rev, up, rec, crashes, seen, lost>>"),
    ("exclusion-staged-never-applied-live", "StagedBecomesVisible", "MCRecovery_Main.cfg", "Recovery.tla",
     "    /\\ up /\\ cur.p = \"durable\"\n", "    /\\ up /\\ cur.p = \"durable\" /\\ cur.x.k # \"excl\"\n"),

    # Derived child grinds (DerivedChildGrinds.tla): lattice-node bugs, earlier
    # and possible. A trailing True marks a witness config: the correct model
    # violates the property there, so the mutant is killed when it holds.
    ("no-arrival-trigger", "Converges", "DerivedChildGrinds_Main.cfg", DCG,
     "ArrivalJobs(st, arr) == ArrivalKeys(st, arr)", "ArrivalJobs(st, arr) == {}"),
    ("dedup-in-flight-derivation", "Converges", "DerivedChildGrinds_Grow.cfg", DCG,
     "Issued(js, S) == S",
     r"Issued(js, S) == {k \in S : ~\E j \in JobKeys : j[1] = k[1] /\ js[j] > 0}"),
    ("apply-only-while-counted", "Converges", "DerivedChildGrinds_Main.cfg", DCG,
     "Applies(dv, c) == TRUE", "Applies(dv, c) == dv[c] > 0"),
    ("evict-ignores-deriving", "Converges", "DerivedChildGrinds_Main.cfg", DCG,
     r"Holds(dv, pq, y) == dv[y] > 0 \/ pq[y] # {}", r"Holds(dv, pq, y) == pq[y] # {}"),
    ("holds-ignores-peer-proofs", "PeerConverges", "DerivedChildGrinds_PeerPush.cfg", DCG,
     r"Holds(dv, pq, y) == dv[y] > 0 \/ pq[y] # {}", r"Holds(dv, pq, y) == dv[y] > 0"),
    ("no-boot-pass", "Converges", "DerivedChildGrinds_Main.cfg", DCG,
     r'BootKeys(st) == ArrivalKeys(st, {c \in Children : st[c] = "tree"})', "BootKeys(st) == {}"),
    ("rehost-no-boot", "Converges", "DerivedChildGrinds_Main.cfg", DCG,
     "LET S == Issued(jobs, BootKeys(status))", "LET S == {}"),
    ("underflow", "TypeOK", "DerivedChildGrinds_Main.cfg", DCG,
     "dv1 == [deriving EXCEPT ![c] = IF @ > 0 THEN @ - 1 ELSE 0]", "dv1 == [deriving EXCEPT ![c] = @ - 1]"),
    ("no-proofless", "Converges", "DerivedChildGrinds_Main.cfg", DCG,
     r'/\ p # "none" \/ Wanted(c)', r'/\ p # "none"'),
    ("no-target-check", "Safety", "DerivedChildGrinds_Main.cfg", DCG,
     r"Proofs(b) == {g \in Meets : CarrierOf[g] = b}", r"Proofs(b) == {g \in Grinds : CarrierOf[g] = b}"),
    ("author-stops-on-first-credit", "Converges", "DerivedChildGrinds_Main.cfg", DCG,
     r"/\ (AuthorStopsOnCredit => c \notin seen)", r"/\ c \notin seen"),
    ("no-retrigger-on-grown-grinds", "Converges", "DerivedChildGrinds_Grow.cfg", DCG,
     "          /\\ Retrigger(b, cg)\n    /\\ UNCHANGED <<weighed,",
     "          /\\ UNCHANGED <<jobs, deriving>>\n    /\\ UNCHANGED <<weighed,"),
    ("pending-not-lost-on-restart", "Converges", "DerivedChildGrinds_StopOnCredit.cfg", DCG,
     "    /\\ restarts' = restarts + 1\n    /\\ Lose(Durable(status))",
     "    /\\ restarts' = restarts + 1\n    /\\ Lose(Durable(status) \\cup {c \\in Children : status[c] = \"pending\"})", True),
    ("promote-on-empty-answer", "CreditHeld", "DerivedChildGrinds_Grow.cfg", DCG,
     'IF P # {} /\\ st[c] = "awaiting"', 'IF st[c] = "awaiting"'),
    ("evict-non-leaf", "Converges", "DerivedChildGrinds_Parent.cfg", DCG,
     '         /\\ ~\\E x \\in Children : Parent[x] = v /\\ status[x] = "pending"\n', ""),
    ("wanted-no-parent-clause", "Converges", "DerivedChildGrinds_Parent.cfg", DCG,
     'Wanted(c) == Committers(c) # {} \\/ \\E x \\in Children : Parent[x] = c /\\ status[x] \\in {"awaiting", "pending"}',
     "Wanted(c) == Committers(c) # {}"),
    # Removes the MaxEvicts bound: documents assumption (A3).
    ("unbounded-evict", "Converges", "DerivedChildGrinds_Main.cfg", DCG,
     "    /\\ evicts' = evicts + 1\n", "    /\\ evicts' = evicts\n"),
    ("weigh-no-retrigger", "Converges", "DerivedChildGrinds_Main.cfg", DCG,
     "            /\\ Retrigger(b, cg)\n    /\\ UNCHANGED <<status,",
     "            /\\ UNCHANGED <<jobs, deriving>>\n    /\\ UNCHANGED <<status,"),
    ("derive-skips-tree", "Converges", "DerivedChildGrinds_Main.cfg", DCG,
     r"b \in {x \in B : Known(st, Commit[x])", r'b \in {x \in B : st[Commit[x]] \in {"awaiting", "pending"}'),
    ("settle-ignores-parent", "CreditHeld", "DerivedChildGrinds_Main.cfg", DCG,
     'IF st[c] = "pending" /\\ (Parent[c] = "genesis" \\/ st[Parent[c]] = "tree")', 'IF st[c] = "pending"'),
    ("peer-proof-unchecked", "Safety", "DerivedChildGrinds_PeerPush.cfg", DCG,
     r"IF Valid(c, p) /\ Known(status, c)", r"IF Known(status, c)"),
    ("admit-never-evicts", "Converges", "DerivedChildGrinds_Main.cfg", DCG,
     r"    ELSE {[x \in Children |-> IF x = c", r"    ELSE {} \cap {[x \in Children |-> IF x = c"),
]


def run(name, expect, cfg, file, old, new, witness=False):
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
        if witness:
            if "No error has been found" in out:
                return f"MUTANT {name}: killed ({expect} now holds on witness {cfg})", True
            return f"MUTANT {name}: SURVIVED (witness {cfg} still violates {expect})", False
        # A liveness violation names no property; the property is checked
        # alone, so it is the one violated.
        if re.search(rf"(Invariant|Temporal property|Action property) {expect} .*violated"
                     rf"|{expect} is violated|Temporal properties were violated", out):
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
