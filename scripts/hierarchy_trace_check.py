#!/usr/bin/env python3
"""Check two- and three-level implementation traces against the hierarchy spec.

    scripts/hierarchy_trace_check.py <trace-dir-or-files...>
    scripts/hierarchy_trace_check.py --selftest <passing-trace.json>

Each trace-<seed>.json (Lattice's HierarchyTraceExportTests) becomes a TLA+
model of TraceHierarchy, checked by TLC. A trace passes when every event is a
step of the spec with the same accept/refuse, reason and header exclusion, and
after every event, on every chain, the tips, weights and continuity equal the
spec's. A two-level trace has no "G" chain; the grandchild then holds nothing.
"""
import copy
import json
import os
import pathlib
import re
import shutil
import subprocess
import sys
import tempfile

from trace_check import NONE, ROOT, fn, tla

INVARIANTS = ["CanonicalTipMatches", "ValidatedTipMatches", "WeightsMatch", "ContinuityMatches"]


def model(t):
    chains = t["chains"]
    p_blocks = [b["label"] for b in chains["P"]["blocks"]]
    c_blocks = [b["label"] for b in chains["C"]["blocks"]]
    g_blocks = [b["label"] for b in chains.get("G", {"blocks": []})["blocks"]]
    blocks = chains["P"]["blocks"] + chains["C"]["blocks"] + chains.get("G", {"blocks": []})["blocks"]
    grinds = sorted({g["label"] for g in t["grinds"]} | {e["grind"] for e in t["events"] if "grind" in e})
    events = []
    for e in t["events"]:
        a = e["after"]
        empty = {"canonicalTip": None, "validatedTip": None, "weights": {}, "continuity": {}}
        def side(ch, lower=True):
            s = a.get(ch, empty)
            return "[canonicalTip |-> {}, validatedTip |-> {}, weights |-> {}{}]".format(
                tla(s["canonicalTip"]), tla(s["validatedTip"]),
                fn({b: int(w) for b, w in s["weights"].items()}),
                f", continuity |-> {fn(s['continuity'])}" if lower else "")
        rec = {
            "kind": tla(e["kind"]),
            "ch": tla(e["ch"]),
            "block": tla(e["block"]),
            "grind": tla(e.get("grind", "")),
            "qty": tla(e.get("qty", 0)),
            "accepted": tla(e["accepted"]),
            "reason": tla(e.get("reason") or ""),
            "cause": tla(e.get("cause") or ""),
            "headerExcluded": tla(bool(e.get("headerExcluded"))),
            "after": "[P |-> {}, C |-> {}, G |-> {}]".format(side("P", lower=False), side("C"), side("G")),
        }
        events.append("[" + ", ".join(f"{k} |-> {v}" for k, v in rec.items()) + "]")
    obs = ", ".join(f"[ch |-> {tla(g['ch'])}, g |-> {tla(g['label'])}, b |-> {tla(g['block'])}, q |-> {g['qty']}]"
                    for g in t["grinds"])
    commits = ", ".join(f"<<{tla(p)}, {tla(c)}>>" for p, c in t["commits"])
    sep = ",\n    "
    return f"""---- MODULE MCTrace ----
EXTENDS TraceHierarchy, TLC
TPBlocks == {{{", ".join(tla(x) for x in p_blocks)}}}
TCBlocks == {{{", ".join(tla(x) for x in c_blocks)}}}
TGBlocks == {{{", ".join(tla(x) for x in g_blocks)}}}
TParent == {fn({b["label"]: b["parent"] for b in blocks})}
TPrevState == {fn({b["label"]: b.get("prevStateBlock", b["parent"]) for b in blocks})}
TCidRank == {fn({b["label"]: b["cidRank"] for b in blocks})}
TGrinds == {{{", ".join(tla(g) for g in grinds)}}}
TObs == {{{obs}}}
TCommits == {{{commits}}}
TAnchor == {fn(t["anchor"])}
TValid == {fn({b["label"]: b["valid"] for b in blocks})}
THeaderBad == {{{", ".join(tla(b["label"]) for b in blocks if b.get("headerBad"))}}}
TAvailable == {{{", ".join(tla(b["label"]) for b in blocks if not b.get("withheld"))}}}
TTips == [ch \\in {{"P", "C", "G"}} |-> [canonical |-> "{NONE}", validated |-> "{NONE}"]]
TChildWork == [x \\in TCBlocks |-> 0]
TTrace == <<
    {sep.join(events)}
>>
====
"""


CFG = f"""INIT TraceInit
NEXT TraceNext
CONSTANTS
    None = "{NONE}"
    PBlocks <- TPBlocks
    CBlocks <- TCBlocks
    GBlocks <- TGBlocks
    Parent <- TParent
    PrevState <- TPrevState
    CidRank <- TCidRank
    Grinds <- TGrinds
    Obs <- TObs
    Commits <- TCommits
    Anchor <- TAnchor
    Valid <- TValid
    HeaderBad <- THeaderBad
    Available <- TAvailable
    ExpectedTips <- TTips
    ExpectedChildWork <- TChildWork
    Trace <- TTrace
"""


def check(path):
    t = json.loads(path.read_text())
    with tempfile.TemporaryDirectory() as work:
        work = pathlib.Path(work)
        for f in ("Hierarchy.tla", "TraceHierarchy.tla"):
            shutil.copy(ROOT / "specs" / f, work)
        (work / "MCTrace.tla").write_text(model(t))
        (work / "MCTrace_Run.cfg").write_text(CFG + "INVARIANTS " + " ".join(INVARIANTS) + "\n")
        out = subprocess.run([str(ROOT / "scripts" / "tlc.sh"), "MCTrace_Run.cfg", str(work)],
                             capture_output=True, text=True,
                             env={**os.environ, "TLC_CHECK_DEADLOCK": "1"}).stdout
    n = len(t["events"])
    if "No error has been found" in out:
        return True, f"{path.name}: pass ({n} events)"
    steps = re.findall(r"^/\\ i = (\d+)", out, re.M)
    at = int(steps[-1]) if steps else None
    if "Deadlock reached" in out and at is not None:
        e = t["events"][at - 1]
        why = f"event {at} is not a spec step with accepted={e['accepted']}: {json.dumps({k: e[k] for k in e if k != 'after'})}"
    elif (m := re.search(r"Invariant (\w+Matches) is violated", out)) and at is not None:
        e = t["events"][at - 2]
        why = f"{m.group(1)} after event {at - 1}: {json.dumps(e)}"
    else:
        why = "\n".join(l for l in out.splitlines() if re.search("Error|violated|Assumption", l)).strip() or out[-2000:] or "no TLC output"
    return False, f"{path.name}: FAIL ({n} events)\n  {why}"


def selftest(path):
    """Corrupt a passing trace; each corruption must be caught.  Six apply to
    every trace; three more apply to three-level traces."""
    base = json.loads(path.read_text())
    ok, line = check(path)
    if not ok:
        return False, f"selftest: base trace must pass\n{line}"
    def child_weight(t):
        e = next(e for e in t["events"] if e["after"]["C"]["weights"])
        b = next(iter(e["after"]["C"]["weights"]))
        e["after"]["C"]["weights"][b] = str(int(e["after"]["C"]["weights"][b]) + 1)
        return "WeightsMatch"
    def continuity(t):
        e = next(e for e in t["events"] if "held" in e["after"]["C"]["continuity"].values())
        b = next(k for k, v in e["after"]["C"]["continuity"].items() if v == "held")
        e["after"]["C"]["continuity"][b] = "proven"
        return "ContinuityMatches"
    def child_tip(t):
        e = next(e for e in t["events"] if e["after"]["C"]["validatedTip"] is not None)
        e["after"]["C"]["validatedTip"] = None
        return "ValidatedTipMatches"
    def held_as_accepted(t):
        e = next(e for e in t["events"] if e.get("reason") == "continuity")
        e["accepted"], e["reason"] = True, None
        return "not a spec step"
    def wrong_cause(t):
        e = next(e for e in t["events"] if e["kind"] == "exclude" and e.get("cause"))
        e["cause"] = "continuity" if e["cause"] == "transition" else "transition"
        return "not a spec step"
    def elsewhere_unreported(t):
        e = next(e for e in t["events"] if e.get("reason") == "grindElsewhere")
        e["reason"] = None
        return "not a spec step"
    def grandchild_weight(t):
        e = next((e for e in t["events"] if e["after"].get("G", {}).get("weights")), None)
        if e is None:
            return None
        b = next(iter(e["after"]["G"]["weights"]))
        e["after"]["G"]["weights"][b] = str(int(e["after"]["G"]["weights"][b]) + 1)
        return "WeightsMatch"
    def grandchild_continuity(t):
        e = next((e for e in t["events"] if "held" in e["after"].get("G", {}).get("continuity", {}).values()), None)
        if e is None:
            return None
        b = next(k for k, v in e["after"]["G"]["continuity"].items() if v == "held")
        e["after"]["G"]["continuity"][b] = "proven"
        return "ContinuityMatches"
    def header_exclusion_unreported(t):
        e = next((e for e in t["events"] if e.get("headerExcluded")), None)
        if e is None:
            return None
        e["headerExcluded"] = False
        return "not a spec step"
    results, ok = [], True
    with tempfile.TemporaryDirectory() as d:
        for corrupt in (child_weight, continuity, child_tip, held_as_accepted,
                        wrong_cause, elsewhere_unreported,
                        grandchild_weight, grandchild_continuity, header_exclusion_unreported):
            t = copy.deepcopy(base)
            expect = corrupt(t)
            if expect is None:
                continue
            q = pathlib.Path(d) / f"trace-{corrupt.__name__}.json"
            q.write_text(json.dumps(t))
            passed, line = check(q)
            caught = not passed and expect in line
            ok &= caught
            results.append(f"selftest {corrupt.__name__}: {'caught' if caught else 'MISSED'}"
                           + ("" if caught else f"\n{line}"))
    return ok, "\n".join(results + [f"selftest {'pass' if ok else 'FAIL'}"])


def main():
    if sys.argv[1:2] == ["--selftest"]:
        ok, line = selftest(pathlib.Path(sys.argv[2]))
        print(line)
        sys.exit(0 if ok else 1)
    paths = []
    for a in sys.argv[1:]:
        p = pathlib.Path(a)
        paths += sorted(p.glob("trace-*.json"), key=lambda q: int(re.sub(r"\D", "", q.stem) or 0)) if p.is_dir() else [p]
    if not paths:
        sys.exit("no traces given")
    failures = 0
    for p in paths:
        ok, line = check(p)
        print(line, flush=True)
        failures += not ok
    print(f"{len(paths) - failures}/{len(paths)} traces pass")
    sys.exit(1 if failures else 0)


if __name__ == "__main__":
    main()
