#!/usr/bin/env python3
"""Check fork-choice traces exported by Lattice against specs/ForkChoice.tla.

    scripts/trace_check.py [--skip <Invariant>]... <trace-dir-or-files...>
    scripts/trace_check.py --selftest <passing-trace.json>

Each trace-<seed>.json (Lattice's ForkChoiceTraceExportTests) becomes a TLA+
model of TraceForkChoice, checked by TLC. A trace passes when every event is a
step of the spec with the same accept/refuse, and every recorded tip and weight
equals the spec's.
"""
import json
import os
import pathlib
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
NONE = "none"


def tla(v):
    if v is None:
        return f'"{NONE}"'
    if isinstance(v, bool):
        return "TRUE" if v else "FALSE"
    if isinstance(v, int):
        return str(v)
    if isinstance(v, str):
        return json.dumps(v)
    raise TypeError(v)


def fn(d):
    """A TLA+ function literal over string keys."""
    if not d:
        return "[x \\in {} |-> 0]"
    return "(" + " @@ ".join(f"{tla(k)} :> {tla(v)}" for k, v in d.items()) + ")"


def model(t):
    blocks = t["blocks"]
    ids = [b["id"] for b in blocks]
    grinds = sorted({e["grind"] for e in t["events"] if "grind" in e})
    obs = sorted({(e["grind"], e["block"], e["qty"]) for e in t["events"]
                  if e["kind"] in ("admit", "observe")})
    events = []
    for e in t["events"]:
        after = e["after"]
        rec = {
            "kind": tla(e["kind"]),
            "block": tla(e["block"]),
            "grind": tla(e.get("grind", "")),
            "qty": tla(e.get("qty", 0)),
            "accepted": tla(e["accepted"]),
            "after": "[canonicalTip |-> {}, validatedTip |-> {}, weights |-> {}, cumulative |-> {}]".format(
                tla(after["canonicalTip"]), tla(after["validatedTip"]),
                fn({b: int(w) for b, w in after["weights"].items()}),
                fn({b: int(w) for b, w in after["cumulative"].items()})),
        }
        events.append("[" + ", ".join(f"{k} |-> {v}" for k, v in rec.items()) + "]")
    sep = ",\n    "
    return f"""---- MODULE MCTrace ----
EXTENDS TraceForkChoice, TLC
TBlocks == {{{", ".join(tla(x) for x in ids)}}}
TParent == {fn({b["id"]: b["parent"] for b in blocks})}
TCidRank == {fn({b["id"]: b["cidRank"] for b in blocks})}
TGrinds == {{{", ".join(tla(g) for g in grinds)}}}
TObs == {{{", ".join(f"[g |-> {tla(g)}, b |-> {tla(b)}, q |-> {q}]" for g, b, q in obs)}}}
TValid == {fn(t["valid"])}
TTrace == <<
    {sep.join(events)}
>>
====
"""


CFG = f"""INIT TraceInit
NEXT TraceNext
CONSTANTS
    Nodes = {{n}}
    None = "{NONE}"
    Blocks <- TBlocks
    Parent <- TParent
    CidRank <- TCidRank
    Grinds <- TGrinds
    Obs <- TObs
    Valid <- TValid
    Available <- TBlocks
    ExpectedCanonical = "{NONE}"
    ExpectedValidated = "{NONE}"
    Trace <- TTrace
"""
INVARIANTS = ["CanonicalTipMatches", "WeightsMatch", "CumulativeMatches", "ValidatedTipMatches"]


def check(path, skip=()):
    t = json.loads(path.read_text())
    with tempfile.TemporaryDirectory() as work:
        work = pathlib.Path(work)
        for f in ("ForkChoice.tla", "TraceForkChoice.tla"):
            shutil.copy(ROOT / "specs" / f, work)
        (work / "MCTrace.tla").write_text(model(t))
        invs = [v for v in INVARIANTS if v not in skip]
        (work / "MCTrace_Run.cfg").write_text(CFG + "INVARIANTS " + " ".join(invs) + "\n")
        out = subprocess.run([str(ROOT / "scripts" / "tlc.sh"), "MCTrace_Run.cfg", str(work)],
                             capture_output=True, text=True,
                             env={**os.environ, "TLC_CHECK_DEADLOCK": "1"}).stdout
    n = len(t["events"])
    if "No error has been found" in out:
        return True, f"{path.name}: pass ({n} events)"
    # The failing event is the last i in TLC's error trace.
    steps = re.findall(r"^/\\ i = (\d+)", out, re.M)
    at = int(steps[-1]) if steps else None
    if "Deadlock reached" in out and at is not None:
        e = t["events"][at - 1]
        why = f"event {at} is not a spec step with accepted={e['accepted']}: {json.dumps({k: e[k] for k in e if k != 'after'})}"
    elif (m := re.search(r"Invariant (\w+Match(?:es)?) is violated", out)) and at is not None:
        e = t["events"][at - 2]
        spec = re.findall(r"^/\\ (?:weighed|validated|excluded) = .*$", out, re.M)[-3:]
        why = (f"{m.group(1)} after event {at - 1}: {json.dumps(e)}\n  spec state: "
               + " ".join(spec))
    else:
        why = "\n".join(l for l in out.splitlines() if re.search("Error|violated", l)).strip() or out[-2000:] or "no TLC output"
    return False, f"{path.name}: FAIL ({n} events)\n  {why}"


def selftest(path):
    """Corrupt a passing trace three ways; each must be caught."""
    import copy
    base = json.loads(path.read_text())
    ok, line = check(path)
    if not ok:
        return False, f"selftest: base trace must pass\n{line}"
    cases = []
    def weight(t):
        e = next(e for e in t["events"] if e["after"]["weights"])
        b = next(iter(e["after"]["weights"]))
        e["after"]["weights"][b] = str(int(e["after"]["weights"][b]) + 1)
        return "WeightsMatch"
    def cumulative(t):
        e = next(e for e in t["events"] if e["after"]["cumulative"])
        b = next(iter(e["after"]["cumulative"]))
        e["after"]["cumulative"][b] = str(int(e["after"]["cumulative"][b]) + 1)
        return "CumulativeMatches"
    def accepted(t):
        e = next(e for e in t["events"] if e["kind"] in ("validate", "exclude"))
        e["accepted"] = not e["accepted"]
        return "not a spec step"
    results = []
    with tempfile.TemporaryDirectory() as d:
        for corrupt in (weight, cumulative, accepted):
            t = copy.deepcopy(base)
            expect = corrupt(t)
            q = pathlib.Path(d) / f"trace-{corrupt.__name__}.json"
            q.write_text(json.dumps(t))
            ok, line = check(q)
            caught = not ok and expect in line
            results.append(caught)
            print(f"selftest {corrupt.__name__}: {'caught' if caught else 'MISSED'}", flush=True)
    return all(results), "selftest " + ("pass" if all(results) else "FAIL")


def main():
    if sys.argv[1:2] == ["--selftest"]:
        ok, line = selftest(pathlib.Path(sys.argv[2]))
        print(line)
        sys.exit(0 if ok else 1)
    args, skip, paths = sys.argv[1:], [], []
    while args[:1] == ["--skip"]:
        skip.append(args[1])
        args = args[2:]
    for a in args:
        p = pathlib.Path(a)
        paths += sorted(p.glob("trace-*.json"), key=lambda q: int(re.sub(r"\D", "", q.stem) or 0)) if p.is_dir() else [p]
    if not paths:
        sys.exit("no traces given")
    failures = 0
    for p in paths:
        ok, line = check(p, skip)
        print(line, flush=True)
        failures += not ok
    note = f" (skipping {', '.join(skip)})" if skip else ""
    print(f"{len(paths) - failures}/{len(paths)} traces pass{note}")
    sys.exit(1 if failures else 0)


if __name__ == "__main__":
    main()
