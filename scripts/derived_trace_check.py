#!/usr/bin/env python3
"""Check lattice-node derived-child-grind traces against the spec.

    scripts/derived_trace_check.py <trace-dir-or-files...>
    scripts/derived_trace_check.py --selftest <passing-trace.json>

Each trace-<name>.json (lattice-node's DerivedChildGrindTests, written under
DERIVED_TRACE_DIR) becomes a TLA+ model of TraceDerivedChildGrinds, checked
by TLC with the trace's own fixture in place of the spec's. A trace passes
when every event is the named step of DerivedChildGrinds (a refused gossip:
one the spec cannot take) and, after every host step, each child's status,
credits, derivation count and queued peer proofs and every derivation in
flight equal the spec's.
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

from trace_check import ROOT, fn, tla

INVARIANTS = ["HostedMatches", "StatusMatches", "CreditedMatches", "DerivingMatches",
              "PeerQMatches", "JobsMatch"]
BOUND = 1000  # restarts, unhosts, evictions, strikes and queued proofs: never binding here


def tset(xs):
    return "{" + ", ".join(tla(x) for x in sorted(xs)) + "}"


def tfn(d, value):
    """A function literal over string keys, with values rendered by `value`."""
    if not d:
        return "[x \\in {} |-> 0]"
    return "(" + " @@ ".join(f"{tla(k)} :> {value(v)}" for k, v in sorted(d.items())) + ")"


def after(a):
    if a is None:
        a = {"hosted": True, "status": {}, "credited": {}, "deriving": {}, "peerQ": {}, "jobs": []}
    jobs = ", ".join(f"<<<<{tla(j['carrier'])}, {tla(j['child'])}, {tset(j['grinds'])}>>, {j['count']}>>"
                     for j in a["jobs"])
    return "[hosted |-> {}, status |-> {}, credited |-> {}, deriving |-> {}, peerQ |-> {}, jobs |-> {{{}}}]".format(
        tla(a["hosted"]), tfn(a["status"], tla), tfn(a["credited"], tset),
        tfn(a["deriving"], tla), tfn(a["peerQ"], tset), jobs)


def event(e):
    rec = {
        "kind": tla(e["kind"]),
        "carrier": tla(e.get("carrier", "")),
        "child": tla(e.get("child", "")),
        "proof": tla(e.get("proof", "")),
        "grinds": tset(e.get("grinds", [])),
        "grind": tla(e.get("grind", "")),
        "victim": tla(e.get("victim", "none")),
        "x": tla(bool(e.get("x", False))),
        "accepted": tla(bool(e.get("accepted", False))),
        "checked": tla("after" in e),
        "after": after(e.get("after")),
    }
    return "[" + ", ".join(f"{k} |-> {v}" for k, v in rec.items()) + "]"


def model(t):
    children, carriers, grinds = t["children"], t["carriers"], t["grinds"]
    init = t["init"]
    # A level not hosted when tracing began holds nothing.
    status = {c: init["status"].get(c, "unknown") for c in children}
    credited = {c: init["credited"].get(c, []) for c in children}
    sep = ",\n    "
    return f"""---- MODULE MCTrace ----
EXTENDS TraceDerivedChildGrinds, TLC
TCarriers == {tset(carriers)}
TChildren == {tset(children)}
TParent == {tfn(children, tla)}
TCommit == {tfn(carriers, tla)}
TGrinds == {tset(grinds)}
TCarrierOf == {tfn(grinds, tla)}
TMeets == {tset(t["meets"])}
TPeerProofs == {tset(set(grinds) | {"bogus"})}
TReal == {tfn(t["real"], tla)}
TTInit == [hosted |-> {tla(init["hosted"])}, weighed |-> {tset(init["weighed"])},
           cgr |-> {tfn(init["cgr"], tset)},
           status |-> {tfn(status, tla)}, credited |-> {tfn(credited, tset)}]
TTrace == <<
    {sep.join(event(e) for e in t["events"])}
>>
====
"""


def cfg(t):
    return f"""INIT TraceInit
NEXT TraceNext
CONSTANTS
    Cap = {t["cap"]}
    Grow = {tla(t["grow"])}
    PeerPush = FALSE
    AuthorStopsOnCredit = FALSE
    DeferSettle = FALSE
    ParentsFetched = FALSE
    IndexFetched = FALSE
    MaxRestarts = {BOUND}
    MaxUnhosts = {BOUND}
    MaxEvicts = {BOUND}
    MaxStrikes = {BOUND}
    QBudget = {BOUND}
    Carriers <- TCarriers
    Children <- TChildren
    Parent <- TParent
    Commit <- TCommit
    Grinds <- TGrinds
    CarrierOf <- TCarrierOf
    Meets <- TMeets
    PeerProofs <- TPeerProofs
    Real <- TReal
    TInit <- TTInit
    Trace <- TTrace
INVARIANTS {" ".join(INVARIANTS)}
"""


def check(path):
    t = json.loads(path.read_text())
    n = len(t["events"])
    if t.get("anomalies"):
        return False, f"{path.name}: FAIL ({n} events)\n  steps outside the model: {t['anomalies']}"
    with tempfile.TemporaryDirectory() as work:
        work = pathlib.Path(work)
        for f in ("DerivedChildGrinds.tla", "TraceDerivedChildGrinds.tla"):
            shutil.copy(ROOT / "specs" / f, work)
        (work / "MCTrace.tla").write_text(model(t))
        (work / "MCTrace_Run.cfg").write_text(cfg(t))
        out = subprocess.run([str(ROOT / "scripts" / "tlc.sh"), "MCTrace_Run.cfg", str(work)],
                             capture_output=True, text=True,
                             env={**os.environ, "TLC_CHECK_DEADLOCK": "1"}).stdout
    if "No error has been found" in out:
        return True, f"{path.name}: pass ({n} events)"
    steps = re.findall(r"^/\\ i = (\d+)", out, re.M)
    at = int(steps[-1]) if steps else None
    def show(e):
        return json.dumps({k: e[k] for k in e if k != "after"})
    if "Deadlock reached" in out and at is not None:
        why = f"event {at} is not a spec step: {show(t['events'][at - 1])}"
    elif (m := re.search(r"Invariant (\w+) is violated", out)) and at is not None:
        e = t["events"][at - 2]
        why = f"{m.group(1)} after event {at - 1}: {show(e)}\n  code after: {json.dumps(e.get('after'))}"
        spec = re.split(r"State \d+:", out)[-1]
        why += "\n  spec state:" + "".join(f"\n    {l.strip()}" for l in spec.splitlines()
                                            if re.match(r"\s*/\\ (status|credited|deriving|peerQ|hosted|jobs) ", l))
    else:
        why = "\n".join(l for l in out.splitlines() if re.search("Error|violated|Assumption", l)).strip() or out[-2000:] or "no TLC output"
    return False, f"{path.name}: FAIL ({n} events)\n  {why}"


def selftest(path):
    """Corrupt a passing trace; each corruption must be caught."""
    base = json.loads(path.read_text())
    ok, line = check(path)
    if not ok:
        return False, f"selftest: base trace must pass\n{line}"
    def checked(t, pred):
        return next((e for e in t["events"] if "after" in e and pred(e)), None)
    def credit(t):
        e = checked(t, lambda e: any(e["after"]["credited"].values()))
        c = next(c for c, g in e["after"]["credited"].items() if g)
        e["after"]["credited"][c] = []
        return "CreditedMatches"
    def status(t):
        e = checked(t, lambda e: "tree" in e["after"]["status"].values())
        c = next(c for c, s in e["after"]["status"].items() if s == "tree")
        e["after"]["status"][c] = "pending"
        return "StatusMatches"
    def deriving(t):
        e = checked(t, lambda e: e["after"]["hosted"])
        c = next(iter(e["after"]["deriving"]))
        e["after"]["deriving"][c] += 1
        return "DerivingMatches"
    def job(t):
        e = checked(t, lambda e: e["after"]["jobs"])
        e["after"]["jobs"] = []
        return "JobsMatch"
    def refused_as_taken(t):
        e = next((e for e in t["events"] if e["kind"] == "gossip" and e["accepted"]), None)
        if e is None:
            return None
        e["accepted"] = False
        return "not a spec step"
    def answer_first(t):
        # An answer before its derivation was issued.
        e = next(e for e in t["events"] if e["kind"] == "answer")
        t["events"].insert(0, {k: v for k, v in e.items() if k != "after"})
        return "not a spec step"
    results, ok = [], True
    with tempfile.TemporaryDirectory() as d:
        for corrupt in (credit, status, deriving, job, refused_as_taken, answer_first):
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
        paths += sorted(p.glob("trace-*.json")) if p.is_dir() else [p]
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
