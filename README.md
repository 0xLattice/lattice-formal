# lattice-formal

Formal models of the Lattice protocol, checked with TLC.

The models are written from the normative specification
([Lattice `docs/spec.md`](https://github.com/adalinxx/Lattice/blob/main/docs/spec.md)),
not from the implementation. A passing check means the listed properties hold
for every interleaving of the modelled facts, within the model's bounds and
abstractions. It does not mean Lattice is bug-free.

## Run

Requires Java 11+. The pinned `tla2tools.jar` (v1.7.4, SHA-256 checked) is
fetched on first use.

```sh
scripts/check.sh                       # every model, then every planted bug
scripts/tlc.sh MCMain.cfg              # one model (MC.tla)
scripts/tlc.sh MCHierarchy_Main.cfg    # <Module>_<name>.cfg checks <Module>.tla
```

Set `JAVA=/path/to/java` if `java` is not on `PATH`.

## Fork choice (`specs/ForkChoice.tla`)

Single-chain fork choice: spec §9.1–9.4 and §9.9. Two nodes receive the same
immutable facts (grind observations, headers, bodies) in independent orders.
Each derives the canonical tip (heaviest selectable path) and the validated tip
(the tip it acts on).

| Property | Kind | Spec |
|---|---|---|
| `Convergence`: quiescent nodes with the same facts derive the same weight for every block and select the same canonical and validated tips | invariant | §9.4, §9.8, §9.9 "independent of arrival order" |
| `WorkMonotone`: no step lowers any block's `trueCumWork`, exclusion included | action | §9.1, §9.9 "work weighs", §12.5.4 |
| `TipsWellFormed`: tip path admitted, one root, no excluded block; validated tip's path fully validated | invariant | §9.9, §12.3.3–4 |
| `NothingValidatedBelowExcluded` | invariant | §9.9 |
| `VerdictsSound`, `VerdictsPermanent`: an executed block is never excluded; verdicts never retract | invariant, action | §9.9 |
| `AgreeWhenValidated`: once the canonical path is validated, the node acts on the canonical tip | invariant | §9.9 |
| `CatchesUp`: with every body obtainable, the validated tip eventually reaches the canonical tip for good | liveness | §9.9 |
| `ExpectedAnswer`: quiescent tips equal hand-computed answers | oracle | §9.4 tie-break, §9.9 |

Models (`specs/MC.tla`) share one five-block tree that exercises every rule:
an invalid but heaviest root, the root-exclusion guard, an exact subtree tie,
a quantity ratchet, and a valid block under an excluded one.

| Config | Scenario |
|---|---|
| `MCMain.cfg` | all bodies available |
| `MCGap.cfg` | one body never arrives: canonical tip `b`, validated tip stuck at `r1` |
| `MCTie.cfg` | the exact tie decides the tip, by smaller CID |

### Planted bugs

A property that cannot fail proves nothing. `scripts/mutants.py` breaks one rule
at a time and requires the named property, checked alone, to go red:

| Mutant | Must be caught by |
|---|---|
| exclusion removes the excluded subtree's weight | `WorkMonotone` |
| last observation wins instead of the strongest | `Convergence` |
| execute a block whose parent is not validated | `NothingValidatedBelowExcluded` |
| canonical descent steps into excluded blocks | `TipsWellFormed` |
| exact tie breaks to the larger CID | `ExpectedAnswer` |
| a grind observed at two locations, which needs a SHA-256 collision (`MCProbeConflict.cfg`) | `Convergence` |

### Convergence rests on unique grind location

The last row is an assumption probe, not a code change. If one grind could be
observed at two blocks of the same chain, the "first location wins, conflict
rejected" rule (§9.1) would make the outcome depend on arrival order, and
nodes would diverge.

That cannot happen short of a SHA-256 collision. The root's bytes commit to
its `children` CID. `children` is one DAG-CBOR map with one CID per directory
(§3.1), and a chain is identified by its full path (§4.1). So a root has one
path to a given chain, and every hop is bound by a standard CIDv1 dag-cbor
sha256 link. Two terminals would need one CID to resolve to two contents.
The guarantee also needs strict decoding: a decoder that accepted duplicate
map keys would allow two children under one CID with no collision, so
canonical DAG-CBOR's duplicate-key rejection is part of the assumption.

Checked against cashew 5.0.3, the version Lattice 52.1.0 and lattice-node pin.
`DagCBOR.decode` re-encodes what it parsed and requires the same bytes, and
every content fetch goes through it after the SHA-256 check. That includes the
`FlatDictionary` children index the `ChildBlockProof` walk resolves. A children
map with two different children under one directory is refused, both when
decoded directly and when resolved by its CID. With the re-encode check
removed, the decoder silently keeps the last entry, so that one line is what
the guarantee rests on.

### Abstractions and limits

- **Verified work is an input.** An observation stands for a proof that
  already verified; PoW hashing, targets, retargeting and `ChildBlockProof`
  checking are not modelled.
- **Static block tree; verdicts and availability are constants.** They are
  facts about immutable bytes, so every node computes the same verdict.
  Availability is the same for every node.
- **Eager validation.** Any block with a validated parent may execute. The
  spec's lazy validation is a subset of these behaviours.
- **Header schedule and admission drops** (§9.9 timestamp, target, malformed
  headers) are folded into "admitted or not".
- **Recovery is by construction.** Both tips are functions of the fact set,
  so replay equals live import trivially here. Whether the implementation's
  cached subtree totals and persisted tip match this needs an implementation-
  level model or trace validation (below). For the same reason the root-
  exclusion guard is exercised but not pinned: its purpose, never recording a
  fact recovery could not replay, sits in the unmodelled persistence layer.
- **Small scope:** five blocks, two nodes, one chain.

## Hierarchy (`specs/Hierarchy.tla`)

One node hosting a parent chain and one child chain: parent-attributed run work
(§9.10), parent-state continuity (§5.3 step 6, §9.5), and fork choice with
weighed and validated tiers on each chain. The node receives every fact in
every order TLC can find. Reaching only one answer is the order-independence
check, so one node is enough here.

| Property | Kind | Spec |
|---|---|---|
| `PhysicalWorkOnce`: a child block's weight equals the sum over the distinct physical grinds it rests on; its components (child grinds, attributed runs) never share a grind | invariant | §9.1, §9.10 |
| `AnchoredAtExecuted`: a validated child block is anchored at a state the parent's executed frontier produced | invariant | §5.3 step 6, §9.5 |
| `AnchorsAdvance`: along validated child history, anchors never move back to empty or sideways | invariant | §5.3 step 6, §12.5.8 |
| `WorkMonotone`: no step lowers any block's weight on either chain, attributed runs included | action | §9.10 "only ever raised" |
| `TipsWellFormed`, `VerdictsPermanent` | invariant, action | §9.9 |
| `ExpectedAnswer`: quiescent tips equal hand-computed answers, and child weights equal ONE table shared by every model | oracle | §9.10, §12.5.7 |

The three models differ only in the parent's verdicts and body availability,
and must all produce the same child weights. That is §12.5.7, that parent
canonicity alone cannot change child weight, and §9.10's "independent of
exclusion and of parent canonicity".

| Config | Scenario |
|---|---|
| `MCHierarchy_Main.cfg` | the parent's canonical tip (`p2`) is on a different branch from the child's anchor (`p1`); the child still validates there |
| `MCHierarchy_P2Bad.cfg` | `p2` is invalid, so the parent's canonical tip moves to `p4`; nothing in the child moves |
| `MCHierarchy_P1Gap.cfg` | `p1`'s body never arrives: the child block anchored there is held, not invalid, and the child acts on its sibling |

In every model the child's fork is decided by the attributed run alone: `c1`
and `c2` tie on their own work, `c2` has the smaller CID, and `c1`'s parent
run is what makes it win.

### Planted bugs

| Mutant | Model | Must be caught by |
|---|---|---|
| attributed run also counts the carrier's own grind | Main | `PhysicalWorkOnce` |
| no run attribution | Main | `ExpectedAnswer` |
| runs skip excluded parent blocks (follow canonicity) | P2Bad | `ExpectedAnswer` |
| continuity requires the anchor on the parent's canonical chain | Main | `ExpectedAnswer` |
| continuity accepts a weighed but unexecuted anchor | P1Gap | `AnchoredAtExecuted` |
| continuity allows a sideways anchor | Main | `AnchorsAdvance` |

### Interpretation choices

Two places where the spec admits more than one reading. The model takes one
reading at each:

- **When a sideways anchor becomes a verdict.** The model records the child's
  exclusion as soon as the node holds both anchors' parent headers and the
  older is not an ancestor of the newer. Ancestry of held headers is
  immutable, so this is a completed deterministic check (§9.9). The other
  reading waits until the new anchor is also executed.
- **An anchor at an excluded parent block** is never proven, so the child
  block stays held (weighed, unvalidated) forever rather than being excluded.
  §9.5 calls continuity across unexecuted blocks "not proven here", never a
  verdict.

Also not modelled: the equality and back-to-empty continuity cases (no block
in these models repeats its predecessor's anchor or drops to empty),
multi-level recursion (Nexus → A → B, §9.10), and more than one child
directory.

## Roadmap

1. **Hierarchy depth:** a grandchild level, so attributed runs recurse
   (§9.10), plus the equality and back-to-empty continuity cases.
2. **Trace validation:** record fact streams from lattice-node's deterministic
   tests and simulator, then check each trace is a behaviour of these specs.
   This is the link from model to Swift code.
3. **Proofs:** Lean for cross-chain value conservation (§8.2, §12.2,
   §12.4).
