# lattice-formal

Formal models of the Lattice protocol: TLA+ models checked with TLC, trace
validation of the implementation against them, and Lean proofs of value
conservation.

The models are written from the normative specification
([Lattice `docs/spec.md`](https://github.com/adalinxx/Lattice/blob/main/docs/spec.md)),
not from the implementation. A passing check means the listed properties hold
for every interleaving of the modelled facts, within the model's bounds and
abstractions. It does not mean Lattice is bug-free.

## Run

TLA+ requires Java 11+. The pinned `tla2tools.jar` (v1.7.4, SHA-256 checked) is
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
| `PhysicalWorkOnce`: a child block's weight equals the sum over the distinct physical grinds it rests on, computed from an independent reference (the deepest committing ancestor, not `NearestCarrier`) | invariant | §9.1, §9.10 |
| `AnchoredAtExecuted`: a validated child block is anchored at a state the parent's executed frontier produced; a child genesis never at empty | invariant | §5.1 rule 4, §5.3 step 6, §9.5 |
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
| `MCHierarchy_ParentBad.cfg` | `p2` and `p4` are invalid, so the parent's canonical tip moves to `p3`. The child block anchored at the excluded `p2` is held, not excluded, and `p4` still counts in its carrier's run; nothing in the child moves |
| `MCHierarchy_P1Gap.cfg` | `p1`'s body never arrives: the child block anchored there is held, not invalid, and the child acts on its sibling branch |
| `MCHierarchy_HeldInvalid.cfg` | `c3`'s anchor is sideways (continuity held) and its transition is invalid: `c3` is excluded, not held, so the child's canonical tip moves to `c1` |

The shared scenario also covers:
- a second child genesis with an empty anchor, which is invalid (§5.1 rule 4) and excluded once the other root executes;
- a parent fork below a carrier where each branch has its own carrier, so runs partition;
- a committed child block the child chain never holds, whose run is never credited;
- a merged grind credited differently at its parent and child locations.

In every model the child's fork is decided by the attributed run alone: `c1`
and `c2` tie on their own work, `c2` has the smaller CID, and `c1`'s parent
run is what makes it win.

Admission carries the block's securing grind in the same batch, as the
implementation's import does. Staged locations ahead of admission are covered
by `ForkChoice.tla`.

### Planted bugs

| Mutant | Model | Must be caught by |
|---|---|---|
| attributed run also counts the carrier's own grind | Main | `PhysicalWorkOnce` |
| nearest carrier skips the block itself | Main | `PhysicalWorkOnce` |
| no run attribution | Main | `ExpectedAnswer` |
| runs skip excluded parent blocks (follow canonicity) | ParentBad | `ExpectedAnswer` |
| continuity requires the anchor on the parent's canonical chain | Main | `ExpectedAnswer` |
| continuity accepts a weighed but unexecuted anchor | P1Gap | `AnchoredAtExecuted` |
| continuity allows a sideways anchor | Main | `AnchorsAdvance` |
| a child genesis may anchor at empty | Main | `AnchoredAtExecuted` |
| continuity is decided before the transition (a held anchor hides a failed transition) | HeldInvalid | `ExpectedAnswer` |

### Readings and limits

- **A failed transition is a verdict before continuity is answered.** §5.3
  orders continuity (step 6) before the transition (step 7), but the
  transition is checked against the block's declared `parentState`, so a
  failure there makes the block invalid whatever continuity concludes. The
  model excludes it even while its anchor is held; Lattice does the same, and
  the spec says so since adalinxx/Lattice#36.
- **A sideways anchor is held, never a verdict.** §9.5: a child "anchoring
  elsewhere is anchoring at something this parent has not checked, and the
  correct answer is the retriable 'not proven here', not a verdict". State
  CIDs are not block IDs, so a later header could still supply the path; the
  model's block-as-state abstraction must not turn that into a verdict.
- **An anchor at an excluded parent block** is never proven, so the child
  block stays held forever rather than being excluded (§9.9: an excluded
  block is "never treated as invalid by any peer on that account").
- **Header-rule exclusions** (§9.9: `spec` or `prevState` mismatch, recorded
  the moment a block is weighed) are not modelled; exclusion here always
  follows execution.
- **"Equality is never evidence" is unfalsifiable here**: a child block
  executes only after its predecessor validated, so an equal anchor was
  already proven. The hazard lives in implementations that act on weighed
  predecessors.
- Not modelled: multi-level recursion (Nexus → A → B, §9.10) and more than
  one child directory.

## Trace validation (`specs/TraceForkChoice.tla`)

The link from the model to the Swift code. Lattice's
`ForkChoiceTraceExportTests` drives the real `ChainTree` with a seeded random
sequence of facts and records, after every event, what the implementation
decided. `scripts/trace_check.py` replays each trace through `ForkChoice.tla`:

- each event must be a spec step, and the implementation's accept/refuse must
  match whether the spec allows it (a mismatch deadlocks TLC);
- after each event, the canonical tip, the validated (act-on) tip, every held
  block's subtree weight and its prefix work must equal the spec's.

```sh
scripts/trace_check.py traces/lattice-53.2.0            # all checks
scripts/trace_check.py --selftest traces/lattice-53.2.0/trace-2.json
```

The self-test corrupts a passing trace four ways (a weight, a prefix work, an
act-on tip, an accept flag) and requires each to be caught.

`traces/lattice-53.2.0/` holds 20 traces (800 events) exported from Lattice
53.2.0. Every event matches the spec on accept/refuse, canonical tip, act-on
tip, subtree weight and prefix work.

### Divergence found and fixed: the act-on tip at the genesis fork

Traces from Lattice before 53.2.0 differed from the spec in 7 of 20 traces,
always in the same shape: two genesis roots, where the executed root is not
the canonical (heaviest) one. The implementation returned no act-on tip; the
spec acts on the executed root.

- Spec: §9.9, "descending from genesis, at each fork it follows the heaviest
  child that is validated", and §9.4, a chain "may hold several genesis roots;
  the same rule applies to them".
- Implementation: `ChainTree.heaviestExecutedTip` started its descent at
  `executedPrefix()`, which follows the canonical root only.
- Consequence: on a child chain, which may hold several genesis roots, a
  heavier competing genesis whose body is withheld left every node with no
  act-on tip.

Fixed in Lattice 53.2.0 (adalinxx/Lattice#35), with the node's body scheduler,
mempool spec and boot walk following the same rule (adalinxx/lattice-node#15).
The regenerated traces differ from the old ones only in the act-on tip of those
7 traces.

## Hierarchy trace validation (`specs/TraceHierarchy.tla`)

Lattice's `HierarchyTraceExportTests` drives a real parent `ChainTree` and a
real child `ChainTree` from seeded random facts: commits, anchors, merged
grinds, verdicts, and withheld bodies. After every apply on either tree it
re-derives the attributed runs exactly as the node does. A child block's
continuity is decided by the implementation's own check, `validateParentFacts`
over the live parent tree, which is the call the connect path makes.
`scripts/hierarchy_trace_check.py` replays each trace through `Hierarchy.tla`:

- each event must be a spec step with the same accept/refuse, and each
  refusal reason must be the spec's: a child validation held for
  continuity, an observation refused because the grind is located
  elsewhere, an invalid root kept because no other root executed. A child
  exclusion's cause (transition or continuity) must be the spec's too;
- after each event, on both chains, the canonical tip, the act-on tip and
  every held block's weight (attributed runs included) must equal the
  spec's, and so must every held child block's continuity.

```sh
scripts/hierarchy_trace_check.py traces/hierarchy-434a3be
scripts/hierarchy_trace_check.py --selftest traces/hierarchy-434a3be/trace-2.json
```

`traces/hierarchy-434a3be/` holds 20 traces (Lattice PR #37 at `434a3be`):

| Recorded | Count |
|---|---|
| events | 1,600 |
| child validations proven | 25 |
| child validations held for continuity | 101 |
| child validations with continuity invalid | 7 |
| attributed runs credited (final states) | 17, in 12 traces |
| merged grinds | 29 |

All conform. The self-test corrupts a child weight, a continuity answer, a
child act-on tip, a held validation reported as accepted, a child
exclusion's cause, and an unreported grind-elsewhere refusal, and requires
each to be caught. The traces also fail against planted bugs in the model:
with no run attribution 12 of 20 fail, and with sideways anchors allowed 12
of 20 fail.

## Value conservation (`lean/`)

Lean 4 proofs, core library only, toolchain pinned in `lean/lean-toolchain`.
`LatticeProofs/Model.lean` models the value-bearing part of a block's state
transition from the spec:
- account balances, deleted at zero (§6.2);
- deposits and withdrawals, withdrawals first, with a permanent zero spent
  marker (§6.4);
- receipts and the debit and credit they derive (§6.5);
- the parent receipt a withdrawal needs (§8.1 phase 3);
- the fee rule and coinbase (§8.2).

| Theorem | Spec |
|---|---|
| `fee_nonneg`: a valid block's fee is never negative (no value creation) | §8.2, §8.3 |
| `spendable_with_recipient`, `spendable_without_recipient`: spendable supply changes by exactly `reward + W - D`, or `W - D - F` when fees burn | §8.2 |
| `locked_change`: locked value changes by exactly `D - W` | §8.2 |
| `value_with_recipient`, `value_without_recipient`: spendable plus locked changes by exactly the reward, or minus the burned fee | §8.2, §12.2 |
| `value_chain`: over any chain segment, total value moves only by issued rewards and burned fees | §12.2 |
| `withdrawal_authorized`: each withdrawal takes exactly the nonzero amount its deposit holds, and `parentState` holds the receipt naming its withdrawer | §8.1, §12.4.3-5 |
| `withdrawal_spends`, `spent_persists`, `spent_is_final`: a withdrawn deposit becomes a spent marker forever, and no valid block deposits or withdraws it again | §8.3, §12.4.6 |
| `deposit_fresh`, `receipt_fresh`: insertion only at absent keys | §12.4.1-2 |
| `receipt_provenance`: every receipt was inserted by a receipt action | §6.5 |
| `applyBlock_wf`: sub-states keep distinct keys and no zero balance | §6.2 |

```sh
cd lean && lake build                    # the proofs
lake env lean LatticeProofs/Axioms.lean  # only propext, Classical.choice, Quot.sound
python3 scripts/lean_mutants.py          # from the repo root
```

`scripts/lean_mutants.py` breaks one rule of the model at a time and requires
the proofs to stop building. Each mutant makes at least one stated theorem
false:
- a withdrawal leaves no spent marker;
- the coinbase pays the reward without the fees;
- no fee rule;
- a withdrawal ignores the parent receipt;
- over-withdrawal;
- a deposit overwrites;
- a negative balance is clamped.

Not modelled: general key-value actions and nonces (they move no value),
signatures, policies, state growth, the `Int64` and `UInt64` width bounds, the
genesis premine, and the Merkle proofs themselves (each map stands for its
proven sub-state).

## Roadmap

1. **Hierarchy depth:** a grandchild level, so attributed runs recurse
   (§9.10), and header-rule exclusions.
2. **Lean refinement:** connect `Model.lean` to the implementation with the
   same trace approach, or extend it with Merkle proof semantics and width
   bounds.
