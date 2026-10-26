# lattice-formal

Formal models of the Lattice protocol: TLA+ models checked with TLC, trace
validation of the implementation against them, and Lean proofs of value
conservation and of the Merkle state commitments.

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

One node hosting a parent chain, a child chain and, optionally, a grandchild
chain (Nexus → A → B as P → C → G): parent-attributed run work
(§9.10), parent-state continuity (§5.3 step 6, §9.5), and fork choice with
weighed and validated tiers on each chain. The node receives every fact in
every order TLC can find. Reaching only one answer is the order-independence
check, so one node is enough here.

| Property | Kind | Spec |
|---|---|---|
| `PhysicalWorkOnce`: a child or grandchild block's weight equals the sum over the distinct physical grinds it rests on, computed from an independent reference (the deepest committing ancestor, not `NearestCarrier`, followed up through every level) | invariant | §9.1, §9.10 |
| `AnchoredAtExecuted`: a validated child block is anchored at a state the parent's executed frontier produced; a child genesis never at empty | invariant | §5.1 rule 4, §5.3 step 6, §9.5 |
| `AnchorsAdvance`: along validated child history, anchors never move back to empty or sideways | invariant | §5.3 step 6, §12.5.8 |
| `WorkMonotone`: no step lowers any block's weight on either chain, attributed runs included | action | §9.10 "only ever raised" |
| `HeaderExcludedOnAdmission`: a block breaking a header validity rule is excluded the moment it is weighed; `NothingValidatedBelowExcluded` | invariant | §9.9 |
| `TipsWellFormed`, `VerdictsPermanent` | invariant, action | §9.9 |
| `NothingStuck` (Hierarchy only, where `Admit` is gated; in ForkChoice every undelivered fact can always be observed): no reachable state is stuck with a fact undelivered, so `ExpectedAnswer` is never vacuous | invariant | §9.9 header admission |
| `ExpectedAnswer`: quiescent tips equal hand-computed answers, and child weights equal ONE table shared by every model | oracle | §9.10, §12.5.7 |

### Cross-chain fork choice (`specs/HierarchyProps.tla`)

These state how Hierarchical GHOST composes across chains. Each
independence property re-evaluates the model's own operators in a second
instance of `Hierarchy` with one input replaced, and requires the same
answer in every reachable state.

| Property | What is replaced or checked | Spec |
|---|---|---|
| `ChildrenCannotMoveParent`: a chain's weights, verdicts and tips are what they would be with every chain below it erased. Attribution flows down only, so no child chain, however much work or spam it carries, moves its parent's fork choice | every lower-chain block, location, quantity and verdict | §9.10 |
| `ParentCanonicityIrrelevant`: every chain below sees the same weights, verdicts and tips whichever branch of the parent is canonical, or validated and acted on | the parent's exclusions (all non-roots) and its CID order (reversed); what has executed is kept | §12.5.7 |
| `WeightIgnoresVerdicts`: no verdict on any chain, carriers' included, moves any block's weight ("work weighs, validity selects") | every verdict on every chain | §12.5.2, §9.9 |
| `NoDoubleBacking`: merged mining has nothing at stake. The work above that reaches one side of a lower fork through attributed runs, followed level by level to the root, never also backs the other side, genesis forks included | (direct) | §9.10 |
| `HeaviestAtEveryFork`: at every fork on the canonical path, at any depth and genesis forks included, the chosen block is the heaviest selectable sibling by whole-subtree work, ties to the smaller CID; the validated path likewise among validated siblings. Stated per fork rather than by descent, so a frozen prefix or a heaviest-chain rule fails it | (direct) | §9.4, §9.9, §12.5.10 |
| `ExcludedHasCause`: a block is excluded only for a header rule, a failed transition or a forbidden empty anchor. A missing body, a held anchor or an excluded ancestor never excludes | (direct, independent of `Verdict`) | §9.9 |
| `NothingPruned`: admitted blocks, located grinds and verified quantities only grow | action | §12.5.9 |

Checks keep these from passing vacuously. `ParentCanonMoves` and
`ParentValidatedMoves` require the replacement to really move the parent's
canonical and validated tips. `MCHierarchyFork_W.cfg` and
`MCHierarchyFork_WG.cfg` must *fail* `NoBackedFork` and
`NoBackedGrandchildFork`, showing that a child fork, and a grandchild fork
with parent-chain work behind it, each with work from above on both sides,
are reachable. They are reached only in `MCHierarchyFork`, which was added
for that purpose: the parent's branches tie, so its tips are decided by CID
alone, and each level below picks the side the level above did not.

The five two-level models differ only in verdicts, header-rule violations and body availability,
and must all produce the same child weights. That is §12.5.7, that parent
canonicity alone cannot change child weight, and §9.10's "independent of
exclusion and of parent canonicity".

| Config | Scenario |
|---|---|
| `MCHierarchy_Main.cfg` | the parent's canonical tip (`p2`) is on a different branch from the child's anchor (`p1`); the child still validates there |
| `MCHierarchy_ParentBad.cfg` | `p2` and `p4` are invalid, so the parent's canonical tip moves to `p3`. The child block anchored at the excluded `p2` is held, not excluded, and `p4` still counts in its carrier's run; nothing in the child moves |
| `MCHierarchy_P1Gap.cfg` | `p1`'s body never arrives: the child block anchored there is held, not invalid, and the child acts on its sibling branch |
| `MCHierarchy_HeldInvalid.cfg` | `c3`'s anchor is sideways (continuity held) and its transition is invalid: `c3` is excluded, not held, so the child's canonical tip moves to `c1` |
| `MCHierarchy_HeaderBad.cfg` | `p3` (the carrier of `c1`) and `c3` break a header validity rule (§9.9: `spec` or `prevState` mismatch), so each is excluded the moment it is weighed. `p3` and its descendant still weigh and its run still credits `c1`; `c3` is excluded rather than held, so the child's canonical tip moves to `c1` |
| `MCHierarchyFork_Main.cfg` | merged-mining forks at three levels. The parent's branches `pa` and `pb` tie, so its tips (`pa2`) are decided by CID alone; each carries its own child block. The child chooses `cb`, the other side (3 against 2), and its block `ca2` anchors deep on `pa`'s branch. The grandchild has a genesis fork backed through the child's runs and chooses `ga`, again the other side. No work above backs both sides of either fork |
| `MCHierarchy3_Main.cfg` | three levels: the run P attributes at a C carrier is credited work in that carrier's own run, so it reaches G (§9.10 "level by level"); P attributes both at the carrier and at a non-carrier member of its run; one grind is merged across all three levels, with a different quantity at each, and counted once at each |

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
| a header-rule violation is excluded only once executed | HeaderBad | `HeaderExcludedOnAdmission` |
| a header-rule violation is dropped instead of weighed (its descendants can then never land) | HeaderBad | `NothingStuck` |
| runs sum grinds only, dropping attributed work, so nothing recurses (identical to the spec at two levels) | Hierarchy3 | `ExpectedAnswer` |
| a run credits attributed work only at its carrier, not at its other members | Hierarchy3 | `PhysicalWorkOnce` |
| a grandchild's attributed run also counts the child carrier's own grind | Hierarchy3 | `PhysicalWorkOnce` |
| attributed runs count only once their carrier has executed | Main | `WeightIgnoresVerdicts` |
| the child credits only carriers on selectable parent branches | Fork | `ParentCanonicityIrrelevant` |
| child continuity requires the anchor on the parent's validated chain | Fork | `ParentCanonicityIrrelevant` |
| a run backs every child block anchored in it, not just the one its carrier commits | Fork | `NoDoubleBacking` |
| the grandchild credits every carrier that commits any grandchild block, not the block's own | Fork | `NoDoubleBacking` |
| a carrier is credited the child work it commits (upward attribution) | Fork | `ChildrenCannotMoveParent` |
| a held anchor excludes the block | Main | `ExcludedHasCause` |
| fork choice compares a block's own work, not its subtree's (heaviest chain, not GHOST) | Main | `HeaviestAtEveryFork` |
| an exclusion prunes the block | HeldInvalid | `NothingPruned` |

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
- **Header-rule exclusions** (§9.9: `spec` or `prevState` mismatch) are
  recorded in the same step that weighs the block. `ChainTree.insertHeader`
  applies the block, its work and the exclusion as one admission, all or
  nothing.
- **"Equality is never evidence" is unfalsifiable here**: a child block
  executes only after its predecessor validated, so an equal anchor was
  already proven. The hazard lives in implementations that act on weighed
  predecessors.
- Not modelled: more than one child directory per chain, and more than
  three levels. The recursion is the same at every level, so a third level
  is the first where it can go wrong. The three-level model has no forks,
  verdicts or missing bodies; those are checked at two levels only.

## Swaps under forks and reorgs (`specs/SwapReorg.tla`)

What a cross-chain swap guarantees when either chain forks or reorganizes
(§8.1, §8.3, §5.3 step 6, §9.5, §12.4). `Swap.lean` proves atomicity along
one valid branch; this model lets both chains fork and lets either
canonical tip move to any selectable block at any time, so each property
holds under every reorganization. Fork choice itself is not modelled
(`Hierarchy.tla` covers it): a tip may land wherever enough work could put
it.

A parent chain P and one child chain C each grow to four blocks, any block
extendable, with one swap. A P block inserts receipts (the withdrawer pays
the demander, §6.5), or is forged: it declares receipts in its `postState`
without a transition that produces them, and is weighed but never
executed. A valid P block above a forged one executes against the fetched
state but is off the executed-from-genesis frontier (§8.3 rule 2). A C
block deposits, withdraws, or does nothing; only valid C blocks are mined,
so the validity rule is the guard under test. As in `Hierarchy.tla`, a P
block stands for the state it produced and a C block's `parentState` is its
anchor. A branch's deposit state is its replay from genesis.

| Property | Kind | Spec |
|---|---|---|
| `WithdrawalBackedOnAnchorBranch`: every withdrawal on any child branch, canonical or not, is backed by its paid receipt (inserted by a frontier block) on every parent branch containing that block's anchor | invariant | §8.1 phase 3, §8.3, §12.4.4 |
| `NoDoubleRelease`: on any child branch, a deposit is released at most once | invariant | §8.3, §12.4.6 |
| `ReleaseHasDeposit`: a release needs the deposit in a strictly earlier block of the same branch | invariant | §8.1 phase 3, §12.4.3 |
| `SpentIffReleased`: a branch's replayed state shows a deposit spent exactly when that branch released it. State is per branch: the new canonical branch's replay does not contain the abandoned release, and never revives a deposit the new branch spent | invariant | §6.4 |
| `DemanderSafeIfAnchorCanonical`: once the canonical child tip anchors on the canonical parent chain, every release on the canonical child chain is paid on the canonical parent chain | invariant | §5.3 step 6, §8.1 "Receipt canonicity" |
| `WithdrawerCanRedeem` (a lemma that the withdrawal guard is not too strict, not a guarantee: nothing makes a miner include the release): a receipt paid on the canonical parent chain can be redeemed by a block on the canonical child tip, anchored at the parent tip, whenever the deposit is live there and the tip anchors on the canonical parent chain | invariant | §8.1 phase 3 |

Witnesses (each must FAIL):

| Config | Fails | Shows |
|---|---|---|
| `MCSwapReorg_WParentReorg.cfg` | `NaiveCanonicalBacking`: a release on the canonical child chain is paid on the canonical parent chain, even after the parent reorganizes away from the receipt | the demander's exposure: the child keeps a release anchored on an abandoned parent branch |
| `MCSwapReorg_WChildReorg.cfg` | `PaidImpliesReleased`: once released, a receipt paid on the canonical parent chain stays released on the canonical child chain | the withdrawer's exposure: the child reorganizes away from the release (in the shortest trace, the deposit with it) while the payment stands |
| `MCSwapReorg_WTwoBranches.cfg` | `ReleasedOnOneBranch` | one deposit released on two child branches: `NoDoubleRelease` is per branch |
| `MCSwapReorg_WRedeem.cfg` | `NoRedeemAfterReorg` | `WithdrawerCanRedeem` applies after a release was reorged out |
| `MCSwapReorg_WDemanderSafe.cfg` | `NoSafeReleaseBesideParentFork` | `DemanderSafeIfAnchorCanonical` applies while another executed parent branch lacks the receipt |

### Planted bugs

| Mutant | Must be caught by |
|---|---|
| a withdrawal accepts any receipt the node has seen on any parent branch | `WithdrawalBackedOnAnchorBranch` |
| a withdrawal reads the parent's canonical tip instead of its `parentState` | `WithdrawalBackedOnAnchorBranch` |
| continuity accepts a weighed, unexecuted anchor | `WithdrawalBackedOnAnchorBranch` |
| continuity accepts an executed anchor off the executed-from-genesis frontier | `WithdrawalBackedOnAnchorBranch` |
| an anchor may move sideways | `DemanderSafeIfAnchorCanonical` |
| replay drops the spent marker (the key is deleted, not zeroed), so the deposit is made again and released twice against one receipt (`MCSwapReorg_Replay.cfg`: one parent block, four child blocks) | `NoDoubleRelease` |
| a withdrawal accepts the spent marker (checks presence, not a nonzero value) | `NoDoubleRelease` |
| a withdrawal skips the deposit proof | `ReleaseHasDeposit` |
| a withdrawal needs the receipt inserted in the anchor block itself | `WithdrawerCanRedeem` |

### Readings and limits

- **The guarantee is conditional on the anchor's branch.** A release is
  backed on every parent branch through its anchor, whichever is
  canonical. Nothing ties it to the parent's canonical chain: §8.1 relies
  on the child reorganizing once the honest branch, anchored on the
  canonical parent, is heavier. That step is fork choice and hashrate,
  outside this model, which is why the naive canonical form fails here.
- **Exposures.** The demander is safe once the child's canonical tip
  anchors at or above the parent block holding the receipt and both stay
  canonical. The withdrawer is exposed until the release is confirmed on
  the child: a child reorg can drop it, and if the deposit is dropped too
  there is nothing to redeem; while the deposit stays live on the
  canonical child, the receipt can be redeemed again (`WithdrawerCanRedeem`
  says the guard allows it; nothing makes a miner include it). If the
  canonical child tip anchors on an abandoned parent branch, the withdrawer
  cannot redeem until the child reorganizes. A receipt is admitted
  without any deposit (§8.1 phase 2), so paying before the deposit is
  confirmed on the child is the withdrawer's risk.
- Not modelled: fork choice, amounts and accounts (`Swap.lean`), more than
  one swap or directory, and invalid child blocks (excluded, never
  canonical).

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

### Three levels and header rules

Lattice PR #38 extends the exporter to three chains, P → C → G, and to the
§9.9 header rules. Each generated block's header is classified by the real
`Block.headerAdmission`: a block whose `spec` or `prevState` differs from its
parent's is weighed and excluded in one step. Since Lattice PR #42 every
admission goes through the real `ChainTree.insertHeader`, and the trace's
header-exclusion flag is read back from the tree afterwards, not from the
harness (the traces were byte-identical before and after that change).
Grandchild continuity is decided by `validateParentFacts` over the live C
tree, and attributed runs are re-derived parents first, as the node does, so
a run P attributes at a C block reaches G through C's runs. The replay
compares every chain, both lower chains' continuity, and each admission's
header-exclusion flag. Each block's declared prevState is part of the trace,
because a carrier breaking the prevState rule anchors its committed child at
the state it declared, not at its parent's (`PrevState` in `Hierarchy.tla`).

```sh
scripts/hierarchy_trace_check.py traces/hierarchy3-8c60c39
scripts/hierarchy_trace_check.py --selftest traces/hierarchy3-8c60c39/trace-10.json
```

`traces/hierarchy3-8c60c39/` holds 20 traces (Lattice PR #38 at `8c60c39`),
2,400 events:

| Recorded | P | C | G |
|---|---|---|---|
| blocks | 127 | 131 | 132 |
| header-rule violations (`spec` / `prevState`) | 17 / 12 | 12 / 12 | 1 / 8 |
| carriers breaking a header rule | 19 | 20 | – |

There are 65 P → C and 61 C → G commits, and 59 header-excluded admissions.
Merged grinds lie on every proof path: P–C–G 7, P–C 18, C–G 16, P–G 6. In 6
traces a G block's attributed run carries work P attributed into C.

All conform. The self-test adds three corruptions for three-level traces: a
grandchild weight, a grandchild continuity answer, and a header exclusion
reported as an ordinary admission. Planted bugs in the model fail the
traces: runs that drop attributed work, so nothing recurses, fail 6 of 20,
and a header exclusion recorded only after execution fails all 20.

## Value conservation (`lean/`)

Lean 4 proofs, core library only, toolchain pinned in `lean/lean-toolchain`.
`LatticeProofs/Model.lean` models the value-bearing part of a block's state
transition from the spec:
- account balances, deleted at zero (§6.2);
- deposits and withdrawals, withdrawals first, with a permanent zero spent
  marker (§6.4);
- receipts, with a nonzero demand, and the debit and credit they derive
  (§6.5);
- the parent receipt a withdrawal needs (§8.1 phase 3);
- the fee rule and coinbase (§8.2);
- the width bounds: a delta is an `Int64` other than `Int64.min` (§3.6), a
  coinbase paid to a recipient fits an `Int64` (§5.2 step 11; a
  burned one has no bound), and a balance fits a `UInt64` (§6.2).

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
| `balances_fit`, `coinbase_fits`: every balance fits a `UInt64`, and a paid coinbase an `Int64` | §6.2, §5.2 |
| `receipt_value_provenance`, `deposit_value_provenance`: after a valid block, every receipt entry (with its withdrawer) and every live deposit (with its amount) was already there or was inserted by an action of the block | §6.4, §6.5 |
| `receipt_chain_provenance`, `deposit_chain_provenance`: the same over a valid run from empty receipt (deposit) state: each entry comes from an action in some block of the run | §6.4, §6.5 |
| `swap_atomic`: every withdrawal in a valid child run is backed by a receipt in a valid parent block whose account actions include the withdrawer's debit and the demander's credit (gross, before netting), and by a deposit of exactly the withdrawn amount in a strictly earlier child block | §6.4, §6.5, §8.1, §12.4 |
| `withdrawal_once`, `receipt_once`, `payment_releases_once`: across a valid run, no two withdrawal actions release the same deposit, no two receipt actions record the same payment, and, within one child run, no two withdrawals consume the same parent receipt | §8.3, §12.4 |

```sh
cd lean && lake build                    # the proofs
lake env lean LatticeProofs/Axioms.lean  # only propext, Classical.choice, Quot.sound
python3 scripts/lean_mutants.py          # from the repo root
```

### Cross-chain swaps (`LatticeProofs/Swap.lean`)

A swap locks value on a child chain and pays for it on the parent. On the
child at directory `dir`, a deposit locks `amountDeposited` at
`(demander, amountDemanded, nonce)`. On the parent, a receipt naming the
withdrawer is inserted at `(dir, demander, amountDemanded, nonce)` and
moves `amountDemanded` from the withdrawer to the demander. Back on the
child, a withdrawal that the receipt in its `parentState` names releases the
deposit and leaves the spent marker.

Atomicity here is the safety half: no deposit is released without the
payment. `swap_atomic` takes a valid parent run from empty receipts, a valid
child run from a well-formed state with no deposits, and the hypothesis that
the withdrawing child block's `parentState` receipts are those of some state
the parent run reached. Then each withdrawal in that block has its receipt in a valid parent
block, that block's account actions include the withdrawer's debit and the
demander's credit, and a strictly earlier child block made the deposit
(withdrawals see only `prevState`, so a deposit cannot be withdrawn in its own
block).

The payment is stated gross, not net: the derived debit `(withdrawer,
-amountDemanded)` and credit `(demander, amountDemanded)` are among the
block's account actions, but deltas net per owner (§6.2), so other actions in
the same block may cancel them. Debiting the demander that way needs the
demander's signature, which is not modelled.

Uniqueness is counted per action position, so two copies of one action count
twice. `withdrawal_once`: within one valid run, no two withdrawals release the
same deposit. `receipt_once`: within one valid run, no two receipts record the
same payment. `payment_releases_once` is `withdrawal_once` mapped through the
injective map from a deposit key to the receipt key it consumes: within one
child run, each parent receipt releases at most one deposit.

Not covered:
- **Signatures.** Nothing in the model ties the withdrawal's credit to the
  withdrawer; the receipt names the withdrawer, but who the withdrawn value
  goes to is the transaction's account actions, unconstrained here.
- **Liveness.** That a paid receipt can always be withdrawn on the child
  (the deposit is still live, the child sees the parent state) is not
  proved.
- **Anchor validity and reorgs.** That a child's `parentState` is a state of
  the parent's chain is the hypothesis above, not a theorem here; the TLA+
  hierarchy model covers anchoring (§5.3 step 6, §9.5). "Paid in a valid
  parent block" means on the parent branch the child anchors to, which may
  not be canonical: parent canonicity does not enter (§9.9). If that branch
  is abandoned, the payment reverts, and the child withdrawal goes with it
  only through reorg coupling (§5.3, fork choice), which is not proved here;
  `specs/SwapReorg.tla` checks what holds under forks and reorgs.

### Refinement by traces

The proofs say the model conserves value; the traces say Lattice's state
transition is the model. Lattice's `ValueTransitionTraceExportTests` builds
seeded chains of child-chain blocks and runs each through the real validator
(`Block.validateNexus`, the full non-genesis path: action shape rules, fee
rule and coinbase, parent receipts, state proofs and updates). It records the
entering state, the parent receipts, the block's value actions, reward and
recipient, and the implementation's verdict and post-state, read back from
its real state. `lake exe tracecheck` replays every case through `applyBlock`:
the verdict must agree, and on a valid block every entry of the three post
sub-states must be equal.

```sh
cd lean && lake build tracecheck
.lake/build/bin/tracecheck ../traces/value-2dfbab1/*.json ../traces/value-width-38bef1e/*.json
```

`traces/value-2dfbab1/` holds 510 cases (Lattice PR #39 at `2dfbab1`), all
conforming:
- 332 valid blocks: 251 with a recipient and 81 burning fees, with spent
  markers in 102. 105 are valid only because account deltas net per owner: in
  action order the owner's debit comes first and alone overdraws it. Others
  rely on the coinbase netting with the recipient's own debits.
- 178 blocks that each break exactly one rule, and the test asserts the
  implementation rejects each at that rule's check (a deposit and a receipt
  at an existing key share the insertion-proof failure, and a wrong-amount
  and a spent withdrawal share the spend check): overdraft, the fee rule, a
  zero delta, a zero deposit, a deposit or receipt at an existing key, a
  withdrawal with the wrong amount, of a spent deposit, without a parent
  receipt or with one naming another withdrawer, of a deposit made in the
  same block (withdrawals come first, §6.4), and zero demands or amounts on
  receipts and withdrawals.

`traces/value-width-38bef1e/` holds 140 more (Lattice PR #41 at `38bef1e`),
on a chain whose reward is 2^62 so that balances can reach the bounds, all
conforming. 40 break one width bound, and the implementation rejects each
at that bound's check: a
delta of `Int64.min`, an owner's net credit beyond `UInt64`, a balance beyond
`UInt64` (by transfer or by the coinbase), and a paid coinbase beyond
`Int64`. The valid ones sit at the bounds: deltas of ±`Int64.max`, a balance
of exactly `UInt64.max`, a coinbase of exactly `Int64.max`, and a burned
coinbase beyond `Int64.max`, which is accepted.

Checking the model against the implementation found two rules the spec did
not state, and the model lacked one of them: a receipt needs a nonzero
`amountDemanded`, and a block's account deltas, explicit, receipt-derived and
the coinbase alike, net per owner before any balance moves. The spec states
both since adalinxx/Lattice#40, and the model has the receipt rule.

### Planted bugs

`scripts/lean_mutants.py traces/value-2dfbab1 traces/value-width-38bef1e`
breaks one rule of the model at
a time. A rule a theorem depends on must make the proofs stop building, and
every value-model mutant must make the model disagree with the implementation's
traces. The Merkle trie has no implementation traces yet, so its mutants must
break the proofs:

| Mutant | Proofs | Traces |
|---|---|---|
| a withdrawal leaves no spent marker | break | disagree |
| the coinbase pays the reward without the fees | break | disagree |
| no fee rule | break | disagree |
| a withdrawal ignores the parent receipt | break | disagree |
| over-withdrawal | break | disagree |
| a deposit overwrites | break | disagree |
| a negative balance is clamped | break | disagree |
| a paid coinbase is unbounded | break | disagree |
| a balance may exceed `UInt64` | break | disagree |
| a withdrawal checks the child's own receipts, not `parentState`'s | break | disagree |
| a receipt key drops the directory | break | disagree |
| a receipt overwrites an existing one | break | disagree |
| a receipt debits the withdrawer but credits no demander | break | disagree |
| a withdrawal accepts a receipt naming any withdrawer | break | disagree |
| deposits applied before withdrawals (`swap_atomic`'s "strictly earlier") | break | disagree |
| a burned coinbase is bounded too | (no theorem states it) | disagree |
| a delta of `Int64.min` is accepted | (no theorem states it) | disagree |
| a receipt with zero demand is accepted | (no theorem states it) | disagree |
| balances move delta by delta in action order, not netted | (no theorem states it) | disagree |
| a deletion skips the collapse | break | (not traced) |
| a node's digest ignores its prefix | break | (not traced) |
| an insertion reads a stub child as absent | break | (not traced) |
| a split keeps the old prefix on the moved node | break | (not traced) |
| the root `count` does not move | break | (not traced) |
| an inserted child is not put in character order | break | (not traced) |
| an insertion overwrites an existing value | break | (not traced) |
| a deletion at a key with no value succeeds | break | (not traced) |
| a collapse merges a stub instead of failing | break | (not traced) |
| the root's digest ignores `count` | break | (not traced) |

Not modelled: general key-value actions and nonces (they move no value),
signatures, policies, state growth, the encoding bounds of the other action
fields (a value outside them cannot be written), and the genesis premine.
Each map stands for its proven sub-state; what a sub-state root commits to is
the subject of the next section.

### Merkle state commitments

`LatticeProofs/Merkle.lean` models how a block commits to each sub-state. The
spec does not define the structure (see the discrepancies below), so this
model is written from the implementation: cashew 5.0.3, the version Lattice
pins, whose `MerkleDictionary` is a path-compressed radix (Patricia) trie
keyed by characters.

- **Trie.** A root holds a `count` and children filed under a key's first
  character; it has no prefix and no value. An inner node holds a `prefix`, an
  optional `value`, and children filed under the next character, in character
  order. A node's digest is an abstract `H` of its fields with each child
  replaced by the child's digest (`Enc`); the root's CID is the commitment.
- **Partial trie.** There is no proof object. A validator resolves the nodes
  on the touched paths (each fetched by CID and hash-checked) and leaves every
  other child as a stub that names only its digest. One type, `Trie`, holds
  both; a full trie is one with no stub (`Full`).
- **Reads** return `found`, `absent`, or `unknown` (a stub on the path). The
  implementation reads with `try? get`, which turns `unknown` into absent.
- **Writes** (`insert`, `update`, `delete`) follow `RadixNode.transform` for
  one key: an insertion splits a prefix where the key leaves it, a deletion
  collapses (a node left with no value and one child merges into it, and the
  merged child must be resolved), the preconditions of `proof()` are enforced
  (insertion at an absent key, update and deletion at a present one), and a
  write that needs a stub's contents fails. The root never collapses, refuses
  the empty key, and moves `count` by `+1`, `0` or `-1`.
- **Canonical form** (`Canon`): every node resolved with a nonempty prefix,
  a value or at least two children, children filed under their prefix's first
  character in strictly increasing order, and `count` equal to the number of
  entries.

**Collision resistance.** `H` is not assumed injective: a 256-bit digest of
unbounded encodings has collisions, so that hypothesis would make every
theorem vacuous for SHA-256. A theorem that compares digests assumes instead
`NoCollision H A B`, that no encoding of a resolved node in the tries it names
collides with another (for a run of writes, every trie the run reaches,
`Root.RunHasEnc`). That holds unless those particular tries contain a SHA-256
collision, so each theorem reads in the standard form: a breach yields a
SHA-256 collision among the nodes involved. `or_collision` turns any of them
into that form, and `lookup_sound_or_collision`, `apply_sound_or_collision`
and `block_commits_or_collision` state it outright: the property holds, or
two distinct encodings, one from each side, have the same digest. Theorems
about canonical tries take `StrictOrder K`, that the character order is a
strict total order.

| Theorem | Spec |
|---|---|
| `or_collision`, `lookup_sound_or_collision`, `apply_sound_or_collision`, `block_commits_or_collision`: the collision-extraction forms: the property holds or a collision between the two sides' nodes is exhibited | §6.1, §11 |
| `lookup_sound`: a read of a partial trie whose root equals a full trie's, when found or absent, is that trie's read | §6.1 |
| `unknown_write_fails`, `read_then_write_sound`: a write through a stub fails, so a write that succeeds read no stub, and the `try? get` read it was chosen from is the committed value | §6.1 |
| `apply_sound`: a write that succeeds on a partial trie gives the root the same write gives on the full trie | §6.1 |
| `apply_correct`, `apply_complete`: on a canonical trie a write succeeds exactly when its precondition holds on the map, changes the map at its key only, and leaves the trie canonical, `count` included | §6.1-6.5 |
| `canonical_unique`, `digest_of_map`: two canonical tries that hold the same map are equal, so the root is a function of the map, not of the writes that built it | §3.4 |
| `witness_digest`, `witness_live`: the partial trie that resolves only a write's path and the nodes of the children along it has the same root, and the write succeeds on it with the same result (this witness resolves more than cashew's `proof()`, see below) | §6.1 |
| `applyAll_sound`, `applyAll_correct`, `batch_eq_fold`: the same for writes one after another; a batch result that is canonical and holds the map the writes make is the sequential result | §6.1 |
| `commits_empty`, `commits_unique`, `block_commits`, `chain_commits`, `chain_from_empty`: from the empty root, a chain of blocks, each verified against a partial trie of the root the last one left, ends at the root of the canonical trie of the map its writes make | §12.1 |
| `receipts_commit`: tied to the value model for the receipt sub-state: the root after a block's receipt writes commits to exactly the receipts `applyReceipts` produces | §6.5, §12.1 |

Abstracted: the DAG-CBOR bytes and the CID's multibase text (a node's digest
is `H` of its fields); SHA-256's collision resistance (the `NoCollision`
hypotheses above); key characters (any `K` with decidable equality and a strict
order; the implementation's keys are visible ASCII); `encryptionInfo` (Lattice
writes state tries unencrypted); Volume storage and pinning; nested dictionaries as
values. The root `count` is modelled: it is in the digest, moves by
arithmetic, and is equal to the number of entries in a canonical trie.

**Batches.** Lattice writes each sub-state in one `transform` pass over all
of a block's keys (one write per key), after one `proof()` that resolves
every path, and the batch collapses jointly. The model applies writes one at
a time (`Root.applyAll`). `batch_eq_fold` reduces the gap to one property:
if cashew's batch output is canonical and holds the map the writes make, it
is the sequential result, because there is only one such trie. That property
of cashew's batch code (`insertAll`, `transformPrefixLonger`,
`transformDivergent`, the joint collapse and `resolveGrandchildren`) is not
proven. Only the receipt sub-state is tied to the value model; balances and
deposits use the same writes but are not.

**Liveness is shown for a larger proof than cashew's.** `witness` resolves, at
every node on the path, all children's nodes (and at the key's own node, its
children's nodes even when the write is not a deletion). cashew's `proof()`
resolves the path and fetches grandchildren only where a batched deletion
could leave one child (`shouldExpandForBatchedDeletion`). `witness_live` shows
that the larger partial trie suffices; it does not show that cashew's smaller
one does.

**Spec and implementation differ** (found while mapping the model; Lattice
is not changed here):
- §2, §3.4 and §11 call each sub-state an SMT (sparse Merkle tree). It is a
  character-keyed compressed radix trie whose root also commits to a `count`
  of entries.
- §6.1 partitions actions into 5 groups, generates "Sparse Merkle proofs" and
  assembles 5 roots. `LatticeState` has 4 sub-states (account, general,
  deposit, receipt), and there is no proof object: the proof is the partially
  resolved trie, and the transform recomputes the root from it.
- A child link is encoded as a `{"rawCID": <CID text>}` map, and a node's
  children as an array of `{key, value}` entries sorted by key. The spec says
  neither.
- The canonical shape is not stated in the spec, and cashew checks only part
  of it on decoding. Its strict DAG-CBOR decode (re-encoding must give back
  the bytes) enforces single-character child keys, strictly increasing child
  order and no duplicates. It does not check that a child's prefix starts with
  the character it is filed under, that a prefix is nonempty, that a node holds
  a value or at least two children, or that `count` matches the contents. The
  root is a function of the map only because every state is a transform
  output from the empty root.

```sh
cd lean && lake build                    # includes the Merkle proofs
lake env lean LatticeProofs/Axioms.lean  # lists the Merkle theorems too
```

## Import and recovery (`specs/Recovery.tla`)

One node importing into one chain, crashing anywhere: spec §9.3 steps 8-9,
§9.8, §9.9 (exclusions are replayed facts) and §12.5.11. Each import attempt
is checked against the live graph under the mutation lease, staged as one
immutable batch in a durable log, then applied to the in-memory graph through
the reducer. A crash may fall between any two steps, during recovery
included. It loses the graph, the projection, the revision and any commit in
flight. Recovery replays the log through the same reducer, in any order the
prerequisites allow, then reprojects and only then exposes the runtime. The
genesis batch is staged before any runtime exists and appears only through
that path.

Batches are the implementation's kinds: a block (with its securing grind, and
its validation in the eager tier), a work fact (a grind location or a
strengthening of one), an exclusion, a validation. The weights and tip rule
are `ForkChoice.tla`'s, restated over a graph value so a replayed graph and a
live one can be compared.

| Property | Kind | Spec |
|---|---|---|
| `RecoveredEqualsLive`: while the runtime is exposed, its graph, every weight and the tip equal what the durable prefix produces applied in staging order, minus a batch staged and not yet applied, whether built live or rebuilt by replay in any order; the tip is a projection of that graph | invariant | §9.3 "the same immutable facts through the same reducer", §9.8 |
| `VisibleImpliesDurable`: nothing exposed is missing from the log, and no runtime exists before the genesis batch is durable | invariant | §9.3 "Durability MUST precede visible graph mutation", genesis bootstrap |
| `ReplayIdempotent`: applying any durable batch again to the exposed graph changes nothing | invariant | §9.3, §9.8 "idempotently" |
| `ConflictRejected`: the log never holds two metadata values for one block or one grind at two blocks, and the graph holds the durable metadata | invariant | §9.3, §9.1 |
| `RevisionMonotone`: no exposed revision is lower than one exposed before a crash | invariant | §12.5.11 |
| `RevisionAdvances`: every live mutation takes a strictly greater revision | action | §12.5.11 |
| `FailureLeavesGraphUnchanged`: a failed durable write changes neither graph, tip nor revision | action | §9.3 |
| `StagedBecomesVisible`: once crashes stop, the runtime comes up and every durable batch is visible, for good | liveness | §9.8 |

The scenario (`specs/MCRecovery.tla`) is a root `r` with children `a` and
`b`. The candidates move the tip at every step: `a`, then `b` (heavier), a
grind located at `a` that ties them (CID decides), its strengthening, an
exclusion of `a`, a validation of `b`, and a block fact for `a` with
different metadata, which the store must refuse. Up to five batches, two
crashes.

| Config | Reading |
|---|---|
| `MCRecovery_Main.cfg` | the spec's: replay in any order. Staging records the reserved revision as a durable floor, and restore records the restored revision before exposing it |
| `MCRecovery_Node.cfg` | the implementation's: no floor (lattice-node restores with none), replay in `ChainTree.replay`'s sort order |

Witnesses, each of which must fail: `MCRecovery_WLost.cfg` reaches a crash
between durable and visible, after which recovery shows the batch
(`NoLostBatchRecovered`), and `MCRecovery_WConflict.cfg` reaches the store's
refusal of conflicting metadata (`NoConflictRefused`).
`MCRecovery_WOrder.cfg` drops both the floor and the sort, and
`RevisionMonotone` fails: replay that meets a strengthening before the
weaker observation counts one mutation fewer than live import did. Either
one is needed.

### Planted bugs

| Mutant | Must be caught by |
|---|---|
| the batch is applied when checked, before its durable write | `VisibleImpliesDurable` |
| live import re-resolves the candidate after durability and applies what it finds (a stronger observation) | `RecoveredEqualsLive` |
| a strengthening adds to the quantity instead of ratcheting it | `ReplayIdempotent` |
| restore takes the persisted tip instead of reprojecting | `RecoveredEqualsLive` |
| restore resets the revision | `RevisionMonotone` |
| the floor is recorded only at staging, not at restore (replay order changes the count) | `RevisionMonotone` |
| only new blocks take a revision | `RevisionAdvances` |
| the store accepts a block fact with conflicting metadata | `ConflictRejected` |
| a failed durable write keeps the batch applied | `FailureLeavesGraphUnchanged` |
| an exclusion is staged but never applied live | `StagedBecomesVisible` |

### Finding: revisions can go back across a restart

`MCRecovery_RevisionProbe.cfg` must fail `RevisionMonotone` under the
implementation's reading. A grind is strengthened at `a` (two work batches,
each a mutation with its own revision); then `a`'s deferred validation is
staged as a block batch that re-states the strongest grind the tree holds
(`ChainTree.connectJob`), which live import applies as a duplicate. Replay
sorts block batches before work batches, so that batch lands the grind at its
final quantity in one mutation and both work batches replay as duplicates.
The restored revision is one lower than the last one exposed, and lattice-node
passes no `revisionFloor` to `ChainTree.restore`. With the floor of
`MCRecovery_Main.cfg` the probe passes.

It needs two observations of one grind at one location with different
quantities, which §9.1 allows ("strengthening"). Consensus is unaffected; the
revision is the API's change counter.

### Readings and limits

- **The durable write is atomic.** lattice-node writes every fact of a step
  in one SQLite transaction, and a conflicting fact ID rolls it back. So a
  crash never leaves part of a batch durable. A partial write is not
  modelled.
- **One commit at a time.** The mutation lease covers check, stage and
  apply, so the check cannot go stale before the apply. Preparation outside
  the lease is folded into `Admissible`.
- **Re-staging an identical batch** is not generated (it would only lengthen
  the log); `ReplayIdempotent` checks the re-application it would cause.
- **Order of visibility.** The model follows Lattice's commit path (stage,
  then apply). lattice-node's sans-IO core mutates its tree first and emits
  the persist effect before any publish, send or mining effect, stopping the
  process if the write fails. Nothing outside the step sees the tree before
  the write, which is the state this model's `up` exposes.
- **Revisions without a fact** (`reevaluateForkChoice` bumping on a
  projection change alone) are not modelled. Validations take no revision,
  as in the implementation.
- **Static verdicts and prerequisites.** Proof checks, execution and target
  rules are folded into which batches exist and `Admissible`. Orphans
  (blocks staged before their parent) are not generated.
- **Small scope:** three blocks, eight candidate batches, five durable
  batches, two crashes.

## Roadmap

1. **Lean:** cashew's batch transform, that its output is canonical (closes
   the batch gap above).
2. **Lean:** tie the balance and deposit sub-states to the Merkle model.
