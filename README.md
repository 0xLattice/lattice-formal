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
scripts/check.sh            # every model, then every planted bug
scripts/tlc.sh MCMain.cfg   # one model
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

A property that cannot fail proves nothing. `scripts/mutants.sh` breaks one rule
at a time and requires the named property to go red:

| Mutant | Must be caught by |
|---|---|
| exclusion removes the excluded subtree's weight | `WorkMonotone` |
| last observation wins instead of the strongest | `Convergence` |
| execute a block whose parent is not validated | `NothingValidatedBelowExcluded` |
| canonical descent steps into excluded blocks | `TipsWellFormed` |
| exact tie breaks to the larger CID | `ExpectedAnswer` |
| a grind observed at two locations (`MCProbeConflict.cfg`) | `Convergence` |

### Finding: convergence rests on unique grind location

The last row is an assumption probe, not a code change. If one grind can be
observed at two blocks of the same chain, the "first location wins, conflict
rejected" rule (§9.1) makes the outcome depend on arrival order, and nodes
diverge. Convergence therefore depends on the claim that a root's sparse
directory path resolves to exactly one terminal per chain (§9.5). That claim
lives in proof verification (cashew paths and `ChildBlockProof`), outside this
model, and is the next thing worth proving.

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

## Roadmap

1. **Hierarchy:** parent-attributed run work (§9.10), parent-state continuity
   (§5.3, §9.5), and invariant §12.5.7, that parent canonicity alone cannot
   change child validity, weight or fork choice.
2. **Trace validation:** record fact streams from lattice-node's deterministic
   tests and simulator, then check each trace is a behaviour of these specs.
   This is the link from model to Swift code.
3. **Proofs:** Lean for the unique-location claim and for cross-chain value
   conservation (§8.2, §12.2, §12.4).
