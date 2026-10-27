/-!
# Work from targets (spec §5.4, §9.1, §9.5)

`workForTarget` and `workForHash` exactly as Lattice's `LatticePoW`
computes them, over a width `N` (`N = 2^256` for `U256`, `U256_MAX = N - 1`).
A hash `h` meets target `t` when `0 < t ∧ h ≤ t` (`validateProofOfWork`), so
`t + 1` of the `N` hash values meet a nonzero target.

* `workForTarget t = ⌊N / (t + 1)⌋` for every nonzero target, which is
  Bitcoin's chainwork `(~t / (t + 1)) + 1` in `N`-bit arithmetic; target `0`
  is credited `0` and is met by no hash.
* Incentive: one hash at target `t` earns `(t + 1) / N · workForTarget t`
  in expectation. That is at most `1` and more than `1/2` for every target, so
  no choice of target earns more than the hash's true work.
* The exclusive `U256_MAX / t` form over-credits by up to `2×`, and its
  expected credit per hash exceeds `1`.
* Along a carrier ladder (§9.5) the root-most-beaten rule never credits more
  than the maximum over beaten targets, and a ladder of `k` carriers earns at
  most `k + 1` per hash in expectation, not `1`: a fabricated ladder buys
  per-hash credit above the true work, bounded by the chain's depth.

Hash values are uniform (`SHA256` modelled as a random oracle); expectations
are stated as sums over all `N` hash values.
-/

namespace Lattice.Work


/-- `workForTarget(_:)` (`LatticePoW/ProofOfWork.swift`), at width `N`. -/
def workForTarget (N t : Nat) : Nat :=
  if t = 0 then 0
  else if N - 1 ≤ t then 1
  else (N - 1 - t) / (t + 1) + 1

/-- `workForHash(_:)`: the same, but hash `0` saturates at `U256_MAX`. -/
def workForHash (N h : Nat) : Nat :=
  if h = 0 then N - 1
  else if N - 1 ≤ h then 1
  else (N - 1 - h) / (h + 1) + 1

/-- Bitcoin's chainwork `(~t / (t + 1)) + 1` in `N`-bit wrapping arithmetic
(`~t = N - 1 - t`; Lean's `x / 0 = 0` stands for the division by zero at
`t = N - 1`, which the implementation guards separately). -/
def bitcoinWork (N t : Nat) : Nat := ((N - 1 - t) / ((t + 1) % N) + 1) % N

/-- The rejected exclusive form `U256_MAX / t`. -/
def exclusiveWork (N t : Nat) : Nat := if t = 0 then 0 else (N - 1) / t

/-- `validateProofOfWork(nexusHash:)`: inclusive, and target `0` meets nothing. -/
def Meets (t h : Nat) : Prop := 0 < t ∧ h ≤ t

instance : DecidableRel Meets := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

/-! ## Carrier ladders (§9.1, §9.5) -/

/-- §9.5, `ChildBlockProof.verifySecuringWork`: the work of the first carrier,
root first, whose target the root hash meets (`carriers.first`), else `0`. -/
def rootMost (N : Nat) : List Nat → Nat → Nat
  | [], _ => 0
  | t :: cs, h => if Meets t h then workForTarget N t else rootMost N cs h

/-- §9.1: `contribution.work = max(workForTarget(T_rootmost_beaten),
workForTarget(target(B_terminal)))`, credited only when the terminal's own
target is met. `cs` are the carriers, root first; `tT` the terminal's target. -/
def credit (N : Nat) (cs : List Nat) (tT h : Nat) : Nat :=
  if Meets tT h then max (rootMost N cs h) (workForTarget N tT) else 0

/-- The superseded rule: the maximum over every met carrier target. -/
def maxBeaten (N : Nat) : List Nat → Nat → Nat
  | [], _ => 0
  | t :: cs, h => max (if Meets t h then workForTarget N t else 0) (maxBeaten N cs h)

def creditMax (N : Nat) (cs : List Nat) (tT h : Nat) : Nat :=
  if Meets tT h then max (maxBeaten N cs h) (workForTarget N tT) else 0

/-- `Σ_{h < n} f h`. -/
def sumBelow (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumBelow f n + f n

/-- The credit of target `t` on hash `h` if it is met, else `0`. -/
def paid (N t h : Nat) : Nat := if Meets t h then workForTarget N t else 0

/-! ## `U256` (`N = 2^256`) -/

abbrev U256Max : Nat := 2 ^ 256 - 1

end Lattice.Work
