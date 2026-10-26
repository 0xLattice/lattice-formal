/-!
# ASERT difficulty schedule (§5.5)

A transcription of Lattice's `ChainSpec.calculateAsertTarget`
(`Sources/LatticePoW/ChainSpec+Asert.swift`), operation by operation, at the
implementation's widths: `UInt64` heights and spec fields, `Int64` timestamps
and fixed-point arithmetic, `UInt256` targets.

Every value is a `Nat` or `Int` inside its Swift type's range, and every
Swift operation that can trap is checked:
* a trapping `+`, `-`, `*` or narrowing conversion that leaves its type, and a
  division by zero (or `Int64.min / -1`), is `none`;
* the `ReportingOverflow` and `clamping:` operations, which never trap, are
  spelled out with their overflow flag and partial value;
* `Int64` division truncates toward zero (`Int.tdiv`); the arithmetic shift
  `>> 16` floors (`Int` `/` by `2^16`); `& (2^16 - 1)` is the non-negative
  remainder (`Int` `%`).

So `calculateAsertTarget ... = none` means the Swift function would trap on
those inputs, and `some t` means it returns `t`.

The anchor is resolved by the caller (§5.5 "per-branch and inherited"):
`anchorOf` and `nextTarget` at the end model that over a branch of headers.
-/

namespace Lattice.Asert

/-- `UInt256.max`. -/
def max256 : Nat := 2 ^ 256 - 1
/-- `Int64.max`. -/
def int64Max : Int := 2 ^ 63 - 1

/-! ## Checked operations (Swift traps are `none`) -/

/-- A `UInt64` result: traps outside `[0, 2^64)`. -/
def u64 (x : Nat) : Option Nat := if x < 2 ^ 64 then some x else none
/-- A `UInt256` result: traps outside `[0, 2^256)`. -/
def u256 (x : Nat) : Option Nat := if x < 2 ^ 256 then some x else none
/-- An `Int64` result: traps outside `[-2^63, 2^63)`. -/
def i64 (x : Int) : Option Int := if -2 ^ 63 ≤ x ∧ x < 2 ^ 63 then some x else none
/-- `UInt64(x)` for an `Int64` `x`: traps when negative. -/
def toU64 (x : Int) : Option Nat := if 0 ≤ x then some x.toNat else none
/-- Unsigned subtraction: traps below zero. -/
def subN (a b : Nat) : Option Nat := if b ≤ a then some (a - b) else none
/-- `Int64` division: truncates toward zero; traps on a zero divisor and on
`Int64.min / -1`. -/
def sdiv64 (x y : Int) : Option Int :=
  if y = 0 ∨ (x = -2 ^ 63 ∧ y = -1) then none else some (x.tdiv y)
/-- `UInt256(1) << k`: the library shifts within 256 bits; every call here
has `k < 256`, and a larger one is treated as a trap so it cannot pass
silently. -/
def shl1 (k : Nat) : Option Nat := if k < 256 then some (2 ^ k) else none
/-- `Int64(clamping:)` of a `UInt64`. -/
def clampU64 (x : Nat) : Int := min (x : Int) int64Max
/-- `Int64` two's-complement wrap, the `partialValue` of a reporting op. -/
def wrap64 (x : Int) : Int := (x + 2 ^ 63) % 2 ^ 64 - 2 ^ 63

/-! ## The chain spec -/

/-- The two `ChainSpec` fields the schedule reads, both `UInt64`. -/
structure Spec where
  targetBlockTime : Nat
  halfLife : Nat
  deriving Repr

/-- `halfLifeMilliseconds()`: `halfLife * targetBlockTime`, saturating to
`Int64.max` on `UInt64` overflow, then clamped into `Int64`. -/
def halfLifeMilliseconds (s : Spec) : Int :=
  let p := s.halfLife * s.targetBlockTime
  let overflow := decide (2 ^ 64 ≤ p)
  if overflow then int64Max else clampU64 (p % 2 ^ 64)

/-! ## The function -/

/-- `elapsedMilliseconds(later:earlier:)`. -/
def elapsedMilliseconds (later earlier : Int) : Option Nat :=
  if later > earlier then
    if earlier ≥ 0 ∨ later < 0 then do
      let d ← i64 (later - earlier)
      toU64 d
    else do
      let e1 ← i64 (earlier + 1)
      let ne ← i64 (-e1)
      let a ← toU64 later
      let b ← toU64 ne
      let s ← u64 (a + b)
      u64 (s + 1)
  else some 0

/-- `x > UInt256.max / n ? UInt256.max : x * n`. -/
def saturatingProduct (x n : Nat) : Option Nat :=
  if x > max256 / n then pure max256 else u256 (x * n)

/-- `multiplyDividingSaturating(_:by:over:)` on `UInt256`. -/
def multiplyDividingSaturating (value numerator denominator : Nat) : Option Nat :=
  if denominator = 0 then some max256
  else if numerator = 0 then some 0
  else do
    let quotient := value / denominator
    let remainder := value % denominator
    let scaledQuotient ← saturatingProduct quotient numerator
    let scaledRemainderProduct ← saturatingProduct remainder numerator
    let scaledRemainder := scaledRemainderProduct / denominator
    let room ← subN max256 scaledRemainder
    if scaledQuotient > room then pure max256 else u256 (scaledQuotient + scaledRemainder)

def asertFixedPointBits : Int := 16
def asertFixedPointOne : Int := 65536
def asertMaximumDoublings : Int := 256
def asertCubicA : Nat := 195766423245049
def asertCubicB : Nat := 971821376
def asertCubicC : Nat := 5127
def asertCubicRounding : Nat := 2 ^ 47

/-- The cubic `a·x + b·x² + c·x³ + 2^47` in `UInt64`, left to right as
Swift evaluates it. -/
def cubic (fraction : Nat) : Option Nat := do
  let t1 ← u64 (asertCubicA * fraction)
  let bf ← u64 (asertCubicB * fraction)
  let t2 ← u64 (bf * fraction)
  let cf ← u64 (asertCubicC * fraction)
  let cff ← u64 (cf * fraction)
  let t3 ← u64 (cff * fraction)
  let s1 ← u64 (t1 + t2)
  let s2 ← u64 (s1 + t3)
  u64 (s2 + asertCubicRounding)

/-- The easing loop: `for _ in 0..<doublings { guard scaled <= ceiling else
{ return .max }; scaled = scaled * 2 }`. The early `return .max` comes back
as `max256`, which the caller's `scaled == .zero ? 1 : scaled` leaves alone. -/
def doubleLoop : Nat → Nat → Option Nat
  | 0, scaled => some scaled
  | k + 1, scaled =>
    if scaled ≤ max256 / 2 then do
      let s ← u256 (scaled * 2)
      doubleLoop k s
    else some max256

def calculateAsertTarget (spec : Spec) (anchorTarget : Nat) (anchorTimestamp : Int)
    (anchorHeight : Nat) (blockTimestamp : Int) (blockHeight : Nat) : Option Nat := do
  if ¬ blockHeight > anchorHeight then return anchorTarget
  let halfLifeMs := halfLifeMilliseconds spec
  if ¬ halfLifeMs > 0 then return anchorTarget
  if anchorTarget = 0 then return 1
  let heights ← subN blockHeight anchorHeight
  -- heights.multipliedReportingOverflow(by: targetBlockTime)
  let product := heights * spec.targetBlockTime
  let scheduled : Int := clampU64 (if 2 ^ 64 ≤ product then 2 ^ 64 - 1 else product % 2 ^ 64)
  let elapsed : Int := clampU64 (← elapsedMilliseconds blockTimestamp anchorTimestamp)
  -- elapsed.subtractingReportingOverflow(scheduled)
  let deviation := elapsed - scheduled
  let overflow := decide (deviation < -2 ^ 63 ∨ 2 ^ 63 ≤ deviation)
  let driftMilliseconds : Int :=
    if overflow then (if scheduled > 0 then -2 ^ 63 else int64Max) else wrap64 deviation
  let maximumDrift : Int := int64Max.tdiv asertFixedPointOne
  let boundedDrift := min (max driftMilliseconds (-maximumDrift)) maximumDrift
  let exponent ← sdiv64 (← i64 (boundedDrift * asertFixedPointOne)) halfLifeMs
  -- Arithmetic shift floors; the mask is the non-negative remainder.
  let doublings := exponent / 2 ^ asertFixedPointBits.toNat
  let fraction ← toU64 (exponent % asertFixedPointOne)
  let c ← cubic fraction
  let factor ← u64 (asertFixedPointOne.toNat + c / 2 ^ 48)
  if doublings < 0 then
    let halvings ← i64 (-doublings)
    if ¬ halvings < asertMaximumDoublings - asertFixedPointBits then return 1
    let shift ← u64 ((← toU64 halvings) + asertFixedPointBits.toNat)
    let scaled ← multiplyDividingSaturating anchorTarget factor (← shl1 shift)
    return if scaled = 0 then 1 else scaled
  let scaled ← multiplyDividingSaturating anchorTarget factor asertFixedPointOne.toNat
  let scaled ←
    if doublings > 0 then
      if ¬ doublings < asertMaximumDoublings then pure max256
      else doubleLoop doublings.toNat scaled
    else pure scaled
  return if scaled = 0 then 1 else scaled

/-! ## The closed form

The same function without the checks, as `calculateAsertTarget_eq` proves
(`AsertProofs.lean`). The theorems are stated on it. -/

/-- The cubic as a formula on `Nat`. -/
def cubicNat (f : Nat) : Nat :=
  asertCubicA * f + asertCubicB * f * f + asertCubicC * f * f * f + asertCubicRounding

/-- `65536 + (cubic >> 48)`: the factor `2^(f/65536)` in 16.16. -/
def factorOf (f : Nat) : Nat := 65536 + cubicNat f / 2 ^ 48

/-- `multiplyDividingSaturating` in closed form: `⌊min(v·n, ⌊v/d⌋·n·d + max)/d⌋`,
capped at the maximum. The inner `min` is where the saturated remainder
product (`remainder * numerator` past 256 bits) loses precision. -/
def mdsC (v n d : Nat) : Nat := min (min (v * n) (v / d * n * d + max256) / d) max256

/-- `Int64.max / 2^16`, the drift clamp. -/
def maximumDriftC : Int := 140737488355327

/-- `min(max(drift, -maximumDrift), maximumDrift)`. -/
def clampDrift (x : Int) : Int := min (max x (-maximumDriftC)) maximumDriftC

/-- The 16.16 exponent: the clamped drift over the half-life, truncated. -/
def exponentOf (drift halfLifeMs : Int) : Int := (clampDrift drift * 65536).tdiv halfLifeMs

/-- `max(0, B.timestamp - anchor.timestamp)`, clamped into `Int64`. -/
def elapsedOf (anchorTimestamp blockTimestamp : Int) : Int :=
  min (max (blockTimestamp - anchorTimestamp) 0) int64Max

/-- `targetBlockTime · heights`, saturating into `Int64`. -/
def scheduledOf (spec : Spec) (heights : Nat) : Int :=
  min ((heights * spec.targetBlockTime : Nat) : Int) int64Max

def driftOf (spec : Spec) (anchorTimestamp : Int) (anchorHeight : Nat) (blockTimestamp : Int)
    (blockHeight : Nat) : Int :=
  elapsedOf anchorTimestamp blockTimestamp - scheduledOf spec (blockHeight - anchorHeight)

/-- `scaled == .zero ? 1 : scaled`. -/
def atLeastOne (s : Nat) : Nat := if s = 0 then 1 else s

/-- The easing loop's result: `d` doublings of `s`, saturating at the
maximum (and the maximum outright from 256 doublings). -/
def easeOf (s : Nat) (d : Int) : Nat := if 256 ≤ d then max256 else min (s * 2 ^ d.toNat) max256

/-- The target for 16.16 exponent `e` from anchor target `A`: whole doublings
`e / 2^16` (floored) and the factor of the fraction `e % 2^16`. Hardening
divides once by `2^(16 + halvings)` and gives 1 from 240 halvings on;
easing multiplies, then doubles, saturating at the maximum. -/
def targetOf (A : Nat) (e : Int) : Nat :=
  if e / 65536 < 0 then
    if 240 ≤ -(e / 65536) then 1
    else atLeastOne (mdsC A (factorOf (e % 65536).toNat) (2 ^ ((-(e / 65536)).toNat + 16)))
  else atLeastOne (easeOf (mdsC A (factorOf (e % 65536).toNat) 65536) (e / 65536))

def asertOf (spec : Spec) (A : Nat) (anchorTimestamp : Int) (anchorHeight : Nat)
    (blockTimestamp : Int) (blockHeight : Nat) : Nat :=
  if ¬ anchorHeight < blockHeight then A
  else if ¬ 0 < halfLifeMilliseconds spec then A
  else if A = 0 then 1
  else targetOf A (exponentOf (driftOf spec anchorTimestamp anchorHeight blockTimestamp blockHeight)
    (halfLifeMilliseconds spec))

/-- Every input inside its Swift type. -/
structure InRange (spec : Spec) (anchorTarget : Nat) (anchorTimestamp : Int)
    (anchorHeight : Nat) (blockTimestamp : Int) (blockHeight : Nat) : Prop where
  targetBlockTime : spec.targetBlockTime < 2 ^ 64
  halfLife : spec.halfLife < 2 ^ 64
  anchorTarget : anchorTarget < 2 ^ 256
  anchorTimestampLo : -2 ^ 63 ≤ anchorTimestamp
  anchorTimestampHi : anchorTimestamp < 2 ^ 63
  anchorHeight : anchorHeight < 2 ^ 64
  blockTimestampLo : -2 ^ 63 ≤ blockTimestamp
  blockTimestampHi : blockTimestamp < 2 ^ 63
  blockHeight : blockHeight < 2 ^ 64

/-! ## The anchor (§5.5 "per-branch and inherited") -/

/-- The header fields the schedule reads. -/
structure Header where
  height : Nat
  timestamp : Int
  target : Nat
  deriving Repr, DecidableEq

/-- A branch, newest block first: the block, then its parent, and so on. A
block at height 1 anchors itself; every other block inherits its parent's
anchor (`immediateDifficultyAnchor`, `resolveDifficultyAnchor`). -/
def anchorOf : List Header → Option Header
  | [] => none
  | b :: ancestors => if b.height = 1 then some b else anchorOf ancestors

/-- `validateNextTarget`: the block's `nextTarget` is the schedule at its own
timestamp and height, from its branch's anchor. -/
def nextTarget (spec : Spec) : List Header → Option Nat
  | [] => none
  | b :: ancestors => do
    let a ← anchorOf (b :: ancestors)
    calculateAsertTarget spec a.target a.timestamp a.height b.timestamp b.height

end Lattice.Asert
