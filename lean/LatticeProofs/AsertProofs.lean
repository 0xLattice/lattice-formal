import LatticeProofs.Asert

/-!
# ASERT: the implementation's function, proven (§5.5)

`calculateAsertTarget_eq` reduces the transcription in `Asert.lean` to a
closed form (`asertOf`): it never traps on in-range inputs, and it returns
`targetOf A e` for the 16.16 exponent `e` of the drift. The §5.5 claims are
then theorems about that closed form.
-/

namespace Lattice.Asert

/-! ## Arithmetic -/

theorem u64_some {x : Nat} (h : x < 2 ^ 64) : u64 x = some x := by simp [u64, h]
theorem u256_some {x : Nat} (h : x < 2 ^ 256) : u256 x = some x := by simp [u256, h]

theorem cubic_eq {f : Nat} (hf : f < 65536) : cubic f = some (cubicNat f) := by
  have h : f ≤ 65535 := by omega
  have e1 : asertCubicA * f ≤ asertCubicA * 65535 := Nat.mul_le_mul_left _ h
  have e2 : asertCubicB * f ≤ asertCubicB * 65535 := Nat.mul_le_mul_left _ h
  have e3 : asertCubicB * f * f ≤ asertCubicB * 65535 * 65535 := Nat.mul_le_mul e2 h
  have e4 : asertCubicC * f ≤ asertCubicC * 65535 := Nat.mul_le_mul_left _ h
  have e5 : asertCubicC * f * f ≤ asertCubicC * 65535 * 65535 := Nat.mul_le_mul e4 h
  have e6 : asertCubicC * f * f * f ≤ asertCubicC * 65535 * 65535 * 65535 := Nat.mul_le_mul e5 h
  simp only [asertCubicA, asertCubicB, asertCubicC, asertCubicRounding] at e1 e2 e3 e4 e5 e6
  simp only [cubic, cubicNat, asertCubicA, asertCubicB, asertCubicC, asertCubicRounding]
  simp only [Option.bind_eq_bind]
  repeat rw [u64_some (by omega), Option.bind_some]
  rw [u64_some (by omega)]

theorem max256_pos : 0 < max256 := by decide

theorem mds_eq {v n d : Nat} (hn : 0 < n) (hd : 0 < d) :
    multiplyDividingSaturating v n d = some (mdsC v n d) := by
  have hvn : v * n = v / d * n * d + v % d * n := by
    have h := Nat.div_add_mod v d
    calc v * n = (d * (v / d) + v % d) * n := by rw [h]
      _ = _ := by rw [Nat.add_mul, Nat.mul_comm d, Nat.mul_right_comm]
  have key : min (v * n) (v / d * n * d + max256) = v / d * n * d + min (v % d * n) max256 := by
    omega
  have hdiv : (v / d * n * d + min (v % d * n) max256) / d
      = v / d * n + min (v % d * n) max256 / d := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hd, Nat.add_comm]
  unfold mdsC
  rw [key, hdiv]
  unfold multiplyDividingSaturating
  rw [if_neg (by omega), if_neg (by omega)]
  have hsat : ∀ x, saturatingProduct x n = some (min (x * n) max256) := by
    intro x
    unfold saturatingProduct
    by_cases h : x > max256 / n
    · have := (Nat.div_lt_iff_lt_mul hn).1 h
      rw [if_pos h]; simp only [pure]; congr 1; omega
    · have := (Nat.le_div_iff_mul_le hn).1 (Nat.le_of_not_gt h)
      rw [if_neg h, u256_some (by unfold max256 at this; omega)]; congr 1; omega
  have hsr : min (v % d * n) max256 / d ≤ max256 :=
    Nat.le_trans (Nat.div_le_self _ _) (Nat.min_le_right _ _)
  simp only [Option.bind_eq_bind, hsat, Option.bind_some, subN, if_pos hsr]
  generalize min (v % d * n) max256 / d = sr at *
  generalize v / d * n = qn at *
  by_cases h2 : min qn max256 > max256 - sr
  · rw [if_pos h2]; simp only [pure]; congr 1; omega
  · rw [if_neg h2, u256_some (by unfold max256 at *; omega)]; congr 1; omega


theorem doubleLoop_eq : ∀ (k s : Nat), s ≤ max256 →
    doubleLoop k s = some (min (s * 2 ^ k) max256)
  | 0, s, hs => by simp [doubleLoop]; omega
  | k + 1, s, hs => by
    unfold doubleLoop
    by_cases h : s ≤ max256 / 2
    · rw [if_pos h, u256_some (by unfold max256 at h; omega), Option.bind_eq_bind,
        Option.bind_some, doubleLoop_eq k (s * 2) (by unfold max256 at h ⊢; omega)]
      rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm 2]
    · rw [if_neg h]
      have h2 : 2 ≤ 2 ^ (k + 1) := Nat.le_trans (by decide) (Nat.pow_le_pow_right (by decide) (Nat.succ_le_succ (Nat.zero_le k)))
      have : s * 2 ≤ s * 2 ^ (k + 1) := Nat.mul_le_mul_left _ h2
      congr 1; unfold max256 at *; omega

theorem tdiv_eq (a b : Int) :
    a.tdiv b = if 0 ≤ a then a / b else -((-a) / b) := by
  by_cases ha : 0 ≤ a
  · rw [if_pos ha, Int.tdiv_eq_ediv_of_nonneg ha]
  · rw [if_neg ha, ← Int.tdiv_eq_ediv_of_nonneg (by omega), Int.neg_tdiv, Int.neg_neg]

theorem tdiv_mono {a₁ a₂ b : Int} (hb : 0 < b) (h : a₁ ≤ a₂) : a₁.tdiv b ≤ a₂.tdiv b := by
  rw [tdiv_eq _ _, tdiv_eq _ _]
  by_cases h1 : 0 ≤ a₁
  · rw [if_pos h1, if_pos (by omega)]; exact Int.ediv_le_ediv hb h
  · rw [if_neg h1]
    by_cases h2 : 0 ≤ a₂
    · rw [if_pos h2]
      have := Int.ediv_nonneg (by omega : 0 ≤ -a₁) (Int.le_of_lt hb)
      have := Int.ediv_nonneg h2 (Int.le_of_lt hb)
      omega
    · rw [if_neg h2]
      have := Int.ediv_le_ediv hb (by omega : -a₂ ≤ -a₁)
      omega

theorem tdiv_bound {a b : Int} (hb : 0 < b) : -(a.natAbs : Int) ≤ a.tdiv b ∧ a.tdiv b ≤ a.natAbs := by
  rw [tdiv_eq _ _]
  by_cases h : 0 ≤ a
  · rw [if_pos h]
    have := Int.ediv_nonneg h (Int.le_of_lt hb)
    have := Int.ediv_le_self b h
    omega
  · rw [if_neg h]
    have := Int.ediv_nonneg (by omega : 0 ≤ -a) (Int.le_of_lt hb)
    have := Int.ediv_le_self b (by omega : 0 ≤ -a)
    omega

theorem elapsed_eq {a b : Int} (ha : -2 ^ 63 ≤ a) (ha' : a < 2 ^ 63) (hb' : b < 2 ^ 63) : elapsedMilliseconds b a = some (max (b - a) 0).toNat := by
  unfold elapsedMilliseconds
  by_cases h : b > a
  · rw [if_pos h]
    by_cases h2 : a ≥ 0 ∨ b < 0
    · rw [if_pos h2]
      simp only [i64, toU64, Option.bind_eq_bind]
      rw [if_pos (by omega), Option.bind_some, if_pos (by omega)]
      congr 1; omega
    · rw [if_neg h2]
      simp only [i64, toU64, u64, Option.bind_eq_bind]
      rw [if_pos (by omega), Option.bind_some, if_pos (by omega), Option.bind_some,
        if_pos (by omega), Option.bind_some, if_pos (by omega), Option.bind_some,
        if_pos (by omega), Option.bind_some, if_pos (by omega)]
      congr 1; omega
  · rw [if_neg h]; congr 1; omega


theorem cubicNat_lt {f : Nat} (hf : f < 65536) : cubicNat f < 2 ^ 64 := by
  have h : f ≤ 65535 := by omega
  have e1 : asertCubicA * f ≤ asertCubicA * 65535 := Nat.mul_le_mul_left _ h
  have e3 : asertCubicB * f * f ≤ asertCubicB * 65535 * 65535 :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ h) h
  have e6 : asertCubicC * f * f * f ≤ asertCubicC * 65535 * 65535 * 65535 :=
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _ h) h) h
  simp only [asertCubicA, asertCubicB, asertCubicC] at e1 e3 e6
  simp only [cubicNat, asertCubicA, asertCubicB, asertCubicC, asertCubicRounding]
  omega

theorem halfLife_le (spec : Spec) : halfLifeMilliseconds spec ≤ int64Max := by
  simp only [halfLifeMilliseconds, clampU64]; split <;> omega

theorem mdsC_le (v n d : Nat) : mdsC v n d ≤ max256 := Nat.min_le_right _ _

theorem factorOf_pos (f : Nat) : 0 < factorOf f := by unfold factorOf; omega

/-- The implementation never traps on in-range inputs, and returns the
closed form. -/
theorem calculateAsertTarget_eq {spec : Spec} {A : Nat} {at_ bt : Int} {ah bh : Nat}
    (hr : InRange spec A at_ ah bt bh) :
    calculateAsertTarget spec A at_ ah bt bh = some (asertOf spec A at_ ah bt bh) := by
  have hHL := halfLife_le spec
  unfold calculateAsertTarget asertOf
  by_cases h1 : ¬ ah < bh
  · rw [if_pos (by omega), if_pos h1]; rfl
  rw [if_neg (by omega), if_neg h1]
  by_cases h2 : ¬ 0 < halfLifeMilliseconds spec
  · simp only []; rw [if_pos (by omega), if_pos h2]; rfl
  simp only []
  rw [if_neg (by omega), if_neg h2]
  by_cases h3 : A = 0
  · rw [if_pos h3, if_pos h3]; rfl
  rw [if_neg h3, if_neg h3]
  have hr' := hr
  obtain ⟨hT, hH, hA, hat, hat', hah, hbt, hbt', hbh⟩ := hr'
  simp only [Option.bind_eq_bind]
  rw [show subN bh ah = some (bh - ah) by simp [subN]; omega, Option.bind_some,
    elapsed_eq hat hat' hbt', Option.bind_some]
  have hsch : clampU64 (if 2 ^ 64 ≤ (bh - ah) * spec.targetBlockTime then 2 ^ 64 - 1
      else (bh - ah) * spec.targetBlockTime % 2 ^ 64) = scheduledOf spec (bh - ah) := by
    unfold scheduledOf clampU64 int64Max
    generalize (bh - ah) * spec.targetBlockTime = P
    split <;> omega
  have hel : clampU64 (max (bt - at_) 0).toNat = elapsedOf at_ bt := by
    unfold elapsedOf clampU64 int64Max; omega
  rw [hsch, hel]
  have hE : 0 ≤ elapsedOf at_ bt ∧ elapsedOf at_ bt ≤ int64Max := by
    unfold elapsedOf int64Max; omega
  have hS : 0 ≤ scheduledOf spec (bh - ah) ∧ scheduledOf spec (bh - ah) ≤ int64Max := by
    unfold scheduledOf int64Max; omega
  have hno : decide (elapsedOf at_ bt - scheduledOf spec (bh - ah) < -2 ^ 63 ∨
      2 ^ 63 ≤ elapsedOf at_ bt - scheduledOf spec (bh - ah)) = false := by
    unfold int64Max at hE hS; simp only [decide_eq_false_iff_not]; omega
  have hwrap : wrap64 (elapsedOf at_ bt - scheduledOf spec (bh - ah))
      = driftOf spec at_ ah bt bh := by
    unfold driftOf wrap64; unfold int64Max at hE hS; omega
  have hmax : int64Max.tdiv asertFixedPointOne = maximumDriftC := by decide
  rw [hno, hwrap, hmax]
  simp only [Bool.false_eq_true, if_false]
  generalize hD : driftOf spec at_ ah bt bh = D
  generalize hHLv : halfLifeMilliseconds spec = HL at h2 hHL
  have hc : -maximumDriftC ≤ clampDrift D ∧ clampDrift D ≤ maximumDriftC := by
    unfold clampDrift maximumDriftC; omega
  have hone : asertFixedPointOne = 65536 := rfl
  rw [hone, show min (max D (-maximumDriftC)) maximumDriftC = clampDrift D from rfl]
  rw [show i64 (clampDrift D * 65536) = some (clampDrift D * 65536) by
    unfold i64; unfold maximumDriftC at hc; rw [if_pos (by omega)], Option.bind_some]
  rw [show sdiv64 (clampDrift D * 65536) HL = some (exponentOf D HL) by
    unfold sdiv64 exponentOf; rw [if_neg (by omega)], Option.bind_some]
  have he := tdiv_bound (a := clampDrift D * 65536) (b := HL) (by omega)
  rw [show (clampDrift D * 65536).tdiv HL = exponentOf D HL from rfl] at he
  generalize exponentOf D HL = e at he
  have he1 : -(2 ^ 63 : Int) < e ∧ e < 2 ^ 63 := by unfold maximumDriftC at hc; omega
  rw [show toU64 (e % 65536) = some (e % 65536).toNat by
    unfold toU64; rw [if_pos (by omega)], Option.bind_some]
  have hf : (e % 65536).toNat < 65536 := by omega
  rw [cubic_eq hf, Option.bind_some]
  have hcl := cubicNat_lt hf
  rw [show u64 (Int.toNat 65536 + cubicNat (e % 65536).toNat / 2 ^ 48)
      = some (factorOf (e % 65536).toNat) by
    unfold u64 factorOf; rw [if_pos (by omega)]; rfl, Option.bind_some]
  have hbits : (2 : Int) ^ asertFixedPointBits.toNat = 65536 := rfl
  rw [hbits]
  unfold targetOf atLeastOne easeOf
  have hF := factorOf_pos (e % 65536).toNat
  generalize factorOf (e % 65536).toNat = F at hF
  by_cases hd : e / 65536 < 0
  · rw [if_pos hd, if_pos hd]
    rw [show i64 (-(e / 65536)) = some (-(e / 65536)) by
      unfold i64; rw [if_pos (by omega)], Option.bind_some]
    have h240 : asertMaximumDoublings - asertFixedPointBits = 240 := rfl
    rw [h240]
    by_cases hh : 240 ≤ -(e / 65536)
    · rw [if_pos (by omega), if_pos hh]; rfl
    rw [if_neg (by omega), if_neg hh]
    rw [show toU64 (-(e / 65536)) = some (-(e / 65536)).toNat by
      unfold toU64; rw [if_pos (by omega)], Option.bind_some]
    rw [show u64 ((-(e / 65536)).toNat + asertFixedPointBits.toNat)
        = some ((-(e / 65536)).toNat + 16) by
      unfold u64; rw [if_pos (by unfold asertFixedPointBits; omega)]; rfl, Option.bind_some]
    rw [show shl1 ((-(e / 65536)).toNat + 16) = some (2 ^ ((-(e / 65536)).toNat + 16)) by
      unfold shl1; rw [if_pos (by omega)], Option.bind_some]
    rw [mds_eq hF (Nat.two_pow_pos _), Option.bind_some]
    rfl
  · rw [if_neg hd, if_neg hd]
    rw [show Int.toNat 65536 = 65536 from rfl, mds_eq hF (by decide), Option.bind_some]
    have hle := mdsC_le A F 65536
    generalize mdsC A F 65536 = s at hle
    have h256 : asertMaximumDoublings = 256 := rfl
    rw [h256]
    by_cases hp : e / 65536 > 0
    · rw [if_pos hp]
      by_cases hb : ¬ e / 65536 < 256
      · rw [if_pos hb, if_pos (show (256 : Int) ≤ e / 65536 by omega)]; rfl
      · rw [if_neg hb, if_neg (show ¬ (256 : Int) ≤ e / 65536 by omega), doubleLoop_eq _ _ hle,
          Option.bind_some]; rfl
    · rw [if_neg hp, if_neg (show ¬ (256 : Int) ≤ e / 65536 by omega)]
      have : (e / 65536).toNat = 0 := by omega
      rw [this, Nat.pow_zero, Nat.mul_one, Nat.min_eq_left hle]; rfl


/-- The implementation never traps on inputs inside their Swift types. -/
theorem never_traps {spec : Spec} {A : Nat} {at_ bt : Int} {ah bh : Nat}
    (hr : InRange spec A at_ ah bt bh) : (calculateAsertTarget spec A at_ ah bt bh).isSome := by
  rw [calculateAsertTarget_eq hr]; rfl

/-! ## Facts about the pieces -/

theorem atLeastOne_mono {a b : Nat} (h : a ≤ b) : atLeastOne a ≤ atLeastOne b := by
  unfold atLeastOne; split <;> split <;> omega

theorem cubicNat_mono {f g : Nat} (h : f ≤ g) : cubicNat f ≤ cubicNat g := by
  unfold cubicNat
  have e1 : asertCubicA * f ≤ asertCubicA * g := Nat.mul_le_mul_left _ h
  have e2 : asertCubicB * f * f ≤ asertCubicB * g * g := Nat.mul_le_mul (Nat.mul_le_mul_left _ h) h
  have e3 : asertCubicC * f * f * f ≤ asertCubicC * g * g * g :=
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _ h) h) h
  omega

theorem factorOf_mono {f g : Nat} (h : f ≤ g) : factorOf f ≤ factorOf g := by
  unfold factorOf; have := Nat.div_le_div_right (c := 2 ^ 48) (cubicNat_mono h); omega

theorem factorOf_zero : factorOf 0 = 65536 := by decide
theorem factorOf_last : factorOf 65535 = 131071 := by decide

theorem mdsC_mono {v n₁ n₂ d : Nat} (h : n₁ ≤ n₂) : mdsC v n₁ d ≤ mdsC v n₂ d := by
  unfold mdsC
  have e1 : v * n₁ ≤ v * n₂ := Nat.mul_le_mul_left _ h
  have e2 : v / d * n₁ * d ≤ v / d * n₂ * d := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h)
  have : min (v * n₁) (v / d * n₁ * d + max256) ≤ min (v * n₂) (v / d * n₂ * d + max256) := by
    omega
  have := Nat.div_le_div_right (c := d) this
  omega

theorem mdsC_le_div (v n d : Nat) : mdsC v n d ≤ v * n / d := by
  unfold mdsC
  have := Nat.div_le_div_right (c := d) (Nat.min_le_left (v * n) (v / d * n * d + max256))
  omega

/-- When the remainder product fits, the division is exact: `⌊v·n/d⌋`. -/
theorem mdsC_exact {v n d : Nat} (h : v % d * n ≤ max256) :
    mdsC v n d = min (v * n / d) max256 := by
  unfold mdsC
  have hvn : v * n = v / d * n * d + v % d * n := by
    have h := Nat.div_add_mod v d
    calc v * n = (d * (v / d) + v % d) * n := by rw [h]
      _ = _ := by rw [Nat.add_mul, Nat.mul_comm d, Nat.mul_right_comm]
  rw [show min (v * n) (v / d * n * d + max256) = v * n by omega]

/-- Halving the divisor and the numerator never lowers the result: the
step across a whole halving. -/
theorem mdsC_double (v n d : Nat) : mdsC v (2 * n) (2 * d) ≤ mdsC v n d := by
  unfold mdsC
  have hq : 2 * (v / (2 * d)) ≤ v / d := by
    rw [Nat.mul_comm 2 d, ← Nat.div_div_eq_div_mul]; omega
  have hq' : 2 * (v / (2 * d)) * n * d ≤ v / d * n * d :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hq)
  have e1 : v / (2 * d) * (2 * n) * (2 * d) = 2 * (2 * (v / (2 * d)) * n * d) := by
    simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have e2 : v * (2 * n) = 2 * (v * n) := by
    simp only [Nat.mul_assoc, Nat.mul_comm]
  have : min (v * (2 * n)) (v / (2 * d) * (2 * n) * (2 * d) + max256)
      ≤ 2 * min (v * n) (v / d * n * d + max256) := by
    rw [e1, e2]; omega
  have h2 := Nat.div_le_div_right (c := 2 * d) this
  rw [Nat.mul_div_mul_left _ _ (by decide : 0 < 2)] at h2
  omega

theorem atLeastOne_eq_max (s : Nat) : atLeastOne s = max 1 s := by
  unfold atLeastOne; split <;> omega

theorem max256_lt : max256 < 2 ^ 256 := Nat.sub_lt (Nat.two_pow_pos _) (by decide)

theorem atLeastOne_pos (s : Nat) : 1 ≤ atLeastOne s := by unfold atLeastOne; split <;> omega

theorem atLeastOne_le {s m : Nat} (h : s ≤ m) (hm : 1 ≤ m) : atLeastOne s ≤ m := by
  unfold atLeastOne; split <;> omega

theorem atLeastOne_of_pos {s : Nat} (h : 0 < s) : atLeastOne s = s := by
  unfold atLeastOne; split <;> omega

theorem easeOf_le (s : Nat) (d : Int) : easeOf s d ≤ max256 := by
  unfold easeOf; split <;> omega

theorem easeOf_mono {s₁ s₂ : Nat} (d : Int) (h : s₁ ≤ s₂) : easeOf s₁ d ≤ easeOf s₂ d := by
  unfold easeOf; split
  · omega
  · have := Nat.mul_le_mul_right (2 ^ d.toNat) h; omega

theorem targetOf_le (A : Nat) (e : Int) : targetOf A e ≤ max256 := by
  have := max256_pos
  unfold targetOf; split
  · split
    · omega
    · exact atLeastOne_le (mdsC_le _ _ _) this
  · exact atLeastOne_le (easeOf_le _ _) this

theorem targetOf_pos (A : Nat) (e : Int) : 1 ≤ targetOf A e := by
  unfold targetOf; split
  · split
    · omega
    · exact atLeastOne_pos _
  · exact atLeastOne_pos _

/-- At exponent 0 the target is the anchor's. -/
theorem mdsC_unit {A : Nat} (hA : A ≤ max256) : mdsC A 65536 65536 = A := by
  rw [mdsC_exact (by have := Nat.mod_lt A (show 0 < 65536 by decide); unfold max256; omega),
    Nat.mul_div_cancel _ (by decide)]
  exact Nat.min_eq_left hA

theorem targetOf_zero {A : Nat} (hA : 0 < A) (hA' : A ≤ max256) : targetOf A 0 = A := by
  unfold targetOf
  rw [if_neg (by decide)]
  rw [show ((0 : Int) % 65536).toNat = 0 from rfl, factorOf_zero, mdsC_unit hA']
  unfold easeOf
  rw [if_neg (by decide), show ((0 : Int) / 65536).toNat = 0 from rfl, Nat.pow_zero, Nat.mul_one,
    Nat.min_eq_left hA', atLeastOne_of_pos hA]

/-- One step of the exponent never lowers the target. -/
theorem targetOf_step {A : Nat} (hA : 0 < A) (hA' : A ≤ max256) (e : Int) :
    targetOf A e ≤ targetOf A (e + 1) := by
  by_cases hf : e % 65536 < 65535
  · -- same whole part, the fraction one higher
    have hd : (e + 1) / 65536 = e / 65536 := by omega
    have hm : ((e + 1) % 65536).toNat = (e % 65536).toNat + 1 := by omega
    have hF := factorOf_mono (Nat.le_succ (e % 65536).toNat)
    unfold targetOf
    rw [hd, hm]
    split
    · split
      · omega
      · exact atLeastOne_mono (mdsC_mono hF)
    · exact atLeastOne_mono (easeOf_mono _ (mdsC_mono hF))
  · -- the fraction wraps from 65535 to 0: one more whole doubling
    have hd : (e + 1) / 65536 = e / 65536 + 1 := by omega
    have hm0 : ((e + 1) % 65536).toNat = 0 := by omega
    have hm : (e % 65536).toNat = 65535 := by omega
    have hpos := targetOf_pos A (e + 1)
    have hle := targetOf_le A e
    by_cases hneg : e / 65536 < 0
    · by_cases hm1 : e / 65536 = -1
      · -- the last halving: e + 1 = 0
        have he : e + 1 = 0 := by omega
        rw [he, targetOf_zero hA hA']
        unfold targetOf
        rw [hm, factorOf_last, hm1, if_pos (by decide), if_neg (by decide)]
        have := mdsC_le_div A 131071 (2 ^ ((-(-1 : Int)).toNat + 16))
        have h2 : A * 131071 / 2 ^ ((-(-1 : Int)).toNat + 16) ≤ A := by
          rw [show 2 ^ ((-(-1 : Int)).toNat + 16) = 131072 from rfl,
            Nat.div_le_iff_le_mul_add_pred (by decide)]; omega
        exact atLeastOne_le (Nat.le_trans this h2) hA
      · -- a deeper halving: 131071 over 2^(h+16) against 65536 over 2^(h+15)
        by_cases h240 : 240 ≤ -(e / 65536)
        · have : targetOf A e = 1 := by
            unfold targetOf; rw [if_pos hneg, if_pos h240]
          omega
        unfold targetOf
        rw [hd, hm, hm0, factorOf_last, factorOf_zero, if_pos hneg, if_neg h240,
          if_pos (show e / 65536 + 1 < 0 by omega), if_neg (show ¬ 240 ≤ -(e / 65536 + 1) by omega)]
        apply atLeastOne_mono
        have hk : (-(e / 65536)).toNat + 16 = ((-(e / 65536 + 1)).toNat + 16) + 1 := by omega
        rw [hk, Nat.pow_succ, Nat.mul_comm _ 2]
        exact Nat.le_trans (mdsC_mono (by decide : 131071 ≤ 2 * 65536))
          (mdsC_double A 65536 _)
    · -- easing: 131071 then 2^d against 65536 then 2^(d+1)
      unfold targetOf
      rw [hd, hm, hm0, factorOf_last, factorOf_zero, if_neg hneg,
        if_neg (show ¬ e / 65536 + 1 < 0 by omega), mdsC_unit hA']
      apply atLeastOne_mono
      unfold easeOf
      by_cases h256 : 256 ≤ e / 65536 + 1
      · rw [if_pos h256]; split <;> omega
      rw [if_neg h256, if_neg (show ¬ 256 ≤ e / 65536 by omega)]
      have h1 := mdsC_le_div A 131071 65536
      have h2 : A * 131071 / 65536 ≤ 2 * A := by
        rw [Nat.div_le_iff_le_mul_add_pred (by decide)]; omega
      have hk : (e / 65536 + 1).toNat = (e / 65536).toNat + 1 := by omega
      rw [hk, Nat.pow_succ]
      have := Nat.mul_le_mul_right (2 ^ (e / 65536).toNat) (Nat.le_trans h1 h2)
      have e3 : 2 * A * 2 ^ (e / 65536).toNat = A * (2 ^ (e / 65536).toNat * 2) := by
        simp only [Nat.mul_assoc, Nat.mul_comm]
      omega


theorem targetOf_mono {A : Nat} (hA : 0 < A) (hA' : A ≤ max256) {e₁ e₂ : Int} (h : e₁ ≤ e₂) :
    targetOf A e₁ ≤ targetOf A e₂ := by
  obtain ⟨k, hk⟩ : ∃ k : Nat, e₂ = e₁ + k := ⟨(e₂ - e₁).toNat, by omega⟩
  subst hk
  induction k with
  | zero => simp
  | succ k ih =>
    have := targetOf_step hA hA' (e₁ + k)
    rw [show e₁ + ((k + 1 : Nat) : Int) = e₁ + k + 1 by omega]
    exact Nat.le_trans (ih (by omega)) this

theorem clampDrift_mono {x y : Int} (h : x ≤ y) : clampDrift x ≤ clampDrift y := by
  unfold clampDrift; omega

theorem exponentOf_mono {D₁ D₂ HL : Int} (hHL : 0 < HL) (h : D₁ ≤ D₂) :
    exponentOf D₁ HL ≤ exponentOf D₂ HL := by
  unfold exponentOf
  have := clampDrift_mono h
  exact tdiv_mono hHL (by omega)

theorem elapsedOf_mono {at_ b₁ b₂ : Int} (h : b₁ ≤ b₂) : elapsedOf at_ b₁ ≤ elapsedOf at_ b₂ := by
  unfold elapsedOf; omega

theorem scheduledOf_mono (spec : Spec) {h₁ h₂ : Nat} (h : h₁ ≤ h₂) :
    scheduledOf spec h₁ ≤ scheduledOf spec h₂ := by
  unfold scheduledOf
  have := Nat.mul_le_mul_right spec.targetBlockTime h
  omega

/-! ## §5.5 claims -/

/-- "The result saturates at both ends: it never exceeds the maximum target." -/
theorem result_le_max {spec : Spec} {A : Nat} {at_ bt : Int} {ah bh : Nat}
    (hr : InRange spec A at_ ah bt bh) : asertOf spec A at_ ah bt bh ≤ max256 := by
  have ht := targetOf_le A
  have hA := hr.anchorTarget
  have := max256_pos
  unfold asertOf
  split
  · unfold max256; omega
  split
  · unfold max256; omega
  split
  · omega
  exact ht _

/-- "... and never reaches zero": true exactly when the anchor target is
nonzero or a schedule runs (a height above the anchor and a positive
half-life). The validator's anchor target is a proof-of-work target, which
is nonzero (`ProofOfWork`: `target > .zero`). -/
theorem result_pos {spec : Spec} {A : Nat} {at_ bt : Int} {ah bh : Nat}
    (h : 0 < A ∨ (ah < bh ∧ 0 < halfLifeMilliseconds spec)) :
    0 < asertOf spec A at_ ah bt bh := by
  have ht := targetOf_pos A
  unfold asertOf
  split
  · omega
  split
  · omega
  split
  · omega
  exact ht _

/-- The caveat is real: a zero anchor at its own height returns zero. -/
theorem result_zero_unscheduled : asertOf ⟨600000, 120⟩ 0 0 1 0 1 = 0 := by decide

/-- "Exactly on schedule holds the anchor's target at any depth." -/
theorem on_schedule {spec : Spec} {A : Nat} {at_ bt : Int} {ah bh : Nat}
    (hA : 0 < A) (hA' : A ≤ max256)
    (hsched : (((bh - ah) * spec.targetBlockTime : Nat) : Int) ≤ int64Max)
    (hon : bt - at_ = (((bh - ah) * spec.targetBlockTime : Nat) : Int)) :
    asertOf spec A at_ ah bt bh = A := by
  unfold asertOf
  split
  · rfl
  split
  · rfl
  rw [if_neg (by omega)]
  have hd : driftOf spec at_ ah bt bh = 0 := by
    unfold driftOf elapsedOf scheduledOf; omega
  have hc : clampDrift 0 = 0 := by unfold clampDrift maximumDriftC; omega
  rw [hd, show exponentOf 0 (halfLifeMilliseconds spec) = 0 by
    unfold exponentOf; rw [hc, Int.zero_mul, Int.zero_tdiv]]
  exact targetOf_zero hA hA'

/-- "Behind schedule eases; ahead hardens": a later timestamp never gives a
harder target, so moving a timestamp backwards never eases. -/
theorem mono_timestamp {spec : Spec} {A : Nat} {at_ b₁ b₂ : Int} {ah bh : Nat}
    (hA' : A ≤ max256) (h : b₁ ≤ b₂) :
    asertOf spec A at_ ah b₁ bh ≤ asertOf spec A at_ ah b₂ bh := by
  unfold asertOf
  by_cases h0 : ¬ ah < bh
  · rw [if_pos h0, if_pos h0]; exact Nat.le_refl _
  rw [if_neg h0, if_neg h0]
  by_cases hHL : ¬ 0 < halfLifeMilliseconds spec
  · rw [if_pos hHL, if_pos hHL]; exact Nat.le_refl _
  rw [if_neg hHL, if_neg hHL]
  simp only [Decidable.not_not] at hHL
  by_cases hA : A = 0
  · rw [if_pos hA, if_pos hA]; exact Nat.le_refl _
  rw [if_neg hA, if_neg hA]
  apply targetOf_mono (by omega) hA'
  apply exponentOf_mono (by omega)
  unfold driftOf
  have := elapsedOf_mono (at_ := at_) h
  omega

/-- More blocks since the anchor never give an easier target, for heights
above the anchor. -/
theorem mono_height {spec : Spec} {A : Nat} {at_ bt : Int} {ah h₁ h₂ : Nat}
    (hA' : A ≤ max256) (h₀ : ah < h₁) (h : h₁ ≤ h₂) :
    asertOf spec A at_ ah bt h₂ ≤ asertOf spec A at_ ah bt h₁ := by
  unfold asertOf
  rw [if_neg (show ¬ ¬ ah < h₂ by omega), if_neg (show ¬ ¬ ah < h₁ by omega)]
  by_cases hHL : ¬ 0 < halfLifeMilliseconds spec
  · rw [if_pos hHL, if_pos hHL]; exact Nat.le_refl _
  rw [if_neg hHL, if_neg hHL]
  simp only [Decidable.not_not] at hHL
  by_cases hA : A = 0
  · rw [if_pos hA, if_pos hA]; exact Nat.le_refl _
  rw [if_neg hA, if_neg hA]
  apply targetOf_mono (by omega) hA'
  apply exponentOf_mono (by omega)
  unfold driftOf
  have := scheduledOf_mono spec (show h₁ - ah ≤ h₂ - ah by omega)
  omega

/-- At the anchor's own height there is no schedule, so the first block
above it can be easier than the anchor: `mono_height` needs `ah < h₁`. -/
theorem mono_height_needs_schedule :
    asertOf ⟨600000, 120⟩ (2 ^ 200) 0 1 (100 * 72000000) 1 = 2 ^ 200 ∧
    2 ^ 200 < asertOf ⟨600000, 120⟩ (2 ^ 200) 0 1 (100 * 72000000) 2 := by decide


/-! ### One half-life of drift is one doubling -/

/-- Whole half-lives of drift give a whole exponent, while the drift is
inside the clamp. -/
theorem exponentOf_whole {k HL : Int} (hHL : 0 < HL) (hk : (k * HL).natAbs ≤ maximumDriftC) :
    exponentOf (k * HL) HL = 65536 * k := by
  unfold exponentOf
  have hc : clampDrift (k * HL) = k * HL := by unfold clampDrift; omega
  rw [hc, show k * HL * 65536 = 65536 * k * HL by
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm], tdiv_eq _ _]
  split
  · exact Int.mul_ediv_cancel _ (by omega)
  · rw [show -(65536 * k * HL) = (-(65536 * k)) * HL by
      simp only [Int.neg_mul], Int.mul_ediv_cancel _ (by omega)]
    omega

/-- Easing by `k` whole doublings is exact: `A · 2^k`, saturating. -/
theorem targetOf_ease_whole {A : Nat} (hA : 0 < A) (hA' : A ≤ max256) (k : Nat) :
    targetOf A (65536 * k) = min (A * 2 ^ k) max256 := by
  unfold targetOf
  rw [if_neg (by omega), show ((65536 * (k : Int)) % 65536).toNat = 0 by omega, factorOf_zero,
    mdsC_unit hA', show (65536 * (k : Int)) / 65536 = k by omega]
  unfold easeOf
  have hp : 1 ≤ A * 2 ^ k := Nat.mul_le_mul hA (Nat.one_le_two_pow)
  split
  · rename_i h
    have : 2 ^ 256 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
    have : 2 ^ k ≤ A * 2 ^ k := Nat.le_mul_of_pos_left _ hA
    rw [Nat.min_eq_right (by unfold max256; omega)]
    exact atLeastOne_of_pos max256_pos
  · rw [show ((k : Int)).toNat = k by omega]
    exact atLeastOne_of_pos (by have := max256_pos; omega)

/-- Hardening by `k ≤ 224` whole halvings is exact: `⌊A / 2^k⌋`, and 1
where that is 0. -/
theorem targetOf_harden_whole {A : Nat} (hA' : A ≤ max256) {k : Nat} (hk : 1 ≤ k)
    (hk' : k ≤ 224) : targetOf A (-(65536 * k)) = max 1 (A / 2 ^ k) := by
  unfold targetOf
  rw [show (-(65536 * (k : Int))) / 65536 = -k by omega, if_pos (by omega), if_neg (by omega),
    show (-(65536 * (k : Int))) % 65536 = 0 by omega, show ((0 : Int)).toNat = 0 from rfl,
    factorOf_zero, show (-(-(k : Int))).toNat = k by omega]
  have hr : A % 2 ^ (k + 16) * 65536 ≤ max256 := by
    have h1 := Nat.mod_lt A (Nat.two_pow_pos (k + 16))
    have h2 : 2 ^ (k + 16) * 65536 ≤ 2 ^ 256 := by
      rw [show (65536 : Nat) = 2 ^ 16 from rfl, ← Nat.pow_add]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    have h3 : A % 2 ^ (k + 16) * 65536 < 2 ^ (k + 16) * 65536 :=
      Nat.mul_lt_mul_of_pos_right h1 (by decide)
    exact Nat.le_sub_one_of_lt (Nat.lt_of_lt_of_le h3 h2)
  rw [mdsC_exact hr, Nat.pow_add,
    show (2 : Nat) ^ 16 = 65536 from rfl, Nat.mul_div_mul_right _ _ (by decide)]
  have : A / 2 ^ k ≤ max256 := Nat.le_trans (Nat.div_le_self _ _) hA'
  rw [Nat.min_eq_left this, atLeastOne_eq_max]

/-- Past 224 halvings the result is never easier than `⌊A / 2^k⌋` (or 1). -/
theorem targetOf_harden_deep {A : Nat} {k : Nat} (hk : 225 ≤ k) :
    targetOf A (-(65536 * k)) ≤ max 1 (A / 2 ^ k) := by
  unfold targetOf
  rw [show (-(65536 * (k : Int))) / 65536 = -k by omega, if_pos (by omega)]
  split
  · omega
  rw [show (-(65536 * (k : Int))) % 65536 = 0 by omega, show ((0 : Int)).toNat = 0 from rfl,
    factorOf_zero, show (-(-(k : Int))).toNat = k by omega]
  have h := mdsC_le_div A 65536 (2 ^ (k + 16))
  rw [show A * 65536 / 2 ^ (k + 16) = A / 2 ^ k by
    rw [Nat.pow_add, show (2 : Nat) ^ 16 = 65536 from rfl, Nat.mul_div_mul_right _ _ (by decide)]] at h
  rw [atLeastOne_eq_max]; omega

/-- And strictly harder there: from an anchor at the maximum, 225 halvings
give less than `⌊max / 2^225⌋`, because `remainder * numerator` saturates in
`multiplyDividingSaturating`; from 240 halvings on the result is 1 although
`⌊max / 2^240⌋ = 65535`. -/
theorem targetOf_harden_deep_strict :
    targetOf max256 (-(65536 * 225)) < max256 / 2 ^ 225 ∧
    targetOf max256 (-(65536 * 240)) = 1 ∧ max256 / 2 ^ 240 = 65535 := by decide

/-- §5.5 "one half-life of drift is exactly one doubling", as the
implementation computes it: `k` half-lives of drift (inside the drift
clamp) multiply the anchor's target by exactly `2^k` when easing (saturating
at the maximum), and divide it by exactly `2^k` (floored, at least 1) for
`k ≤ 224` halvings. -/
theorem half_life_doubling {spec : Spec} {A : Nat} {at_ bt : Int} {ah bh : Nat} {k : Int}
    (hA : 0 < A) (hA' : A ≤ max256) (hh : ah < bh) (hHL : 0 < halfLifeMilliseconds spec)
    (hd : driftOf spec at_ ah bt bh = k * halfLifeMilliseconds spec)
    (hk : (k * halfLifeMilliseconds spec).natAbs ≤ maximumDriftC) :
    (0 ≤ k → asertOf spec A at_ ah bt bh = min (A * 2 ^ k.toNat) max256) ∧
    (k < 0 → -k ≤ 224 → asertOf spec A at_ ah bt bh = max 1 (A / 2 ^ (-k).toNat)) := by
  have he : asertOf spec A at_ ah bt bh = targetOf A (65536 * k) := by
    unfold asertOf
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), hd, exponentOf_whole hHL hk]
  rw [he]
  constructor
  · intro h0
    rw [show 65536 * k = 65536 * ((k.toNat : Nat) : Int) by omega]
    exact targetOf_ease_whole hA hA' _
  · intro h0 h1
    rw [show 65536 * k = -(65536 * (((-k).toNat : Nat) : Int)) by omega]
    exact targetOf_harden_whole hA' (by omega) (by omega)

/-- The drift clamp is not invisible: with a half-life of `2^62` ms, one
half-life of drift is clamped to `2^47 - 1` ms and moves the target by a
factor of `1 + 2^-16`, not 2. Exactness needs `|drift| ≤ 2^47 - 1` ms
(`half_life_doubling`'s last hypothesis). -/
theorem clamp_breaks_doubling :
    asertOf ⟨1, 2 ^ 62⟩ (2 ^ 200) 0 1 (2 ^ 62 + 1) 2 = 2 ^ 200 * factorOf 1 / 65536 ∧
    2 ^ 200 * factorOf 1 / 65536 < 2 ^ 201 := by decide

/-! ### Timestamps -/

/-- A forward shift of `k` half-lives raises the exponent by at most
`k` whole doublings (at or behind schedule). -/
theorem exponentOf_shift {D₁ D₂ HL : Int} {k : Nat} (hHL : 0 < HL) (h0 : 0 ≤ D₁)
    (h : D₁ ≤ D₂) (h' : D₂ ≤ D₁ + k * HL) :
    exponentOf D₂ HL ≤ exponentOf D₁ HL + 65536 * k := by
  unfold exponentOf
  have hc1 : 0 ≤ clampDrift D₁ := by unfold clampDrift maximumDriftC; omega
  have hc2 : 0 ≤ clampDrift D₂ := by unfold clampDrift maximumDriftC; omega
  have hc : clampDrift D₂ ≤ clampDrift D₁ + k * HL := by
    unfold clampDrift maximumDriftC
    have : 0 ≤ (k : Int) * HL := Int.mul_nonneg (by omega) (by omega)
    omega
  rw [Int.tdiv_eq_ediv_of_nonneg (by omega), Int.tdiv_eq_ediv_of_nonneg (by omega)]
  have := Int.ediv_le_ediv hHL (show clampDrift D₂ * 65536 ≤ clampDrift D₁ * 65536 + (65536 * k) * HL by
    have := Int.mul_le_mul_of_nonneg_right hc (show (0 : Int) ≤ 65536 by decide)
    rw [Int.add_mul] at this
    rw [show (65536 * (k : Int)) * HL = (k : Int) * HL * 65536 by
      simp only [Int.mul_assoc, Int.mul_comm]]
    exact this)
  rw [Int.add_mul_ediv_right _ _ (by omega)] at this
  exact this

/-- Easing: `k` more whole doublings multiply the target by at most `2^k`. -/
theorem targetOf_shift {A : Nat} (hA : 0 < A) (hA' : A ≤ max256) {e : Int} (he : 0 ≤ e)
    (k : Nat) : targetOf A (e + 65536 * k) ≤ targetOf A e * 2 ^ k := by
  unfold targetOf
  rw [if_neg (by omega), if_neg (by omega),
    show (e + 65536 * (k : Int)) % 65536 = e % 65536 by omega,
    show (e + 65536 * (k : Int)) / 65536 = e / 65536 + k by omega]
  have hs := mdsC_le A (factorOf (e % 65536).toNat) 65536
  have hs1 : 1 ≤ mdsC A (factorOf (e % 65536).toNat) 65536 := by
    have := mdsC_mono (v := A) (d := 65536) (factorOf_mono (Nat.zero_le (e % 65536).toNat))
    rw [factorOf_zero, mdsC_unit hA'] at this; omega
  generalize mdsC A (factorOf (e % 65536).toNat) 65536 = s at hs hs1
  have hp : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  unfold easeOf
  have hmax := max256_pos
  by_cases h1 : 256 ≤ e / 65536
  · rw [if_pos h1, if_pos (by omega), atLeastOne_of_pos hmax]
    have := Nat.mul_le_mul_left max256 hp; omega
  rw [if_neg h1]
  have hpos : 0 < min (s * 2 ^ (e / 65536).toNat) max256 := by
    have : 1 ≤ s * 2 ^ (e / 65536).toNat := Nat.mul_le_mul hs1 Nat.one_le_two_pow
    omega
  rw [atLeastOne_of_pos hpos]
  apply atLeastOne_le _ (Nat.le_trans hpos (Nat.le_mul_of_pos_right _ (by omega)))
  split
  · -- saturated: either the base was already saturated, or it reaches 2^256
    rename_i h2
    by_cases hb : s * 2 ^ (e / 65536).toNat ≤ max256
    · rw [Nat.min_eq_left hb]
      have h3 : 2 ^ 256 ≤ 2 ^ (e / 65536 + k).toNat := Nat.pow_le_pow_right (by decide) (by omega)
      have e1 : s * 2 ^ (e / 65536).toNat * 2 ^ k = s * 2 ^ (e / 65536 + k).toNat := by
        rw [Nat.mul_assoc, ← Nat.pow_add, show (e / 65536).toNat + k = (e / 65536 + k).toNat by omega]
      rw [e1]
      exact Nat.le_of_lt (Nat.lt_of_lt_of_le max256_lt
        (Nat.le_trans h3 (Nat.le_mul_of_pos_left _ hs1)))
    · rw [Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_le hb))]
      exact Nat.le_mul_of_pos_right _ (Nat.two_pow_pos k)
  · rw [show (e / 65536 + (k : Int)).toNat = (e / 65536).toNat + k by omega, Nat.pow_add,
      ← Nat.mul_assoc]
    by_cases hb : s * 2 ^ (e / 65536).toNat ≤ max256
    · rw [Nat.min_eq_left hb]; exact Nat.min_le_left _ _
    · rw [Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_le hb))]
      exact Nat.le_trans (Nat.min_le_right _ _) (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos k))

/-- §5.5 "moving it forwards ... eases only the one successor by
`2^(Δ / halfLife)`": at or behind schedule, a timestamp `k` half-lives later
gives a target at most `2^k` times easier. -/
theorem forward_shift {spec : Spec} {A : Nat} {at_ b₁ b₂ : Int} {ah bh : Nat} {k : Nat}
    (hA : 0 < A) (hA' : A ≤ max256) (hh : ah < bh) (hHL : 0 < halfLifeMilliseconds spec)
    (hbehind : 0 ≤ driftOf spec at_ ah b₁ bh) (h : b₁ ≤ b₂)
    (h' : b₂ ≤ b₁ + k * halfLifeMilliseconds spec) :
    asertOf spec A at_ ah b₂ bh ≤ asertOf spec A at_ ah b₁ bh * 2 ^ k := by
  unfold asertOf
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega)]
  have hd1 := elapsedOf_mono (at_ := at_) h
  have hd2 : driftOf spec at_ ah b₂ bh ≤ driftOf spec at_ ah b₁ bh + k * halfLifeMilliseconds spec := by
    unfold driftOf elapsedOf; unfold elapsedOf at hd1; omega
  have hx := exponentOf_shift hHL hbehind (by unfold driftOf; omega) hd2
  have he0 : 0 ≤ exponentOf (driftOf spec at_ ah b₁ bh) (halfLifeMilliseconds spec) := by
    have := exponentOf_mono (D₁ := 0) hHL hbehind
    have hc : clampDrift 0 = 0 := by unfold clampDrift maximumDriftC; omega
    unfold exponentOf at this ⊢; rw [hc, Int.zero_mul, Int.zero_tdiv] at this; exact this
  exact Nat.le_trans (targetOf_mono hA hA' hx) (targetOf_shift hA hA' he0 k)


/-! ### The anchor is per-branch: no intervening block matters -/

theorem anchorOf_skip {b a : Header} {mid rest : List Header} (hb : b.height ≠ 1)
    (hmid : ∀ x ∈ mid, x.height ≠ 1) (ha : a.height = 1) :
    anchorOf (b :: (mid ++ a :: rest)) = some a := by
  induction mid generalizing b with
  | nil => simp [anchorOf, hb, ha]
  | cons x mid ih =>
    have hx := hmid x (List.mem_cons_self ..)
    simp only [anchorOf, hb, if_false, List.cons_append]
    exact ih hx (fun y hy => hmid y (List.mem_cons_of_mem _ hy))

/-- §5.5 "a pure function of one anchor block and the block being targeted,
with no window and no intervening history": two branches sharing the
anchor give the block the same `nextTarget`, whatever lies between. -/
theorem next_ignores_intervening (spec : Spec) {b a : Header} {mid₁ mid₂ rest₁ rest₂ : List Header}
    (hb : b.height ≠ 1) (ha : a.height = 1) (h₁ : ∀ x ∈ mid₁, x.height ≠ 1)
    (h₂ : ∀ x ∈ mid₂, x.height ≠ 1) :
    nextTarget spec (b :: (mid₁ ++ a :: rest₁)) = nextTarget spec (b :: (mid₂ ++ a :: rest₂)) := by
  simp only [nextTarget, anchorOf_skip hb h₁ ha, anchorOf_skip hb h₂ ha]

/-- §5.5 "it does not compound": a timestamp moved on an earlier block `x`
of the branch changes no later block's `nextTarget`; it reaches only `x`'s
own (`forward_shift`). -/
theorem shift_does_not_compound (spec : Spec) {b x a : Header} {pre post rest : List Header}
    (t : Int) (hb : b.height ≠ 1) (hx : x.height ≠ 1) (ha : a.height = 1)
    (hpre : ∀ y ∈ pre, y.height ≠ 1) (hpost : ∀ y ∈ post, y.height ≠ 1) :
    nextTarget spec (b :: (pre ++ { x with timestamp := t } :: post ++ a :: rest))
      = nextTarget spec (b :: (pre ++ x :: post ++ a :: rest)) := by
  have hm : ∀ (y : Header), y.height ≠ 1 → ∀ z ∈ pre ++ y :: post, z.height ≠ 1 := by
    intro y hy z hz
    simp only [List.mem_append, List.mem_cons] at hz
    rcases hz with hz | rfl | hz
    · exact hpre z hz
    · exact hy
    · exact hpost z hz
  have e1 : pre ++ { x with timestamp := t } :: post ++ a :: rest
      = (pre ++ { x with timestamp := t } :: post) ++ a :: rest := by simp
  have e2 : pre ++ x :: post ++ a :: rest = (pre ++ x :: post) ++ a :: rest := by simp
  rw [e1, e2]
  exact next_ignores_intervening spec hb ha (hm _ hx) (hm _ hx)

/-- A block above height 1 does not set the schedule with its own target:
mining harder changes no `nextTarget`. -/
theorem next_ignores_own_target (spec : Spec) {b : Header} (anc : List Header) (t : Nat)
    (hb : b.height ≠ 1) :
    nextTarget spec ({ b with target := t } :: anc) = nextTarget spec (b :: anc) := by
  simp [nextTarget, anchorOf, hb]

/-- Block 1 anchors itself: its `nextTarget` is its own target, so block 1's
committed target is where the schedule starts. -/
theorem next_at_anchor (spec : Spec) {b : Header} (anc : List Header) (hb : b.height = 1) :
    nextTarget spec (b :: anc) = some b.target := by
  simp [nextTarget, anchorOf, hb, calculateAsertTarget]

/-! ### The fraction: the cubic against `2^x` -/

def allBelow (p : Nat → Bool) : Nat → Bool
  | 0 => true
  | n + 1 => p n && allBelow p n

theorem allBelow_spec {p : Nat → Bool} {n : Nat} (h : allBelow p n = true) {j : Nat}
    (hj : j < n) : p j = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [allBelow, Bool.and_eq_true] at h
    by_cases hjn : j = n
    · subst hjn; exact h.1
    · exact ih h.2 (by omega)

/-- Cell `j` of the grid `[8j, 8j + 8)`, upper end: the factor at the top of
the cell is within `1.00021 · 2^(8j/65536)`, raised to the 8192nd power. -/
def gridUpper (j : Nat) : Bool :=
  (factorOf (8 * (j + 1)) * 100000) ^ 8192 ≤ (100021 * 65536) ^ 8192 * 2 ^ j

/-- Lower end: the factor at the bottom of the cell is at least
`0.99979 · 2^((8j + 8)/65536)`. -/
def gridLower (j : Nat) : Bool :=
  (99979 * 65536) ^ 8192 * 2 ^ (j + 1) ≤ (factorOf (8 * j) * 100000) ^ 8192

set_option maxRecDepth 100000 in
theorem gridUpper_ok : allBelow gridUpper 8192 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gridLower_ok : allBelow gridLower 8192 = true := by decide +kernel

theorem pow8_lift {X N j : Nat} (h : X ^ 8192 ≤ N ^ 8192 * 2 ^ j) :
    X ^ 65536 ≤ N ^ 65536 * 2 ^ (j * 8) := by
  have h8 := Nat.pow_le_pow_left h 8
  rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul] at h8
  exact h8

theorem pow8_lift' {X N j : Nat} (h : N ^ 8192 * 2 ^ j ≤ X ^ 8192) :
    N ^ 65536 * 2 ^ (j * 8) ≤ X ^ 65536 := by
  have h8 := Nat.pow_le_pow_left h 8
  rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul] at h8
  exact h8

/-- The cubic never overshoots `2^(f/65536)` by more than 0.021%:
`factor/65536 ≤ 1.00021 · 2^(f/65536)`, stated without reals by raising both
sides to the 65536th power. -/
theorem factor_upper {f : Nat} (hf : f < 65536) :
    (factorOf f * 100000) ^ 65536 ≤ (100021 * 65536) ^ 65536 * 2 ^ f := by
  have hg := allBelow_spec gridUpper_ok (j := f / 8) (by omega)
  simp only [gridUpper, decide_eq_true_eq] at hg
  have hF : (factorOf f * 100000) ^ 65536 ≤ (factorOf (8 * (f / 8 + 1)) * 100000) ^ 65536 :=
    Nat.pow_le_pow_left (Nat.mul_le_mul_right _ (factorOf_mono (by omega))) _
  have h2 : 2 ^ (f / 8 * 8) ≤ 2 ^ f := Nat.pow_le_pow_right (by decide) (by omega)
  exact Nat.le_trans hF (Nat.le_trans (pow8_lift hg) (Nat.mul_le_mul_left _ h2))

/-- And never undershoots it by more than 0.021%:
`factor/65536 ≥ 0.99979 · 2^(f/65536)`. -/
theorem factor_lower {f : Nat} (hf : f < 65536) :
    (99979 * 65536) ^ 65536 * 2 ^ f ≤ (factorOf f * 100000) ^ 65536 := by
  have hg := allBelow_spec gridLower_ok (j := f / 8) (by omega)
  simp only [gridLower, decide_eq_true_eq] at hg
  have hF : (factorOf (8 * (f / 8)) * 100000) ^ 65536 ≤ (factorOf f * 100000) ^ 65536 :=
    Nat.pow_le_pow_left (Nat.mul_le_mul_right _ (factorOf_mono (by omega))) _
  have h2 : 2 ^ f ≤ 2 ^ ((f / 8 + 1) * 8) := Nat.pow_le_pow_right (by decide) (by omega)
  exact Nat.le_trans (Nat.mul_le_mul_left _ h2) (Nat.le_trans (pow8_lift' hg) hF)


/-! ## Non-vacuity: every hypothesis above is met by concrete inputs -/

-- One half-life ahead of schedule halves; one behind doubles (§5.5).
example : calculateAsertTarget ⟨600000, 120⟩ (2 ^ 215) 1700000000000 1
    (1700000000000 + 40000 * 600000 - 72000000) 40001 = some (2 ^ 214) := by decide
example : asertOf ⟨600000, 120⟩ (2 ^ 215) 0 1 (40000 * 600000 + 72000000) 40001 = 2 ^ 216 := by
  decide
-- On schedule at depth 1000 holds the anchor.
example : asertOf ⟨600000, 120⟩ (2 ^ 215) 0 1 (1000 * 600000) 1001 = 2 ^ 215 := by decide
-- Half a half-life earlier is strictly harder; a millisecond earlier is not
-- (the exponent truncates toward zero).
example : asertOf ⟨600000, 120⟩ (2 ^ 215) 0 1 (1000 * 600000 - 36000000) 1001 < 2 ^ 215 := by
  decide
example : asertOf ⟨600000, 120⟩ (2 ^ 215) 0 1 (1000 * 600000 - 1) 1001 = 2 ^ 215 := by decide
-- A forward shift of exactly one half-life meets `forward_shift`'s bound.
example : asertOf ⟨600000, 120⟩ (2 ^ 215) 0 1 (1000 * 600000 + 72000000) 1001
    = asertOf ⟨600000, 120⟩ (2 ^ 215) 0 1 (1000 * 600000) 1001 * 2 ^ 1 := by decide
-- Ten more blocks at the same timestamp: strictly harder.
example : asertOf ⟨600000, 120⟩ (2 ^ 215) 0 1 (1000 * 600000) 1011
    < asertOf ⟨600000, 120⟩ (2 ^ 215) 0 1 (1000 * 600000) 1001 := by decide
-- Saturation at both ends.
example : asertOf ⟨600000, 120⟩ max256 0 1 (1000 * 600000 + 72000000) 1001 = max256 := by decide
example : asertOf ⟨1, 1⟩ (2 ^ 215) 0 1 0 1001 = 1 := by decide
example : asertOf ⟨600000, 120⟩ 0 0 1 0 2 = 1 := by decide
-- The cubic at one half: `2^(1/2) · 65536 ≈ 92681.9`.
example : factorOf 32768 = 92674 := by decide
-- Two branches with different blocks between the anchor and `b`.
example : nextTarget ⟨600000, 120⟩
      [⟨4, 1800000, 7⟩, ⟨3, 1200000, 9⟩, ⟨2, 600000, 11⟩, ⟨1, 0, 2 ^ 200⟩, ⟨0, -5, max256⟩]
    = nextTarget ⟨600000, 120⟩ [⟨4, 1800000, 7⟩, ⟨3, 1, 3⟩, ⟨2, 0, 5⟩, ⟨1, 0, 2 ^ 200⟩]
    ∧ nextTarget ⟨600000, 120⟩ [⟨4, 1800000, 7⟩, ⟨1, 0, 2 ^ 200⟩] = some (2 ^ 200) := by decide
-- A harder block 4 leaves its `nextTarget` alone; a harder block 1 moves it.
example : nextTarget ⟨600000, 120⟩ [⟨4, 1800000, 1⟩, ⟨1, 0, 2 ^ 200⟩]
      = nextTarget ⟨600000, 120⟩ [⟨4, 1800000, 2 ^ 199⟩, ⟨1, 0, 2 ^ 200⟩]
    ∧ nextTarget ⟨600000, 120⟩ [⟨1, 0, 2 ^ 100⟩] = some (2 ^ 100) := by decide

end Lattice.Asert