import LatticeProofs.Work

/-!
# Work from targets: proofs (spec §5.4, §9.1, §9.5)

The statements below are the specification of `Work.lean`'s functions; the
proofs only establish them.
-/

namespace Lattice.Work

/-! ## The formula -/

/-- §5.4: for every nonzero target, `workForTarget t = ⌊N / (t + 1)⌋`. -/
theorem workForTarget_eq {N t : Nat} (h1 : 1 ≤ t) (ht : t < N) :
    workForTarget N t = N / (t + 1) := by
  unfold workForTarget
  simp only [show t ≠ 0 by omega, ↓reduceIte]
  split
  · have : t + 1 = N := by omega
    rw [this, Nat.div_self (by omega)]
  · rw [← Nat.add_div_right _ (by omega : 0 < t + 1)]
    congr 1; omega

/-- §5.4: target `0` is credited `0`, and it is met by no hash. -/
theorem workForTarget_zero (N : Nat) : workForTarget N 0 = 0 ∧ ∀ h, ¬ Meets 0 h := by
  refine ⟨rfl, fun h hm => ?_⟩
  exact Nat.lt_irrefl 0 hm.1

/-- §5.4: the easiest target is credited `1`. -/
theorem workForTarget_max {N : Nat} (hN : 2 ≤ N) : workForTarget N (N - 1) = 1 := by
  unfold workForTarget
  simp only [show N - 1 ≠ 0 by omega, Nat.le_refl, ↓reduceIte]

/-- §5.4: the code equals Bitcoin's chainwork in `N`-bit arithmetic for every
target, the zero target included (`N / 1` wraps to `0`). -/
theorem workForTarget_eq_bitcoin {N t : Nat} (hN : 2 ≤ N) (ht : t < N) :
    workForTarget N t = bitcoinWork N t := by
  unfold bitcoinWork
  by_cases h0 : t = 0
  · subst h0
    rw [Nat.mod_eq_of_lt (by omega : 0 + 1 < N), Nat.div_one,
      (by omega : N - 1 - 0 + 1 = N), Nat.mod_self]
    rfl
  by_cases hm : t = N - 1
  · subst hm
    rw [(by omega : N - 1 + 1 = N), Nat.mod_self, Nat.div_zero, Nat.mod_eq_of_lt (by omega)]
    exact workForTarget_max (by omega)
  · rw [Nat.mod_eq_of_lt (by omega : t + 1 < N)]
    have hw : (N - 1 - t) / (t + 1) + 1 = N / (t + 1) := by
      rw [← Nat.add_div_right _ (by omega : 0 < t + 1)]; congr 1; omega
    rw [hw, workForTarget_eq (by omega) ht]
    exact (Nat.mod_eq_of_lt (Nat.div_lt_self (by omega) (by omega))).symm

/-- §5.4: `workForHash` is `workForTarget` of the hash read as a target,
except that hash `0` saturates at `U256_MAX` instead of crediting `0`. -/
theorem workForHash_eq {N h : Nat} (h0 : h ≠ 0) : workForHash N h = workForTarget N h := by
  unfold workForHash workForTarget; simp only [h0, ↓reduceIte]

theorem workForHash_zero (N : Nat) : workForHash N 0 = N - 1 := rfl

/-! ## The exclusive form over-credits by up to 2× -/

/-- §5.4: the exclusive `U256_MAX / t` is never below the inclusive work and
never above twice it. -/
theorem exclusive_between {N t : Nat} (h1 : 1 ≤ t) (ht : t < N) :
    workForTarget N t ≤ exclusiveWork N t ∧ exclusiveWork N t ≤ 2 * workForTarget N t := by
  rw [workForTarget_eq h1 ht]
  unfold exclusiveWork; simp only [show t ≠ 0 by omega, ↓reduceIte]
  have hd := Nat.div_add_mod N (t + 1)
  have hr := Nat.mod_lt N (by omega : 0 < t + 1)
  have hq : 1 ≤ N / (t + 1) := Nat.div_pos (by omega) (by omega)
  generalize N / (t + 1) = q at *
  generalize N % (t + 1) = r at *
  have hqt : q ≤ t * q := Nat.le_mul_of_pos_left q h1
  constructor
  · rw [Nat.le_div_iff_mul_le (by omega)]
    have : (t + 1) * q = t * q + q := by rw [Nat.add_mul, Nat.one_mul]
    rw [Nat.mul_comm]; omega
  · apply Nat.le_of_lt_succ
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    grind

/-- The 2× is reached: at target `1` the exclusive form credits `N - 1`, the
inclusive one `N / 2`. -/
theorem exclusive_at_one {N : Nat} (hN : 2 ≤ N) :
    exclusiveWork N 1 = N - 1 ∧ workForTarget N 1 = N / 2 := by
  refine ⟨by simp [exclusiveWork], workForTarget_eq (by omega) (by omega)⟩

/-! ## Incentive: no target earns more than the true work -/

/-- §5.4: the expected credit of one hash at any target, `(t + 1) / N ·
workForTarget t`, is at most `1`. A harder-than-scheduled target therefore
never earns more than the work the hash did. -/
theorem credit_per_hash_le {N t : Nat} (ht : t < N) :
    (t + 1) * workForTarget N t ≤ N := by
  by_cases h0 : t = 0
  · subst h0; simp [workForTarget]
  rw [workForTarget_eq (by omega) ht]
  exact Nat.mul_div_le N (t + 1)

/-- The lower bound: every nonzero target earns more than `1/2` per hash, and
loses less than `(t + 1) / N` to rounding (nothing at the realistic targets
where `t + 1` divides `N` or `t + 1 ≪ N`). -/
theorem credit_per_hash_ge {N t : Nat} (h1 : 1 ≤ t) (ht : t < N) :
    N < 2 * ((t + 1) * workForTarget N t) ∧ N < (t + 1) * workForTarget N t + (t + 1) := by
  rw [workForTarget_eq h1 ht]
  have hd := Nat.div_add_mod N (t + 1)
  have hr := Nat.mod_lt N (by omega : 0 < t + 1)
  have hq : 1 ≤ N / (t + 1) := Nat.div_pos (by omega) (by omega)
  generalize N / (t + 1) = q at *
  generalize N % (t + 1) = r at *
  have : t + 1 ≤ (t + 1) * q := Nat.le_mul_of_pos_right (t + 1) hq
  omega

/-- The rejected exclusive form earns more than `1` per hash at target `1`
(two hashes meet it, each credited `N - 1`). -/
theorem exclusive_credit_exceeds {N : Nat} (hN : 3 ≤ N) : N < (1 + 1) * exclusiveWork N 1 := by
  simp [exclusiveWork]; omega

/-! ## Carrier ladders (§9.1, §9.5) -/

theorem rootMost_le_maxBeaten (N : Nat) : ∀ (cs : List Nat) (h : Nat),
    rootMost N cs h ≤ maxBeaten N cs h
  | [], _ => Nat.le_refl _
  | t :: cs, h => by
    simp only [rootMost, maxBeaten]
    split
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (rootMost_le_maxBeaten N cs h) (Nat.le_max_right _ _)

/-- §9.5: for every ladder and every hash, the root-most-beaten rule credits
at most what the maximum over beaten targets credits. -/
theorem credit_le_creditMax (N : Nat) (cs : List Nat) (tT h : Nat) :
    credit N cs tT h ≤ creditMax N cs tT h := by
  unfold credit creditMax
  split
  · have := rootMost_le_maxBeaten N cs h
    simp only [Nat.max_def]; split <;> split <;> omega
  · exact Nat.le_refl _

theorem sumBelow_le {f g : Nat → Nat} : ∀ {n : Nat}, (∀ h, h < n → f h ≤ g h) →
    sumBelow f n ≤ sumBelow g n
  | 0, _ => Nat.le_refl _
  | n + 1, hfg => Nat.add_le_add (sumBelow_le fun h hh => hfg h (by omega)) (hfg n (by omega))

theorem sumBelow_add (f g : Nat → Nat) : ∀ n : Nat,
    sumBelow (fun h => f h + g h) n = sumBelow f n + sumBelow g n
  | 0 => rfl
  | n + 1 => by simp only [sumBelow, sumBelow_add f g n]; omega

theorem sumBelow_paid (N t : Nat) : ∀ n : Nat, n ≤ t + 1 → sumBelow (paid N t) n ≤ n * workForTarget N t
  | 0, _ => by simp [sumBelow]
  | n + 1, hn => by
    simp only [sumBelow, Nat.succ_mul]
    have := sumBelow_paid N t n (by omega)
    have : paid N t n ≤ workForTarget N t := by unfold paid; split <;> omega
    omega

theorem sumBelow_paid_tail (N t : Nat) : ∀ n : Nat, t + 1 ≤ n →
    sumBelow (paid N t) n = sumBelow (paid N t) (t + 1)
  | 0, h => by omega
  | n + 1, hn => by
    by_cases he : n + 1 = t + 1
    · rw [he]
    · show sumBelow (paid N t) n + paid N t n = _
      rw [sumBelow_paid_tail N t n (by omega)]
      have : paid N t n = 0 := by
        simp only [paid, Meets]; simp [show ¬ (0 < t ∧ n ≤ t) by omega]
      omega

/-- Expected credit of one target over all `N` hashes: at most `N`, that is at
most `1` per hash. -/
theorem sumBelow_paid_le {N t : Nat} (ht : t < N) : sumBelow (paid N t) N ≤ N := by
  rw [sumBelow_paid_tail N t N (by omega)]
  exact Nat.le_trans (sumBelow_paid N t (t + 1) (Nat.le_refl _)) (credit_per_hash_le ht)

theorem rootMost_le_sum (N : Nat) : ∀ (cs : List Nat) (h : Nat),
    rootMost N cs h ≤ (cs.map fun t => paid N t h).sum
  | [], _ => Nat.le_refl _
  | t :: cs, h => by
    have := rootMost_le_sum N cs h
    simp only [rootMost, List.map_cons, List.sum_cons]
    unfold paid at this ⊢
    split
    · exact Nat.le_add_right _ _
    · omega

theorem sumBelow_listSum (N : Nat) : ∀ (cs : List Nat) (n : Nat),
    sumBelow (fun h => (cs.map fun t => paid N t h).sum) n =
      (cs.map fun t => sumBelow (paid N t) n).sum
  | [], n => by
    simp only [List.map_nil, List.sum_nil]
    induction n with
    | zero => rfl
    | succ n ih => simp [sumBelow, ih]
  | t :: cs, n => by
    simp only [List.map_cons, List.sum_cons]
    rw [sumBelow_add (paid N t) (fun h => (cs.map fun t => paid N t h).sum),
      sumBelow_listSum N cs n]

/-- §9.5, what is true of fabricated ladders: over all `N` hashes, a ladder of
`k` carriers (any targets the prover likes, each a `U256`) earns at most
`(k + 1) · N`, that is at most `k + 1` per hash in expectation. Not `1`: see
`ladder_exceeds_one`. -/
theorem ladder_credit_le {N : Nat} {cs : List Nat} {tT : Nat} (hcs : ∀ t ∈ cs, t < N)
    (hT : tT < N) : sumBelow (credit N cs tT) N ≤ (cs.length + 1) * N := by
  have hpt : ∀ h, credit N cs tT h ≤ paid N tT h + (cs.map fun t => paid N t h).sum := by
    intro h
    have := rootMost_le_sum N cs h
    unfold credit paid at *
    split
    · simp only [Nat.max_def]; split <;> omega
    · omega
  refine Nat.le_trans (sumBelow_le fun h _ => hpt h) ?_
  rw [sumBelow_add, sumBelow_listSum]
  have hT' := sumBelow_paid_le hT
  have : (cs.map fun t => sumBelow (paid N t) N).sum ≤ cs.length * N := by
    clear hT hT' hpt
    induction cs with
    | nil => simp
    | cons t cs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
      have h1 := sumBelow_paid_le (hcs t (List.mem_cons_self ..))
      have h2 := ih fun t ht => hcs t (List.mem_cons_of_mem _ ht)
      omega
  rw [Nat.succ_mul]; omega

/-- With no carrier the rule is the plain target rule: at most `1` per hash. -/
theorem terminal_credit_le {N tT : Nat} (hT : tT < N) : sumBelow (credit N [] tT) N ≤ N := by
  simpa using ladder_credit_le (cs := []) (fun _ h => nomatch h) hT

/-! ## Non-vacuity, at small widths (computed by `decide`) -/

/-- One carrier above the terminal earns more than `1` per hash: at width
`16`, a hard root carrier (target `1`) over the easiest terminal (target `15`)
earns `30` over the `16` hashes, against the bound `2 · 16`. -/
theorem ladder_exceeds_one : sumBelow (credit 16 [1] 15) 16 = 30 := by decide

/-- An inverted ladder where the two rules differ: the root carrier (target
`10`) is met, a deeper carrier (target `5`) is harder and met too. The
root-most rule credits `workForTarget 10 = 23`, the maximum `42`. -/
theorem rules_differ : credit 256 [10, 5] 20 3 = 23 ∧ creditMax 256 [10, 5] 20 3 = 42 := by
  decide

/-- A harder-than-scheduled target can earn more per hash than an awkward
scheduled one (rounding at `t + 1 > N / 2`), though never more than `1`:
target `128` earns `129 / 256`, target `127` exactly `1`. -/
theorem harder_target_rounding :
    (128 + 1) * workForTarget 256 128 = 129 ∧ (127 + 1) * workForTarget 256 127 = 256 := by
  decide

/-! ## `U256` (`N = 2^256`) -/

/-- The edges of §5.4 at full width. -/
theorem u256_edges :
    workForTarget (2 ^ 256) 0 = 0 ∧ workForTarget (2 ^ 256) U256Max = 1 ∧
      workForTarget (2 ^ 256) 1 = 2 ^ 255 ∧ exclusiveWork (2 ^ 256) 1 = U256Max ∧
      workForHash (2 ^ 256) 0 = U256Max := by
  decide


end Lattice.Work
