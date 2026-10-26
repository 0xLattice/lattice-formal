import LatticeProofs.Model

/-! Helper lemmas for `Conservation.lean`. -/

namespace Lattice

section MapLemmas

variable {κ ν : Type} [DecidableEq κ]

@[simp] theorem Map.get?_nil (k : κ) : Map.get? ([] : Map κ ν) k = none := rfl

theorem Map.get?_cons (k0 k : κ) (v : ν) (t : Map κ ν) :
    Map.get? ((k0, v) :: t) k = if k0 = k then some v else t.get? k := by
  by_cases h : k0 = k <;> simp [Map.get?, h]

@[simp] theorem Map.erase_nil (k : κ) : Map.erase ([] : Map κ ν) k = [] := rfl

theorem Map.erase_cons (k0 k : κ) (v : ν) (t : Map κ ν) :
    Map.erase ((k0, v) :: t) k = if k0 = k then t.erase k else (k0, v) :: t.erase k := by
  by_cases h : k0 = k <;> simp [Map.erase, h]

theorem Map.get?_erase_self (m : Map κ ν) (k : κ) : (m.erase k).get? k = none := by
  induction m with
  | nil => rfl
  | cons e t ih =>
    obtain ⟨k0, v⟩ := e
    rw [Map.erase_cons]
    by_cases h : k0 = k
    · simp [h, ih]
    · simp [h, Map.get?_cons, ih]

theorem Map.get?_erase_ne (m : Map κ ν) {k k' : κ} (h : k' ≠ k) :
    (m.erase k).get? k' = m.get? k' := by
  induction m with
  | nil => rfl
  | cons e t ih =>
    obtain ⟨k0, v⟩ := e
    rw [Map.erase_cons, Map.get?_cons]
    by_cases h0 : k0 = k
    · subst h0
      have : ¬ k0 = k' := fun e => h e.symm
      simp [this, ih]
    · simp [h0, Map.get?_cons, ih]

theorem Map.get?_set_self (m : Map κ ν) (k : κ) (v : ν) : (m.set k v).get? k = some v := by
  simp [Map.set, Map.get?_cons]

theorem Map.get?_set_ne (m : Map κ ν) {k k' : κ} (v : ν) (h : k' ≠ k) :
    (m.set k v).get? k' = m.get? k' := by
  have : ¬ k = k' := fun e => h e.symm
  simp [Map.set, Map.get?_cons, this, Map.get?_erase_ne m h]

theorem Map.get?_set (m : Map κ ν) (k k' : κ) (v : ν) :
    (m.set k v).get? k' = if k' = k then some v else m.get? k' := by
  by_cases h : k' = k
  · subst h; simp [Map.get?_set_self]
  · simp [h, Map.get?_set_ne m v h]

theorem Map.get?_erase (m : Map κ ν) (k k' : κ) :
    (m.erase k).get? k' = if k' = k then none else m.get? k' := by
  by_cases h : k' = k
  · subst h; simp [Map.get?_erase_self]
  · simp [h, Map.get?_erase_ne m h]

omit [DecidableEq κ] in
theorem Map.keys_cons (k : κ) (v : ν) (t : Map κ ν) :
    Map.keys ((k, v) :: t) = k :: t.keys := rfl

theorem Map.get?_eq_none_of_not_mem (m : Map κ ν) (k : κ) (h : k ∉ m.keys) :
    m.get? k = none := by
  induction m with
  | nil => rfl
  | cons e t ih =>
    obtain ⟨k0, v⟩ := e
    rw [Map.keys_cons, List.mem_cons, not_or] at h
    rw [Map.get?_cons]
    have : ¬ k0 = k := fun e => h.1 e.symm
    simp [this, ih h.2]

theorem Map.erase_of_not_mem (m : Map κ ν) (k : κ) (h : k ∉ m.keys) : m.erase k = m := by
  induction m with
  | nil => rfl
  | cons e t ih =>
    obtain ⟨k0, v⟩ := e
    rw [Map.keys_cons, List.mem_cons, not_or] at h
    rw [Map.erase_cons]
    have : ¬ k0 = k := fun e => h.1 e.symm
    simp [this, ih h.2]

theorem Map.keys_erase_sublist (m : Map κ ν) (k : κ) : (m.erase k).keys.Sublist m.keys := by
  unfold Map.keys Map.erase
  exact (List.filter_sublist).map _

theorem Map.not_mem_keys_erase (m : Map κ ν) (k : κ) : k ∉ (m.erase k).keys := by
  unfold Map.keys Map.erase
  simp

theorem Map.nodup_erase {m : Map κ ν} (h : m.keys.Nodup) (k : κ) : (m.erase k).keys.Nodup :=
  h.sublist (Map.keys_erase_sublist m k)

theorem Map.nodup_set {m : Map κ ν} (h : m.keys.Nodup) (k : κ) (v : ν) :
    (m.set k v).keys.Nodup := by
  unfold Map.set
  rw [Map.keys_cons, List.nodup_cons]
  exact ⟨Map.not_mem_keys_erase m k, Map.nodup_erase h k⟩

theorem Map.mem_erase {m : Map κ ν} {e : κ × ν} {k : κ} (h : e ∈ m.erase k) : e ∈ m := by
  unfold Map.erase at h
  exact (List.mem_filter.mp h).1

omit [DecidableEq κ] in
theorem Map.total_cons (k : κ) (v : Nat) (t : Map κ Nat) :
    Map.total ((k, v) :: t) = v + t.total := by
  simp [Map.total]

theorem Map.total_erase {m : Map κ Nat} (h : m.keys.Nodup) (k : κ) :
    m.total = (m.erase k).total + (m.get? k).getD 0 := by
  induction m with
  | nil => rfl
  | cons e t ih =>
    obtain ⟨k0, v⟩ := e
    rw [Map.keys_cons, List.nodup_cons] at h
    rw [Map.erase_cons, Map.get?_cons, Map.total_cons]
    by_cases h0 : k0 = k
    · subst h0
      simp [Map.erase_of_not_mem t k0 h.1]
      omega
    · simp [h0, Map.total_cons, ih h.2]
      omega

theorem Map.total_set {m : Map κ Nat} (h : m.keys.Nodup) (k : κ) (v : Nat) :
    (m.set k v).total + (m.get? k).getD 0 = m.total + v := by
  unfold Map.set
  rw [Map.total_cons, Map.total_erase h k]
  omega

end MapLemmas

/-! ## Withdrawals -/

theorem applyWithdrawals_spec {dir : String} {pr : Map ReceiptKey Address} :
    ∀ (as : List Action) (m m' : Map DepositKey Nat),
      m.keys.Nodup → applyWithdrawals dir pr m as = some m' →
      m'.keys.Nodup ∧ m'.total + totalWithdrawn as = m.total ∧
      (∀ k, m.get? k = some 0 → m'.get? k = some 0) ∧
      (∀ k, m'.get? k = none → m.get? k = none) ∧
      (∀ w n dm amtD amtW, Action.withdrawal w n dm amtD amtW ∈ as →
        m.get? ⟨dm, amtD, n⟩ = some amtW ∧ amtW ≠ 0 ∧
        pr.get? ⟨dir, dm, amtD, n⟩ = some w ∧ m'.get? ⟨dm, amtD, n⟩ = some 0)
  | [], m, m', hn, h => by
    simp [applyWithdrawals] at h
    subst h
    exact ⟨hn, by simp [totalWithdrawn], fun _ h => h, fun _ h => h, by simp⟩
  | a :: as, m, m', hn, h => by
    cases a with
    | withdrawal w0 n0 dm0 amtD0 amtW0 =>
      simp only [applyWithdrawals] at h
      split at h
      · rename_i hc
        obtain ⟨hget, hne, -, hpr⟩ := hc
        have hn' := Map.nodup_set hn ⟨dm0, amtD0, n0⟩ 0
        obtain ⟨r1, r2, r3, r4, r5⟩ := applyWithdrawals_spec as _ m' hn' h
        have ht := Map.total_set hn ⟨dm0, amtD0, n0⟩ 0
        rw [hget] at ht
        refine ⟨r1, ?_, ?_, ?_, ?_⟩
        · simp only [totalWithdrawn, Option.getD] at ht ⊢
          omega
        · intro k hk
          apply r3
          rw [Map.get?_set]
          split <;> simp_all
        · intro k hk
          have := r4 k hk
          rw [Map.get?_set] at this
          split at this
          · simp at this
          · exact this
        · intro w n dm amtD amtW hmem
          rw [List.mem_cons] at hmem
          rcases hmem with heq | hmem
          · cases heq
            exact ⟨hget, hne, hpr, r3 _ (Map.get?_set_self _ _ _)⟩
          · obtain ⟨q1, q2, q3, q4⟩ := r5 w n dm amtD amtW hmem
            rw [Map.get?_set] at q1
            split at q1
            · simp at q1; exact absurd q1.symm q2
            · exact ⟨q1, q2, q3, q4⟩
      · simp at h
    | _ =>
      simp only [applyWithdrawals] at h
      obtain ⟨r1, r2, r3, r4, r5⟩ := applyWithdrawals_spec as m m' hn h
      refine ⟨r1, by simpa [totalWithdrawn] using r2, r3, r4, ?_⟩
      intro w n dm amtD amtW hmem
      rw [List.mem_cons] at hmem
      rcases hmem with heq | hmem
      · cases heq
      · exact r5 w n dm amtD amtW hmem

/-! ## Deposits -/

theorem applyDeposits_spec :
    ∀ (as : List Action) (m m' : Map DepositKey Nat),
      m.keys.Nodup → applyDeposits m as = some m' →
      m'.keys.Nodup ∧ m'.total = m.total + totalDeposited as ∧
      (∀ k v, m.get? k = some v → m'.get? k = some v) ∧
      (∀ n dm amtD amt, Action.deposit n dm amtD amt ∈ as → m.get? ⟨dm, amtD, n⟩ = none)
  | [], m, m', hn, h => by
    simp [applyDeposits] at h
    subst h
    exact ⟨hn, by simp [totalDeposited], fun _ _ h => h, by simp⟩
  | a :: as, m, m', hn, h => by
    cases a with
    | deposit n0 dm0 amtD0 amt0 =>
      simp only [applyDeposits] at h
      split at h
      · rename_i hc
        obtain ⟨hget, hne, hneD⟩ := hc
        have hn' := Map.nodup_set hn ⟨dm0, amtD0, n0⟩ amt0
        obtain ⟨r1, r2, r3, r4⟩ := applyDeposits_spec as _ m' hn' h
        have ht := Map.total_set hn ⟨dm0, amtD0, n0⟩ amt0
        rw [hget] at ht
        refine ⟨r1, ?_, ?_, ?_⟩
        · simp only [totalDeposited, Option.getD] at ht ⊢
          omega
        · intro k v hk
          apply r3
          rw [Map.get?_set]
          split
          · rename_i hk'; subst hk'; rw [hget] at hk; cases hk
          · exact hk
        · intro n dm amtD amt hmem
          rw [List.mem_cons] at hmem
          rcases hmem with heq | hmem
          · cases heq; exact hget
          · have q := r4 n dm amtD amt hmem
            rw [Map.get?_set] at q
            split at q
            · simp at q
            · exact q
      · simp at h
    | _ =>
      simp only [applyDeposits] at h
      obtain ⟨r1, r2, r3, r4⟩ := applyDeposits_spec as m m' hn h
      refine ⟨r1, by simpa [totalDeposited] using r2, r3, ?_⟩
      intro n dm amtD amt hmem
      rw [List.mem_cons] at hmem
      rcases hmem with heq | hmem
      · cases heq
      · exact r4 n dm amtD amt hmem

/-! ## Receipts -/

theorem applyReceipts_spec :
    ∀ (as : List Action) (m m' : Map ReceiptKey Address),
      applyReceipts m as = some m' →
      (m.keys.Nodup → m'.keys.Nodup) ∧
      (∀ a k, a ∈ as → receiptKeyOf a = some k → m.get? k = none) ∧
      (∀ k, (m'.get? k).isSome → (m.get? k).isSome ∨ ∃ a ∈ as, receiptKeyOf a = some k)
  | [], m, m', h => by
    simp [applyReceipts] at h
    subst h
    exact ⟨id, by simp, fun _ h => Or.inl h⟩
  | a :: as, m, m', h => by
    cases a with
    | receipt w0 n0 dm0 amtD0 d0 =>
      simp only [applyReceipts] at h
      split at h
      · rename_i hget
        obtain ⟨r1, r2, r3⟩ := applyReceipts_spec as _ m' h
        refine ⟨fun hn => r1 (Map.nodup_set hn _ _), ?_, ?_⟩
        · intro a k hmem hk
          rw [List.mem_cons] at hmem
          rcases hmem with heq | hmem
          · subst heq; simp [receiptKeyOf] at hk; subst hk; exact hget.1
          · have q := r2 a k hmem hk
            rw [Map.get?_set] at q
            split at q
            · simp at q
            · exact q
        · intro k hk
          rcases r3 k hk with q | ⟨a, ha, hka⟩
          · rw [Map.get?_set] at q
            split at q
            · rename_i hkk
              exact Or.inr ⟨_, List.mem_cons_self, by simp [receiptKeyOf, hkk]⟩
            · exact Or.inl q
          · exact Or.inr ⟨a, List.mem_cons_of_mem _ ha, hka⟩
      · simp at h
    | _ =>
      simp only [applyReceipts] at h
      obtain ⟨r1, r2, r3⟩ := applyReceipts_spec as m m' h
      refine ⟨r1, ?_, ?_⟩
      · intro a k hmem hk
        rw [List.mem_cons] at hmem
        rcases hmem with heq | hmem
        · subst heq; simp [receiptKeyOf] at hk
        · exact r2 a k hmem hk
      · intro k hk
        rcases r3 k hk with q | ⟨a, ha, hka⟩
        · exact Or.inl q
        · exact Or.inr ⟨a, List.mem_cons_of_mem _ ha, hka⟩

/-! ## Balances -/

/-- The step function of `applyBalances`. -/
def balStep (m : Map Address Nat) (ds : List (Address × Int)) (acc : Map Address Nat)
    (o : Address) : Option (Map Address Nat) :=
  let v : Int := ((m.get? o).getD 0 : Int) + netDelta ds o
  if v < 0 then none
  else if v = 0 then some (acc.erase o)
  else some (acc.set o v.toNat)

theorem applyBalances_eq (m : Map Address Nat) (ds : List (Address × Int)) :
    applyBalances m ds = (ds.map (·.1)).eraseDups.foldlM (balStep m ds) m := rfl

theorem balFold_spec (m : Map Address Nat) (ds : List (Address × Int)) :
    ∀ (L : List Address) (acc r : Map Address Nat),
      L.Nodup → acc.keys.Nodup → (∀ e ∈ acc, 0 < e.2) →
      (∀ o ∈ L, acc.get? o = m.get? o) →
      L.foldlM (balStep m ds) acc = some r →
      r.keys.Nodup ∧ (∀ e ∈ r, 0 < e.2) ∧
      (r.total : Int) = acc.total + (L.map (netDelta ds)).sum
  | [], acc, r, _, hn, hp, _, h => by
    simp at h
    subst h
    exact ⟨hn, hp, by simp⟩
  | o :: L, acc, r, hL, hn, hp, hag, h => by
    rw [List.foldlM_cons] at h
    rw [List.nodup_cons] at hL
    have hag' : ∀ o' ∈ L, o' ≠ o := fun o' ho' e => hL.1 (e ▸ ho')
    have hacc : acc.get? o = m.get? o := hag o List.mem_cons_self
    have ht := Map.total_erase hn o
    rw [hacc] at ht
    unfold balStep at h
    simp only at h
    split at h
    · simp at h
    · rename_i hv0
      split at h
      · rename_i hv
        simp only [Option.bind_eq_bind, Option.bind_some] at h
        obtain ⟨r1, r2, r3⟩ := balFold_spec m ds L (acc.erase o) r hL.2 (Map.nodup_erase hn o)
          (fun e he => hp e (Map.mem_erase he))
          (fun o' ho' => by rw [Map.get?_erase_ne _ (hag' o' ho')]; exact hag o' (List.mem_cons_of_mem _ ho'))
          h
        refine ⟨r1, r2, ?_⟩
        rw [r3, List.map_cons, List.sum_cons]
        omega
      · rename_i hv
        simp only [Option.bind_eq_bind, Option.bind_some] at h
        obtain ⟨r1, r2, r3⟩ := balFold_spec m ds L _ r hL.2 (Map.nodup_set hn o _)
          (by
            intro e he
            unfold Map.set at he
            rw [List.mem_cons] at he
            rcases he with he | he
            · subst he; simp only; omega
            · exact hp e (Map.mem_erase he))
          (fun o' ho' => by rw [Map.get?_set_ne _ _ (hag' o' ho')]; exact hag o' (List.mem_cons_of_mem _ ho'))
          h
        have ht2 := Map.total_set hn o (((m.get? o).getD 0 : Int) + netDelta ds o).toNat
        rw [hacc] at ht2
        refine ⟨r1, r2, ?_⟩
        rw [r3, List.map_cons, List.sum_cons]
        omega

theorem nodup_eraseDups_aux : ∀ (n : Nat) (l : List Address), l.length ≤ n → l.eraseDups.Nodup
  | _, [], _ => by simp
  | 0, _ :: _, h => by simp at h
  | n + 1, a :: l, h => by
    rw [List.eraseDups_cons, List.nodup_cons]
    refine ⟨?_, nodup_eraseDups_aux n _ ?_⟩
    · rw [List.mem_eraseDups, List.mem_filter]; simp
    · simp at h
      exact Nat.le_trans (List.length_filter_le _ _) h

theorem nodup_eraseDups (l : List Address) : l.eraseDups.Nodup :=
  nodup_eraseDups_aux _ l (Nat.le_refl _)

theorem sum_map_zero {α : Type} (L : List α) : (L.map (fun _ => (0 : Int))).sum = 0 := by
  induction L with
  | nil => rfl
  | cons a t ih => simp [ih]

theorem sum_map_add' {α : Type} (f g : α → Int) (L : List α) :
    (L.map (fun a => f a + g a)).sum = (L.map f).sum + (L.map g).sum := by
  induction L with
  | nil => rfl
  | cons a t ih => simp [ih]; omega

theorem sum_ite_eq (c : Int) (x : Address) :
    ∀ (L : List Address), L.Nodup → x ∈ L →
      (L.map (fun o => if x = o then c else 0)).sum = c
  | [], _, h => by simp at h
  | o :: L, hL, h => by
    rw [List.nodup_cons] at hL
    rw [List.map_cons, List.sum_cons]
    by_cases hx : x = o
    · subst hx
      have : (L.map (fun o => if x = o then c else 0)).sum = 0 := by
        have : ∀ o ∈ L, (if x = o then c else 0) = 0 := by
          intro o ho; have : x ≠ o := fun e => hL.1 (e ▸ ho); simp [this]
        rw [List.map_congr_left this]; exact sum_map_zero L
      simp [this]
    · simp [hx]
      exact sum_ite_eq c x L hL.2 (by simpa [hx] using h)

theorem netDelta_cons (x : Address × Int) (ds : List (Address × Int)) (o : Address) :
    netDelta (x :: ds) o = (if x.1 = o then x.2 else 0) + netDelta ds o := by
  unfold netDelta
  by_cases h : x.1 = o <;> simp [h]

theorem sum_netDelta (L : List Address) (hL : L.Nodup) :
    ∀ (ds : List (Address × Int)), (∀ x ∈ ds, x.1 ∈ L) →
      (L.map (netDelta ds)).sum = (ds.map (·.2)).sum
  | [], _ => by
    have : ∀ o ∈ L, netDelta [] o = 0 := fun _ _ => rfl
    rw [List.map_congr_left this]; exact sum_map_zero L
  | x :: ds, h => by
    have e : ∀ o ∈ L, netDelta (x :: ds) o = (if x.1 = o then x.2 else 0) + netDelta ds o :=
      fun o _ => netDelta_cons x ds o
    rw [List.map_congr_left e, sum_map_add' (fun o => if x.1 = o then x.2 else 0) (netDelta ds), sum_ite_eq _ _ L hL (h x List.mem_cons_self),
      sum_netDelta L hL ds (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    simp

theorem applyBalances_spec {m r : Map Address Nat} {ds : List (Address × Int)}
    (hn : m.keys.Nodup) (hp : ∀ e ∈ m, 0 < e.2) (h : applyBalances m ds = some r) :
    r.keys.Nodup ∧ (∀ e ∈ r, 0 < e.2) ∧ (r.total : Int) = m.total + (ds.map (·.2)).sum := by
  rw [applyBalances_eq] at h
  obtain ⟨r1, r2, r3⟩ := balFold_spec m ds _ m r (nodup_eraseDups _) hn hp (fun _ _ => rfl) h
  refine ⟨r1, r2, ?_⟩
  rw [r3, sum_netDelta _ (nodup_eraseDups _)]
  intro x hx
  rw [List.mem_eraseDups]
  exact List.mem_map_of_mem hx

/-! ## Block decomposition and totals -/

theorem applyBlock_some {dir : String} {pr : Map ReceiptKey Address} {s s' : State} {b : Block}
    (h : applyBlock dir pr s b = some s') :
    accountActionsValid b.actions = true ∧
    totalCredits b.actions + totalDeposited b.actions ≤
      totalDebits b.actions + totalWithdrawn b.actions ∧
    ∃ afterW, applyWithdrawals dir pr s.deposits b.actions = some afterW ∧
      applyDeposits afterW b.actions = some s'.deposits ∧
      applyReceipts s.receipts b.actions = some s'.receipts ∧
      applyBalances s.balances (accountActions b.actions ++ coinbase b) = some s'.balances := by
  unfold applyBlock at h
  by_cases h1 : accountActionsValid b.actions = true
  · by_cases h2 : totalCredits b.actions + totalDeposited b.actions ≤
        totalDebits b.actions + totalWithdrawn b.actions
    · simp only [h1, h2, guard, ite_true] at h
      refine ⟨h1, h2, ?_⟩
      cases hw : applyWithdrawals dir pr s.deposits b.actions with
      | none => simp [hw] at h
      | some afterW =>
        cases hd : applyDeposits afterW b.actions with
        | none => simp [hw, hd] at h
        | some d =>
          cases hr : applyReceipts s.receipts b.actions with
          | none => simp [hw, hr] at h
          | some rc =>
            cases hb : applyBalances s.balances (accountActions b.actions ++ coinbase b) with
            | none => simp [hw, hr, hb] at h
            | some bl =>
              simp [hw, hd, hr, hb] at h
              subst h
              refine ⟨afterW, rfl, ?_, ?_, ?_⟩ <;> first | rfl | assumption
    · simp [h1, h2, guard, failure, Option.bind] at h
  · simp [h1, guard, failure, Option.bind] at h

theorem sum_accountActions (as : List Action) :
    ((accountActions as).map (·.2)).sum = (totalCredits as : Int) - totalDebits as := by
  induction as with
  | nil => simp [accountActions, totalCredits, totalDebits]
  | cons a t ih =>
    cases a with
    | account o d =>
      simp only [accountActions, totalCredits, totalDebits, List.map_cons, List.sum_cons] at ih ⊢
      have := Int.toNat_sub_toNat_neg d
      push_cast; omega
    | receipt w n dm amt d =>
      simp only [accountActions, totalCredits, totalDebits, List.map_cons, List.sum_cons] at ih ⊢
      push_cast
      simp
      omega
    | _ => simpa [accountActions, totalCredits, totalDebits] using ih

end Lattice
