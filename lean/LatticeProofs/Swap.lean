import LatticeProofs.Model
import LatticeProofs.Lemmas
import LatticeProofs.Conservation

/-!
# Cross-chain swap atomicity (spec §6.4, §6.5, §8.1, §12.4)

A swap spans two chains. On the child chain at directory `dir`, a deposit
locks `amountDeposited` at `DepositKey(demander, amountDemanded, nonce)`. On
the parent chain, a receipt `(withdrawer, nonce, demander, amountDemanded,
dir)` is inserted at its `ReceiptKey`, debiting the withdrawer and crediting
the demander `amountDemanded`. Back on the child, a withdrawal needs that
receipt in its `parentState`, naming the withdrawer, and turns the deposit
into the spent marker.

Atomicity here: every withdrawal in a valid child run is backed by a receipt
in a valid block of the parent run that paid the demander, and by a deposit
in a strictly earlier child block; each deposit is released at most once,
and each receipt is recorded at most once.

The child run's `parentState`s are assumed to be states the parent run
reached (`hpar` below); that anchors are valid is the hierarchy model's
concern (TLA+), not this file's.
-/

namespace Lattice

/-! ## Keys a run inserts or releases -/

/-- The deposit key a withdrawal action releases. -/
def withdrawalKeyOf : Action → Option DepositKey
  | .withdrawal _ n dm amtD _ => some ⟨dm, amtD, n⟩
  | _ => none

/-- The receipt key each receipt action inserts, one entry per action. -/
def receiptKeys (as : List Action) : List ReceiptKey := as.filterMap receiptKeyOf

/-- The deposit key each withdrawal action releases, one entry per action. -/
def withdrawalKeys (as : List Action) : List DepositKey := as.filterMap withdrawalKeyOf

/-- Every receipt key a run inserts, one entry per receipt action. -/
def runReceiptKeys (bs : List (Map ReceiptKey Address × Block)) : List ReceiptKey :=
  bs.flatMap fun x => receiptKeys x.2.actions

/-- Every deposit key a run releases, one entry per withdrawal action. -/
def runWithdrawalKeys (bs : List (Map ReceiptKey Address × Block)) : List DepositKey :=
  bs.flatMap fun x => withdrawalKeys x.2.actions

/-- The parent receipt key a withdrawal of deposit key `k` on the chain at
`dir` consumes (§8.1 phase 3). -/
def consumedReceipt (dir : String) (k : DepositKey) : ReceiptKey :=
  ⟨dir, k.demander, k.amountDemanded, k.nonce⟩

/-! ## Sub-state lemmas -/

theorem applyReceipts_value :
    ∀ (as : List Action) (m m' : Map ReceiptKey Address), applyReceipts m as = some m' →
      ∀ k w, m'.get? k = some w → m.get? k = some w ∨
        ∃ n dm amtD d, Action.receipt w n dm amtD d ∈ as ∧ k = ⟨d, dm, amtD, n⟩
  | [], m, m', h, k, w, hk => by
    simp [applyReceipts] at h
    subst h
    exact Or.inl hk
  | a :: as, m, m', h, k, w, hk => by
    cases a with
    | receipt w0 n0 dm0 amtD0 d0 =>
      simp only [applyReceipts] at h
      split at h
      · rcases applyReceipts_value as _ m' h k w hk with q | ⟨n, dm, amtD, d, hm, he⟩
        · rw [Map.get?_set] at q
          split at q
          · rename_i hkk
            obtain rfl := Option.some.inj q
            exact Or.inr ⟨n0, dm0, amtD0, d0, List.mem_cons_self, hkk⟩
          · exact Or.inl q
        · exact Or.inr ⟨n, dm, amtD, d, List.mem_cons_of_mem _ hm, he⟩
      · simp at h
    | _ =>
      simp only [applyReceipts] at h
      rcases applyReceipts_value as m m' h k w hk with q | ⟨n, dm, amtD, d, hm, he⟩
      · exact Or.inl q
      · exact Or.inr ⟨n, dm, amtD, d, List.mem_cons_of_mem _ hm, he⟩

theorem applyReceipts_keep :
    ∀ (as : List Action) (m m' : Map ReceiptKey Address), applyReceipts m as = some m' →
      ∀ k w, m.get? k = some w → m'.get? k = some w
  | [], m, m', h, k, w, hk => by
    simp [applyReceipts] at h
    subst h
    exact hk
  | a :: as, m, m', h, k, w, hk => by
    cases a with
    | receipt w0 n0 dm0 amtD0 d0 =>
      simp only [applyReceipts] at h
      split at h
      · rename_i hc
        apply applyReceipts_keep as _ m' h k w
        rw [Map.get?_set]
        split
        · rename_i hkk; subst hkk; rw [hc.1] at hk; cases hk
        · exact hk
      · simp at h
    | _ =>
      simp only [applyReceipts] at h
      exact applyReceipts_keep as m m' h k w hk

theorem applyReceipts_keys :
    ∀ (as : List Action) (m m' : Map ReceiptKey Address), applyReceipts m as = some m' →
      (receiptKeys as).Nodup ∧
      ∀ k ∈ receiptKeys as, m.get? k = none ∧ (m'.get? k).isSome
  | [], m, m', h => by simp [receiptKeys]
  | a :: as, m, m', h => by
    cases a with
    | receipt w0 n0 dm0 amtD0 d0 =>
      simp only [applyReceipts] at h
      split at h
      · rename_i hc
        obtain ⟨r1, r2⟩ := applyReceipts_keys as _ m' h
        have hself := applyReceipts_keep as _ m' h _ w0 (Map.get?_set_self _ _ _)
        have htail : ∀ k ∈ receiptKeys as, k ≠ ⟨d0, dm0, amtD0, n0⟩ ∧ m.get? k = none := by
          intro k hk
          have q := (r2 k hk).1
          rw [Map.get?_set] at q
          split at q
          · simp at q
          · rename_i hne; exact ⟨hne, q⟩
        show (_ :: receiptKeys as).Nodup ∧ _
        refine ⟨List.nodup_cons.mpr ⟨fun hm => (htail _ hm).1 rfl, r1⟩, ?_⟩
        intro k hk
        change k ∈ _ :: receiptKeys as at hk
        rw [List.mem_cons] at hk
        rcases hk with rfl | hk
        · exact ⟨hc.1, by simp [hself]⟩
        · exact ⟨(htail k hk).2, (r2 k hk).2⟩
      · simp at h
    | _ =>
      simp only [applyReceipts] at h
      exact applyReceipts_keys as m m' h

theorem applyWithdrawals_value {dir : String} {pr : Map ReceiptKey Address} :
    ∀ (as : List Action) (m m' : Map DepositKey Nat),
      applyWithdrawals dir pr m as = some m' →
      ∀ k v, m'.get? k = some v → v ≠ 0 → m.get? k = some v
  | [], m, m', h, k, v, hk, _ => by
    simp [applyWithdrawals] at h
    subst h
    exact hk
  | a :: as, m, m', h, k, v, hk, hv => by
    cases a with
    | withdrawal w0 n0 dm0 amtD0 amtW0 =>
      simp only [applyWithdrawals] at h
      split at h
      · have q := applyWithdrawals_value as _ m' h k v hk hv
        rw [Map.get?_set] at q
        split at q
        · obtain rfl := Option.some.inj q; exact absurd rfl hv
        · exact q
      · simp at h
    | _ =>
      simp only [applyWithdrawals] at h
      exact applyWithdrawals_value as m m' h k v hk hv

theorem applyDeposits_value :
    ∀ (as : List Action) (m m' : Map DepositKey Nat), applyDeposits m as = some m' →
      ∀ k v, m'.get? k = some v → m.get? k = some v ∨
        ∃ n dm amtD, Action.deposit n dm amtD v ∈ as ∧ k = ⟨dm, amtD, n⟩
  | [], m, m', h, k, v, hk => by
    simp [applyDeposits] at h
    subst h
    exact Or.inl hk
  | a :: as, m, m', h, k, v, hk => by
    cases a with
    | deposit n0 dm0 amtD0 amt0 =>
      simp only [applyDeposits] at h
      split at h
      · rcases applyDeposits_value as _ m' h k v hk with q | ⟨n, dm, amtD, hm, he⟩
        · rw [Map.get?_set] at q
          split at q
          · rename_i hkk
            obtain rfl := Option.some.inj q
            exact Or.inr ⟨n0, dm0, amtD0, List.mem_cons_self, hkk⟩
          · exact Or.inl q
        · exact Or.inr ⟨n, dm, amtD, List.mem_cons_of_mem _ hm, he⟩
      · simp at h
    | _ =>
      simp only [applyDeposits] at h
      rcases applyDeposits_value as m m' h k v hk with q | ⟨n, dm, amtD, hm, he⟩
      · exact Or.inl q
      · exact Or.inr ⟨n, dm, amtD, List.mem_cons_of_mem _ hm, he⟩

theorem mem_withdrawalKeys {k : DepositKey} {as : List Action} (h : k ∈ withdrawalKeys as) :
    ∃ w n dm amtD amtW, Action.withdrawal w n dm amtD amtW ∈ as ∧ k = ⟨dm, amtD, n⟩ := by
  obtain ⟨a, ha, hk⟩ := List.mem_filterMap.mp h
  cases a with
  | withdrawal w n dm amtD amtW =>
    simp only [withdrawalKeyOf, Option.some.injEq] at hk
    exact ⟨w, n, dm, amtD, amtW, ha, hk.symm⟩
  | _ => simp [withdrawalKeyOf] at hk

theorem applyWithdrawals_keys {dir : String} {pr : Map ReceiptKey Address} :
    ∀ (as : List Action) (m m' : Map DepositKey Nat),
      m.keys.Nodup → applyWithdrawals dir pr m as = some m' → (withdrawalKeys as).Nodup
  | [], _, _, _, _ => by simp [withdrawalKeys]
  | a :: as, m, m', hn, h => by
    cases a with
    | withdrawal w0 n0 dm0 amtD0 amtW0 =>
      simp only [applyWithdrawals] at h
      split at h
      · have hn' := Map.nodup_set hn ⟨dm0, amtD0, n0⟩ 0
        have r1 := applyWithdrawals_keys as _ m' hn' h
        obtain ⟨-, -, -, -, r5⟩ := applyWithdrawals_spec as _ m' hn' h
        show (_ :: withdrawalKeys as).Nodup
        refine List.nodup_cons.mpr ⟨fun hm => ?_, r1⟩
        obtain ⟨w, n, dm, amtD, amtW, hw, he⟩ := mem_withdrawalKeys hm
        obtain ⟨q1, q2, -⟩ := r5 w n dm amtD amtW hw
        rw [← he, Map.get?_set_self] at q1
        exact q2 (Option.some.inj q1).symm
      · simp at h
    | _ =>
      simp only [applyWithdrawals] at h
      exact applyWithdrawals_keys as m m' hn h

/-- The two account actions a receipt derives (§6.5). -/
theorem receipt_pays {w dm : Address} {n amt : Nat} {d : String} :
    ∀ {as : List Action}, Action.receipt w n dm amt d ∈ as →
      (w, -(amt : Int)) ∈ accountActions as ∧ (dm, (amt : Int)) ∈ accountActions as
  | [], h => by simp at h
  | a :: as, h => by
    rw [List.mem_cons] at h
    rcases h with rfl | h
    · simp [accountActions]
    · have ih := receipt_pays h
      cases a <;> simp [accountActions, ih]

/-! ## Block level -/

variable {dir : String} {pr : Map ReceiptKey Address} {s s' : State} {b : Block}

/-- Every receipt entry after a valid block was already there with the same
withdrawer, or was inserted by a receipt action of the block naming it. -/
theorem receipt_value_provenance (h : applyBlock dir pr s b = some s')
    (hk : s'.receipts.get? k = some w) :
    s.receipts.get? k = some w ∨
      ∃ n dm amtD d, Action.receipt w n dm amtD d ∈ b.actions ∧ k = ⟨d, dm, amtD, n⟩ := by
  obtain ⟨_, _, _, -, -, hr, -⟩ := applyBlock_some h
  exact applyReceipts_value _ _ _ hr k w hk

/-- Every live (nonzero) deposit after a valid block was already there with
the same amount, or was inserted by a deposit action of the block. -/
theorem deposit_value_provenance (h : applyBlock dir pr s b = some s')
    (hk : s'.deposits.get? k = some v) (hv : v ≠ 0) :
    s.deposits.get? k = some v ∨
      ∃ n dm amtD, Action.deposit n dm amtD v ∈ b.actions ∧ k = ⟨dm, amtD, n⟩ := by
  obtain ⟨_, _, afterW, hw, hd, -⟩ := applyBlock_some h
  rcases applyDeposits_value _ _ _ hd k v hk with q | q
  · exact Or.inl (applyWithdrawals_value _ _ _ hw k v q hv)
  · exact Or.inr q

/-! ## Chain level -/

theorem applyChain_cons_some {bs : List (Map ReceiptKey Address × Block)}
    (h : applyChain dir s ((pr, b) :: bs) = some s') :
    ∃ s1, applyBlock dir pr s b = some s1 ∧ applyChain dir s1 bs = some s' := by
  simp only [applyChain] at h
  cases hb : applyBlock dir pr s b with
  | none => simp [hb] at h
  | some s1 =>
    simp only [hb, Option.bind_eq_bind, Option.bind_some] at h
    exact ⟨s1, rfl, h⟩

theorem applyChain_wf {bs : List (Map ReceiptKey Address × Block)} (hs : s.WF)
    (h : applyChain dir s bs = some s') : s'.WF := by
  induction bs generalizing s with
  | nil => simp [applyChain] at h; subst h; exact hs
  | cons x bs ih =>
    obtain ⟨p, b⟩ := x
    obtain ⟨s1, hb, h⟩ := applyChain_cons_some h
    exact ih (applyBlock_wf hs hb) h

/-- The `i`-th block of a valid run applies validly to the state its prefix
reaches. -/
theorem applyChain_prefix {bs : List (Map ReceiptKey Address × Block)}
    (h : applyChain dir s bs = some s') (i : Nat) (hi : i < bs.length) :
    ∃ si si', applyChain dir s (bs.take i) = some si ∧
      applyBlock dir bs[i].1 si bs[i].2 = some si' := by
  induction bs generalizing s i with
  | nil => simp at hi
  | cons x bs ih =>
    obtain ⟨p, b⟩ := x
    obtain ⟨s1, hb, h⟩ := applyChain_cons_some h
    cases i with
    | zero => exact ⟨s, s1, rfl, hb⟩
    | succ i =>
      obtain ⟨si, si', h1, h2⟩ := ih h i (by simpa using hi)
      refine ⟨si, si', ?_, by simpa using h2⟩
      simp [applyChain, hb, h1]

theorem receipt_run_provenance {bs : List (Map ReceiptKey Address × Block)}
    (h : applyChain dir s bs = some s') (hk : s'.receipts.get? k = some w) :
    s.receipts.get? k = some w ∨ ∃ i, ∃ hi : i < bs.length, ∃ n dm amtD d,
      Action.receipt w n dm amtD d ∈ bs[i].2.actions ∧ k = ⟨d, dm, amtD, n⟩ := by
  induction bs generalizing s with
  | nil => simp [applyChain] at h; subst h; exact Or.inl hk
  | cons x bs ih =>
    obtain ⟨p, b⟩ := x
    obtain ⟨s1, hb, h⟩ := applyChain_cons_some h
    rcases ih h with q | ⟨i, hi, n, dm, amtD, d, hm, he⟩
    · rcases receipt_value_provenance hb q with q | ⟨n, dm, amtD, d, hm, he⟩
      · exact Or.inl q
      · exact Or.inr ⟨0, by simp, n, dm, amtD, d, hm, he⟩
    · exact Or.inr ⟨i + 1, by simpa using hi, n, dm, amtD, d, by simpa using hm, he⟩

theorem deposit_run_provenance {bs : List (Map ReceiptKey Address × Block)}
    (h : applyChain dir s bs = some s') (hk : s'.deposits.get? k = some v) (hv : v ≠ 0) :
    s.deposits.get? k = some v ∨ ∃ i, ∃ hi : i < bs.length, ∃ n dm amtD,
      Action.deposit n dm amtD v ∈ bs[i].2.actions ∧ k = ⟨dm, amtD, n⟩ := by
  induction bs generalizing s with
  | nil => simp [applyChain] at h; subst h; exact Or.inl hk
  | cons x bs ih =>
    obtain ⟨p, b⟩ := x
    obtain ⟨s1, hb, h⟩ := applyChain_cons_some h
    rcases ih h with q | ⟨i, hi, n, dm, amtD, hm, he⟩
    · rcases deposit_value_provenance hb q hv with q | ⟨n, dm, amtD, hm, he⟩
      · exact Or.inl q
      · exact Or.inr ⟨0, by simp, n, dm, amtD, hm, he⟩
    · exact Or.inr ⟨i + 1, by simpa using hi, n, dm, amtD, by simpa using hm, he⟩

/-- From empty receipt state, every receipt a valid run ends with was
inserted, naming its withdrawer, by a receipt action of one of its blocks. -/
theorem receipt_chain_provenance {bs : List (Map ReceiptKey Address × Block)}
    (h0 : s.receipts = []) (h : applyChain dir s bs = some s')
    (hk : s'.receipts.get? k = some w) :
    ∃ i, ∃ hi : i < bs.length, ∃ n dm amtD d,
      Action.receipt w n dm amtD d ∈ bs[i].2.actions ∧ k = ⟨d, dm, amtD, n⟩ := by
  rcases receipt_run_provenance h hk with q | q
  · rw [h0] at q; cases q
  · exact q

/-- From empty deposit state, every live deposit a valid run ends with was
inserted, with that amount, by a deposit action of one of its blocks. -/
theorem deposit_chain_provenance {bs : List (Map ReceiptKey Address × Block)}
    (h0 : s.deposits = []) (h : applyChain dir s bs = some s')
    (hk : s'.deposits.get? k = some v) (hv : v ≠ 0) :
    ∃ i, ∃ hi : i < bs.length, ∃ n dm amtD,
      Action.deposit n dm amtD v ∈ bs[i].2.actions ∧ k = ⟨dm, amtD, n⟩ := by
  rcases deposit_run_provenance h hk hv with q | q
  · rw [h0] at q; cases q
  · exact q

/-! ## Atomicity -/

/-- §8.1 phase 3, §12.4: in a valid child run (at directory `dir`, from a
well-formed state with no deposits) whose every `parentState` is a state the
valid parent run (from no receipts) reached, every withdrawal is backed by
(a) a receipt action, naming the withdrawer, in a valid block of the parent
run, which debited the withdrawer and credited the demander `amountDemanded`;
and (b) a deposit of exactly the withdrawn amount at the same key in a
strictly earlier child block. -/
theorem swap_atomic {pdir : String} {p0 ps c0 cs : State}
    {pbs cbs : List (Map ReceiptKey Address × Block)}
    (hp : applyChain pdir p0 pbs = some ps) (hp0 : p0.receipts = [])
    (hc : applyChain dir c0 cbs = some cs) (hc0 : c0.WF) (hc0d : c0.deposits = [])
    (hpar : ∀ x ∈ cbs, ∃ j ps', applyChain pdir p0 (pbs.take j) = some ps' ∧
      x.1 = ps'.receipts)
    (i : Nat) (hi : i < cbs.length)
    (hw : Action.withdrawal w n dm amtD amtW ∈ cbs[i].2.actions) :
    (∃ j, ∃ hj : j < pbs.length,
      Action.receipt w n dm amtD dir ∈ pbs[j].2.actions ∧
      (w, -(amtD : Int)) ∈ accountActions pbs[j].2.actions ∧
      (dm, (amtD : Int)) ∈ accountActions pbs[j].2.actions ∧
      ∃ pj pj', applyChain pdir p0 (pbs.take j) = some pj ∧
        applyBlock pdir pbs[j].1 pj pbs[j].2 = some pj') ∧
    (∃ j, ∃ _ : j < i, Action.deposit n dm amtD amtW ∈ cbs[j].2.actions) := by
  obtain ⟨ci, ci', hci, hbi⟩ := applyChain_prefix hc i hi
  obtain ⟨q1, q2, q3⟩ := withdrawal_authorized (applyChain_wf hc0 hci) hbi hw
  constructor
  · obtain ⟨j, ps', hj, hpr⟩ := hpar _ (List.getElem_mem hi)
    rw [hpr] at q3
    obtain ⟨l, hl, n', dm', amtD', d, hm, he⟩ := receipt_chain_provenance hp0 hj q3
    simp only [ReceiptKey.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl, rfl⟩ := he
    have hl' : l < pbs.length := by rw [List.length_take] at hl; omega
    rw [List.getElem_take] at hm
    obtain ⟨pa, pb⟩ := receipt_pays hm
    exact ⟨l, hl', hm, pa, pb, applyChain_prefix hp l hl'⟩
  · obtain ⟨j, hj, n', dm', amtD', hm, he⟩ := deposit_chain_provenance hc0d hci q1 q2
    simp only [DepositKey.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    have hj' : j < i := by rw [List.length_take] at hj; omega
    rw [List.getElem_take] at hm
    exact ⟨j, hj', hm⟩

/-! ## Uniqueness -/

theorem spent_blocks_withdrawals {bs : List (Map ReceiptKey Address × Block)}
    (hs : s.WF) (hk : s.deposits.get? k = some 0) (h : applyChain dir s bs = some s') :
    k ∉ runWithdrawalKeys bs := by
  induction bs generalizing s with
  | nil => simp [runWithdrawalKeys]
  | cons x bs ih =>
    obtain ⟨p, b⟩ := x
    obtain ⟨s1, hb, h⟩ := applyChain_cons_some h
    simp only [runWithdrawalKeys, List.flatMap_cons, List.mem_append, not_or]
    refine ⟨fun hm => ?_, ih (applyBlock_wf hs hb) (spent_persists hs hk hb) h⟩
    obtain ⟨w, n, dm, amtD, amtW, hw, rfl⟩ := mem_withdrawalKeys hm
    have := spent_is_final (dir := dir) (pr := p) hs hk ⟨_, hw, by simp [touchesDeposit]⟩
    rw [hb] at this
    cases this

/-- §8.3: across a valid run from a well-formed state, no two withdrawal
actions (in one block or in different blocks) release the same deposit key:
each deposit is released at most once. -/
theorem withdrawal_once {bs : List (Map ReceiptKey Address × Block)}
    (hs : s.WF) (h : applyChain dir s bs = some s') : (runWithdrawalKeys bs).Nodup := by
  induction bs generalizing s with
  | nil => simp [runWithdrawalKeys]
  | cons x bs ih =>
    obtain ⟨p, b⟩ := x
    obtain ⟨s1, hb, h⟩ := applyChain_cons_some h
    have hs1 := applyBlock_wf hs hb
    obtain ⟨_, _, afterW, hw, -⟩ := applyBlock_some hb
    show (withdrawalKeys b.actions ++ runWithdrawalKeys bs).Nodup
    refine List.nodup_append.mpr
      ⟨applyWithdrawals_keys _ _ _ hs.depositsNodup hw, ih hs1 h, ?_⟩
    intro k hk k' hk' he
    subst he
    obtain ⟨w, n, dm, amtD, amtW, hwm, rfl⟩ := mem_withdrawalKeys hk
    exact spent_blocks_withdrawals hs1 (withdrawal_spends hs hb hwm) h hk'

theorem present_blocks_receipts {bs : List (Map ReceiptKey Address × Block)}
    (hk : s.receipts.get? k = some w) (h : applyChain dir s bs = some s') :
    k ∉ runReceiptKeys bs := by
  induction bs generalizing s with
  | nil => simp [runReceiptKeys]
  | cons x bs ih =>
    obtain ⟨p, b⟩ := x
    obtain ⟨s1, hb, h⟩ := applyChain_cons_some h
    obtain ⟨_, _, _, -, -, hr, -⟩ := applyBlock_some hb
    simp only [runReceiptKeys, List.flatMap_cons, List.mem_append, not_or]
    refine ⟨fun hm => ?_, ih (applyReceipts_keep _ _ _ hr k w hk) h⟩
    have := ((applyReceipts_keys _ _ _ hr).2 k hm).1
    rw [hk] at this
    cases this

/-- §6.5, §12.4.2: across a valid run, no two receipt actions (in one block
or in different blocks) insert the same receipt key: each payment is
recorded at most once. -/
theorem receipt_once {bs : List (Map ReceiptKey Address × Block)}
    (h : applyChain dir s bs = some s') : (runReceiptKeys bs).Nodup := by
  induction bs generalizing s with
  | nil => simp [runReceiptKeys]
  | cons x bs ih =>
    obtain ⟨p, b⟩ := x
    obtain ⟨s1, hb, h⟩ := applyChain_cons_some h
    obtain ⟨_, _, _, -, -, hr, -⟩ := applyBlock_some hb
    obtain ⟨r1, r2⟩ := applyReceipts_keys _ _ _ hr
    show (receiptKeys b.actions ++ runReceiptKeys bs).Nodup
    refine List.nodup_append.mpr ⟨r1, ih h, ?_⟩
    intro k hk k' hk' he
    subst he
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (r2 k hk).2
    exact present_blocks_receipts hw h hk'

theorem nodup_map_of_inj {α β : Type} {f : α → β} (hf : ∀ a b, f a = f b → a = b) :
    ∀ {l : List α}, l.Nodup → (l.map f).Nodup
  | [], _ => by simp
  | a :: l, h => by
    rw [List.nodup_cons] at h
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, nodup_map_of_inj hf h.2⟩
    obtain ⟨a', ha', he⟩ := List.mem_map.mp hm
    exact h.1 (hf _ _ he ▸ ha')

/-- Each parent receipt is consumed by at most one withdrawal across a valid
child run: a payment releases at most one deposit. -/
theorem payment_releases_once {bs : List (Map ReceiptKey Address × Block)}
    (hs : s.WF) (h : applyChain dir s bs = some s') :
    ((runWithdrawalKeys bs).map (consumedReceipt dir)).Nodup := by
  refine nodup_map_of_inj ?_ (withdrawal_once hs h)
  intro a b he
  simp only [consumedReceipt, ReceiptKey.mk.injEq] at he
  cases a; cases b
  simp_all

end Lattice
