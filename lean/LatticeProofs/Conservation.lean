import LatticeProofs.Model
import LatticeProofs.Lemmas

/-!
# Value conservation (spec §8.2, §8.3, §12.2, §12.4)

The statements below are the specification; the proofs only establish them.
-/

namespace Lattice

variable {dir : String} {pr : Map ReceiptKey Address} {s s' : State} {b : Block}

/-! ## Well-formedness is preserved -/

theorem applyBlock_wf (hs : s.WF) (h : applyBlock dir pr s b = some s') : s'.WF := by
  obtain ⟨_, _, afterW, hw, hd, hr, hb⟩ := applyBlock_some h
  obtain ⟨w1, -⟩ := applyWithdrawals_spec _ _ _ hs.depositsNodup hw
  obtain ⟨d1, -⟩ := applyDeposits_spec _ _ _ w1 hd
  obtain ⟨r1, -⟩ := applyReceipts_spec _ _ _ hr
  obtain ⟨b1, b2, -⟩ := applyBalances_spec hs.balancesNodup hs.balancesPos hb
  exact ⟨b1, d1, r1 hs.receiptsNodup, b2⟩

/-- §6.2: every balance a valid block leaves fits a `UInt64`. -/
theorem balances_fit (h : applyBlock dir pr s b = some s') :
    ∀ e ∈ s'.balances, e.2 ≤ uint64Max :=
  (applyBlock_fits h).2

/-- §5.2 step 11: a valid block's coinbase credit fits an `Int64`. -/
theorem coinbase_fits (h : applyBlock dir pr s b = some s') (hr : b.recipient = some r) :
    (b.reward : Int) + fee b.actions ≤ int64Max := by
  have := (applyBlock_fits h).1
  simpa [coinbaseFits, hr] using this

/-! ## Per-block conservation (§8.2) -/

/-- No value creation: a valid block's fee is never negative. -/
theorem fee_nonneg (h : applyBlock dir pr s b = some s') : 0 ≤ fee b.actions := by
  obtain ⟨_, hf, -⟩ := applyBlock_some h
  unfold fee
  omega

/-- §8.2, with a recipient: spendable supply changes by exactly
`reward(i) + totalWithdrawn - totalDeposited`. -/
theorem spendable_with_recipient (hs : s.WF) (h : applyBlock dir pr s b = some s')
    (hr : b.recipient = some r) :
    (s'.spendable : Int) =
      s.spendable + b.reward + totalWithdrawn b.actions - totalDeposited b.actions := by
  obtain ⟨_, _, afterW, hw, hd, hr', hb⟩ := applyBlock_some h
  obtain ⟨-, -, b3⟩ := applyBalances_spec hs.balancesNodup hs.balancesPos hb
  unfold State.spendable
  rw [b3, List.map_append, List.sum_append, sum_accountActions]
  simp only [coinbase, hr, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fee]
  omega

/-- §8.2, without a recipient: `totalWithdrawn - totalDeposited - F`; fees burn. -/
theorem spendable_without_recipient (hs : s.WF) (h : applyBlock dir pr s b = some s')
    (hr : b.recipient = none) :
    (s'.spendable : Int) =
      s.spendable + totalWithdrawn b.actions - totalDeposited b.actions - fee b.actions := by
  obtain ⟨_, _, afterW, hw, hd, hr', hb⟩ := applyBlock_some h
  obtain ⟨-, -, b3⟩ := applyBalances_spec hs.balancesNodup hs.balancesPos hb
  unfold State.spendable
  rw [b3, List.map_append, List.sum_append, sum_accountActions]
  simp only [coinbase, hr, List.map_nil, List.sum_nil, fee]
  omega

/-- Deposits lock exactly what they deposit; withdrawals release exactly what
they withdraw. -/
theorem locked_change (hs : s.WF) (h : applyBlock dir pr s b = some s') :
    (s'.locked : Int) = s.locked + totalDeposited b.actions - totalWithdrawn b.actions := by
  obtain ⟨_, _, afterW, hw, hd, -⟩ := applyBlock_some h
  obtain ⟨w1, w2, -⟩ := applyWithdrawals_spec _ _ _ hs.depositsNodup hw
  obtain ⟨-, d2, -⟩ := applyDeposits_spec _ _ _ w1 hd
  unfold State.locked
  omega

/-- Spendable plus locked value grows by exactly the reward with a recipient. -/
theorem value_with_recipient (hs : s.WF) (h : applyBlock dir pr s b = some s')
    (hr : b.recipient = some r) :
    (s'.spendable + s'.locked : Int) = s.spendable + s.locked + b.reward := by
  have h1 := spendable_with_recipient hs h hr
  have h2 := locked_change hs h
  push_cast
  omega

/-- Spendable plus locked value shrinks by exactly the burned fee without one. -/
theorem value_without_recipient (hs : s.WF) (h : applyBlock dir pr s b = some s')
    (hr : b.recipient = none) :
    (s'.spendable + s'.locked : Int) = s.spendable + s.locked - fee b.actions := by
  have h1 := spendable_without_recipient hs h hr
  have h2 := locked_change hs h
  push_cast
  omega

/-- §12.2 over a chain segment: total value moves only by issued rewards and
burned fees. -/
theorem value_chain (hs : s.WF) {bs : List (Map ReceiptKey Address × Block)}
    (h : applyChain dir s bs = some s') :
    (s'.spendable + s'.locked : Int) = s.spendable + s.locked + segmentIssuance bs := by
  induction bs generalizing s with
  | nil =>
    simp [applyChain] at h
    subst h
    simp [segmentIssuance]
  | cons x bs ih =>
    obtain ⟨p, b⟩ := x
    simp only [applyChain] at h
    cases hb : applyBlock dir p s b with
    | none => simp [hb] at h
    | some s1 =>
      simp only [hb, Option.bind_eq_bind, Option.bind_some] at h
      have hwf := applyBlock_wf hs hb
      have := ih hwf h
      simp only [segmentIssuance]
      cases hr : b.recipient with
      | some r =>
        have := value_with_recipient hs hb hr
        simp only at *
        push_cast at *
        omega
      | none =>
        have := value_without_recipient hs hb hr
        simp only at *
        push_cast at *
        omega

/-! ## Deposits and withdrawals (§8.3, §12.4) -/

/-- §12.4.3-5, §8.1 phase 3: every withdrawal in a valid block withdraws
exactly the nonzero amount its deposit holds in `prevState`, and the
matching receipt in `parentState` names its withdrawer. -/
theorem withdrawal_authorized (hs : s.WF) (h : applyBlock dir pr s b = some s')
    (hw : Action.withdrawal w n dm amtD amtW ∈ b.actions) :
    s.deposits.get? ⟨dm, amtD, n⟩ = some amtW ∧ amtW ≠ 0 ∧
      pr.get? ⟨dir, dm, amtD, n⟩ = some w := by
  obtain ⟨_, _, afterW, hw', -⟩ := applyBlock_some h
  obtain ⟨-, -, -, -, w5⟩ := applyWithdrawals_spec _ _ _ hs.depositsNodup hw'
  obtain ⟨q1, q2, q3, -⟩ := w5 w n dm amtD amtW hw
  exact ⟨q1, q2, q3⟩

/-- §12.4.6: a withdrawn deposit becomes the permanent spent marker. -/
theorem withdrawal_spends (hs : s.WF) (h : applyBlock dir pr s b = some s')
    (hw : Action.withdrawal w n dm amtD amtW ∈ b.actions) :
    s'.deposits.get? ⟨dm, amtD, n⟩ = some 0 := by
  obtain ⟨_, _, afterW, hw', hd, -⟩ := applyBlock_some h
  obtain ⟨w1, -, -, -, w5⟩ := applyWithdrawals_spec _ _ _ hs.depositsNodup hw'
  obtain ⟨-, -, d3, -⟩ := applyDeposits_spec _ _ _ w1 hd
  exact d3 _ _ (w5 w n dm amtD amtW hw).2.2.2

/-- §8.3 no double withdrawal, no recreated deposit: no valid block deposits
or withdraws a spent key. -/
theorem spent_is_final (hs : s.WF) (hk : s.deposits.get? k = some 0)
    (ht : ∃ a ∈ b.actions, touchesDeposit k a = true) :
    applyBlock dir pr s b = none := by
  cases h : applyBlock dir pr s b with
  | none => rfl
  | some s' =>
    exfalso
    obtain ⟨_, _, afterW, hw', hd, -⟩ := applyBlock_some h
    obtain ⟨w1, -, w3, -, w5⟩ := applyWithdrawals_spec _ _ _ hs.depositsNodup hw'
    obtain ⟨-, -, -, d4⟩ := applyDeposits_spec _ _ _ w1 hd
    obtain ⟨a, ha, ht⟩ := ht
    cases a with
    | deposit n dm amtD amt =>
      simp [touchesDeposit] at ht
      subst ht
      have := d4 n dm amtD amt ha
      rw [w3 _ hk] at this
      cases this
    | withdrawal w n dm amtD amtW =>
      simp [touchesDeposit] at ht
      subst ht
      obtain ⟨q1, q2, -⟩ := w5 w n dm amtD amtW ha
      rw [hk] at q1
      cases q1
      exact q2 rfl
    | _ => simp [touchesDeposit] at ht

/-- The spent marker persists through every later valid block. -/
theorem spent_persists (hs : s.WF) (hk : s.deposits.get? k = some 0)
    (h : applyBlock dir pr s b = some s') : s'.deposits.get? k = some 0 := by
  obtain ⟨_, _, afterW, hw', hd, -⟩ := applyBlock_some h
  obtain ⟨w1, -, w3, -⟩ := applyWithdrawals_spec _ _ _ hs.depositsNodup hw'
  obtain ⟨-, -, d3, -⟩ := applyDeposits_spec _ _ _ w1 hd
  exact d3 _ _ (w3 _ hk)

/-- §12.4.1: a valid block never deposits at a key already in deposit state. -/
theorem deposit_fresh (hs : s.WF) (h : applyBlock dir pr s b = some s')
    (hd : Action.deposit n dm amtD amt ∈ b.actions) :
    s.deposits.get? ⟨dm, amtD, n⟩ = none := by
  obtain ⟨_, _, afterW, hw', hd', -⟩ := applyBlock_some h
  obtain ⟨w1, -, -, w4, -⟩ := applyWithdrawals_spec _ _ _ hs.depositsNodup hw'
  obtain ⟨-, -, -, d4⟩ := applyDeposits_spec _ _ _ w1 hd'
  exact w4 _ (d4 n dm amtD amt hd)

/-! ## Receipts (§6.5, §12.4.2) -/

/-- §12.4.2: a valid block never inserts a receipt key already present. -/
theorem receipt_fresh (hs : s.WF) (h : applyBlock dir pr s b = some s')
    (hr : a ∈ b.actions) (hk : receiptKeyOf a = some k) :
    s.receipts.get? k = none := by
  obtain ⟨_, _, afterW, -, -, hr', -⟩ := applyBlock_some h
  exact (applyReceipts_spec _ _ _ hr').2.1 a k hr hk

/-- Every receipt in the post-state was already there or was inserted by a
receipt action of this block (which debited its withdrawer, §6.5). -/
theorem receipt_provenance (h : applyBlock dir pr s b = some s')
    (hk : (s'.receipts.get? k).isSome) :
    (s.receipts.get? k).isSome ∨ ∃ a ∈ b.actions, receiptKeyOf a = some k := by
  obtain ⟨_, _, afterW, -, -, hr', -⟩ := applyBlock_some h
  exact (applyReceipts_spec _ _ _ hr').2.2 k hk

end Lattice
