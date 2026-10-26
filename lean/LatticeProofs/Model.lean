/-!
# Lattice value-bearing state transitions

A model of the parts of a block's state transition that move value, written
from the normative spec (Lattice `docs/spec.md`), not from the implementation:

* §6.2 account state: per-owner balances, deleted at zero;
* §6.4 deposit state: deposits by insertion, withdrawals to a permanent zero
  spent marker, withdrawals before deposits;
* §6.5 receipt state: receipts by insertion, deriving a debit of the
  withdrawer and a credit of the demander;
* §8.1 phase 3: a withdrawal needs the matching receipt in `parentState`;
* §8.2 the fee rule and the coinbase credit.

* the width bounds that decide validity: an account delta is an `Int64`
  other than `Int64.min` (§3.6), the coinbase credit fits a positive
  `Int64` (§5.2 step 11), and a balance fits a `UInt64` (§6.2).

Not modelled: general key-value actions and nonces (they move no value),
signatures, policies, state growth, the encoding bounds of the other action
fields (a value outside them cannot be written), and Merkle proofs (the maps
stand for the proven sub-states).
-/

namespace Lattice

abbrev Address := String

/-- §3.7 `DepositKey = demander / amountDemanded / nonce`. -/
structure DepositKey where
  demander : Address
  amountDemanded : Nat
  nonce : Nat
  deriving DecidableEq, Repr

/-- §3.7 `ReceiptKey = directory / demander / amountDemanded / nonce`. -/
structure ReceiptKey where
  directory : String
  demander : Address
  amountDemanded : Nat
  nonce : Nat
  deriving DecidableEq, Repr

/-- §3.6 the value-bearing action types. -/
inductive Action where
  | account (owner : Address) (delta : Int)
  | deposit (nonce : Nat) (demander : Address) (amountDemanded amountDeposited : Nat)
  | withdrawal (withdrawer : Address) (nonce : Nat) (demander : Address)
      (amountDemanded amountWithdrawn : Nat)
  | receipt (withdrawer : Address) (nonce : Nat) (demander : Address)
      (amountDemanded : Nat) (directory : String)
  deriving DecidableEq, Repr

/-- An association list standing for one proven sub-state. -/
abbrev Map (κ ν : Type) := List (κ × ν)

def Map.get? [DecidableEq κ] (m : Map κ ν) (k : κ) : Option ν :=
  (m.find? (·.1 == k)).map (·.2)

def Map.erase [DecidableEq κ] (m : Map κ ν) (k : κ) : Map κ ν :=
  m.filter (·.1 != k)

def Map.set [DecidableEq κ] (m : Map κ ν) (k : κ) (v : ν) : Map κ ν :=
  (k, v) :: m.erase k

def Map.keys (m : Map κ ν) : List κ := m.map (·.1)

def Map.total (m : Map κ Nat) : Nat := (m.map (·.2)).sum

structure State where
  /-- §6.2: an owner with a zero balance has no entry. -/
  balances : Map Address Nat
  /-- §6.4: `0` is the permanent spent marker. -/
  deposits : Map DepositKey Nat
  /-- §6.5: the withdrawer's key. -/
  receipts : Map ReceiptKey Address

/-- Distinct keys in every sub-state, and no zero balance entry. -/
structure State.WF (s : State) : Prop where
  balancesNodup : s.balances.keys.Nodup
  depositsNodup : s.deposits.keys.Nodup
  receiptsNodup : s.receipts.keys.Nodup
  balancesPos : ∀ e ∈ s.balances, 0 < e.2

/-- Spendable supply: deposit state counts as locked, not spendable (§8.2). -/
def State.spendable (s : State) : Nat := s.balances.total

/-- Value locked in live deposits; a spent marker locks nothing. -/
def State.locked (s : State) : Nat := s.deposits.total

structure Block where
  actions : List Action
  /-- `reward(i)`, the block subsidy (§10.1). -/
  reward : Nat
  /-- `nil` burns the coinbase (§8.2). -/
  recipient : Option Address

/-! ## Block totals (§8.2) -/

/-- Every account action of the block: explicit ones, and the debit and
credit each receipt derives (§6.5). -/
def accountActions : List Action → List (Address × Int)
  | [] => []
  | .account o d :: as => (o, d) :: accountActions as
  | .receipt w _ dm amt _ :: as =>
      (w, -(amt : Int)) :: (dm, (amt : Int)) :: accountActions as
  | _ :: as => accountActions as

def totalCredits (as : List Action) : Nat :=
  ((accountActions as).map fun e => e.2.toNat).sum

def totalDebits (as : List Action) : Nat :=
  ((accountActions as).map fun e => (-e.2).toNat).sum

def totalDeposited : List Action → Nat
  | [] => 0
  | .deposit _ _ _ amt :: as => amt + totalDeposited as
  | _ :: as => totalDeposited as

def totalWithdrawn : List Action → Nat
  | [] => 0
  | .withdrawal _ _ _ _ amt :: as => amt + totalWithdrawn as
  | _ :: as => totalWithdrawn as

/-- `F = totalDebits + totalWithdrawn - totalCredits - totalDeposited`. -/
def fee (as : List Action) : Int :=
  (totalDebits as : Int) + totalWithdrawn as - totalCredits as - totalDeposited as

/-- The largest `Int64` and `UInt64`. -/
def int64Max : Int := 2 ^ 63 - 1
def uint64Max : Nat := 2 ^ 64 - 1

/-- §3.6: `delta != 0`, and `delta` an `Int64` other than `Int64.min`. -/
def accountActionsValid : List Action → Bool
  | [] => true
  | .account _ d :: as =>
      d != 0 && decide (-int64Max ≤ d) && decide (d ≤ int64Max) && accountActionsValid as
  | _ :: as => accountActionsValid as

/-! ## Sub-state transitions -/

/-- §6.4 withdrawals, in order: the deposit must hold exactly the nonzero
`amountWithdrawn`, and `parentState.receiptState` must name the withdrawer
under this chain's directory (§8.1 phase 3).  It becomes the spent marker.
(§6.4 also asks a nonzero `amountDemanded`; no deposit has a zero demand, so
the deposit match already implies it.) -/
def applyWithdrawals (dir : String) (parentReceipts : Map ReceiptKey Address) :
    Map DepositKey Nat → List Action → Option (Map DepositKey Nat)
  | m, [] => some m
  | m, .withdrawal w n dm amtD amtW :: as =>
      let k : DepositKey := ⟨dm, amtD, n⟩
      if m.get? k = some amtW ∧ amtW ≠ 0 ∧
          parentReceipts.get? ⟨dir, dm, amtD, n⟩ = some w then
        applyWithdrawals dir parentReceipts (m.set k 0) as
      else none
  | m, _ :: as => applyWithdrawals dir parentReceipts m as

/-- §6.4 deposits, in order, after withdrawals: insertion of a nonzero
amount for a nonzero demand at an absent key. -/
def applyDeposits : Map DepositKey Nat → List Action → Option (Map DepositKey Nat)
  | m, [] => some m
  | m, .deposit n dm amtD amt :: as =>
      let k : DepositKey := ⟨dm, amtD, n⟩
      if m.get? k = none ∧ amt ≠ 0 ∧ amtD ≠ 0 then applyDeposits (m.set k amt) as
      else none
  | m, _ :: as => applyDeposits m as

/-- §6.5 receipts, in order: a nonzero `amountDemanded`, inserted at an
absent key. -/
def applyReceipts : Map ReceiptKey Address → List Action → Option (Map ReceiptKey Address)
  | m, [] => some m
  | m, .receipt w n dm amtD d :: as =>
      let k : ReceiptKey := ⟨d, dm, amtD, n⟩
      if m.get? k = none ∧ amtD ≠ 0 then applyReceipts (m.set k w) as else none
  | m, _ :: as => applyReceipts m as

/-- The net delta an owner receives from a list of account actions. -/
def netDelta (ds : List (Address × Int)) (o : Address) : Int :=
  ((ds.filter (·.1 == o)).map (·.2)).sum

/-- §6.2: every owner's balance moves by its net delta, so a payer that is
also credited nets through one balance; a negative result is invalid and a
zero result deletes the entry. -/
def applyBalances (m : Map Address Nat) (ds : List (Address × Int)) :
    Option (Map Address Nat) :=
  (ds.map (·.1)).eraseDups.foldlM
    (fun acc o =>
      let v : Int := ((m.get? o).getD 0 : Int) + netDelta ds o
      if v < 0 then none
      else if v = 0 then some (acc.erase o)
      else some (acc.set o v.toNat))
    m

/-- §8.2: the coinbase credits `M = reward + F` to the recipient, with the
transactions' account actions; `nil` burns it. -/
def coinbase (b : Block) : List (Address × Int) :=
  match b.recipient with
  | some r => [(r, (b.reward : Int) + fee b.actions)]
  | none => []

/-- §5.2 step 11: with a recipient, the coinbase `M = reward + F` must fit an
`Int64` delta (zero credits nothing); a burned coinbase has no bound. -/
def coinbaseFits (b : Block) : Bool :=
  match b.recipient with
  | some _ => decide ((b.reward : Int) + fee b.actions ≤ int64Max)
  | none => true

/-- One block's value-bearing transition, from `prevState`, for a chain at
directory `dir` whose `parentState` holds `parentReceipts`. -/
def applyBlock (dir : String) (parentReceipts : Map ReceiptKey Address)
    (s : State) (b : Block) : Option State := do
  -- §8.2 fee rule, and §3.6 account-action validity.
  guard (accountActionsValid b.actions)
  guard (totalCredits b.actions + totalDeposited b.actions ≤
         totalDebits b.actions + totalWithdrawn b.actions)
  guard (coinbaseFits b)
  let afterW ← applyWithdrawals dir parentReceipts s.deposits b.actions
  let deposits ← applyDeposits afterW b.actions
  let receipts ← applyReceipts s.receipts b.actions
  let balances ← applyBalances s.balances (accountActions b.actions ++ coinbase b)
  -- §6.2: a balance beyond `UInt64` is invalid. This also covers §6.2's
  -- net-delta bound: from balances within `UInt64`, a net credit beyond it
  -- ends beyond it, and a net debit beyond it goes negative.
  guard (balances.all (·.2 ≤ uint64Max))
  pure { balances, deposits, receipts }

/-- A chain segment: each block with its `parentState`'s receipts. -/
def applyChain (dir : String) : State → List (Map ReceiptKey Address × Block) → Option State
  | s, [] => some s
  | s, (pr, b) :: bs => do applyChain dir (← applyBlock dir pr s b) bs

/-- The value a chain segment adds: each block's reward if it has a
recipient, minus its fees if it burns them. -/
def segmentIssuance : List (Map ReceiptKey Address × Block) → Int
  | [] => 0
  | (_, b) :: bs =>
      (match b.recipient with
       | some _ => (b.reward : Int)
       | none => -fee b.actions) + segmentIssuance bs

/-- Whether an action names deposit key `k` (as a deposit or a withdrawal). -/
def touchesDeposit (k : DepositKey) : Action → Bool
  | .deposit n dm amtD _ => (⟨dm, amtD, n⟩ : DepositKey) == k
  | .withdrawal _ n dm amtD _ => (⟨dm, amtD, n⟩ : DepositKey) == k
  | _ => false

/-- The receipt key a receipt action inserts. -/
def receiptKeyOf : Action → Option ReceiptKey
  | .receipt _ n dm amtD d => some ⟨d, dm, amtD, n⟩
  | _ => none

end Lattice
