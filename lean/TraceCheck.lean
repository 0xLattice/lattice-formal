import Lean.Data.Json
import LatticeProofs.Model

/-!
# Value-transition trace check

Replays value-transition traces recorded from Lattice's real block state
transition (`ValueTransitionTraceExportTests`) through the model's
`applyBlock`. A case conforms when the model and the implementation agree on
validity, and on a valid block every entry of the three post sub-states is
the same.

    lake exe tracecheck <trace.json>...
-/

open Lean Lattice

namespace TraceCheck

def field (j : Json) (k : String) : Except String Json := j.getObjVal? k

def nat (j : Json) (k : String) : Except String Nat := do (← field j k).getNat?
def int (j : Json) (k : String) : Except String Int := do (← field j k).getInt?
def str (j : Json) (k : String) : Except String String := do (← field j k).getStr?

def depositKey (j : Json) : Except String DepositKey :=
  return ⟨← str j "demander", ← nat j "amountDemanded", ← nat j "nonce"⟩

def receiptKey (j : Json) : Except String ReceiptKey :=
  return ⟨← str j "directory", ← str j "demander", ← nat j "amountDemanded", ← nat j "nonce"⟩

/-- A JSON array of `[key, value]` pairs. -/
def pairs (j : Json) (k : Json → Except String κ) (v : Json → Except String ν) :
    Except String (Map κ ν) := do
  (← j.getArr?).toList.mapM fun e => do
    let a ← e.getArr?
    unless a.size = 2 do throw s!"expected a pair, got {e.compress}"
    return (← k a[0]!, ← v a[1]!)

def state (j : Json) : Except String State :=
  return { balances := ← pairs (← field j "balances") Json.getStr? Json.getNat?
           deposits := ← pairs (← field j "deposits") depositKey Json.getNat?
           receipts := ← pairs (← field j "receipts") receiptKey Json.getStr? }

def action (j : Json) : Except String Action := do
  match ← str j "kind" with
  | "account" => return .account (← str j "owner") (← int j "delta")
  | "deposit" =>
      return .deposit (← nat j "nonce") (← str j "demander") (← nat j "amountDemanded")
        (← nat j "amountDeposited")
  | "withdrawal" =>
      return .withdrawal (← str j "withdrawer") (← nat j "nonce") (← str j "demander")
        (← nat j "amountDemanded") (← nat j "amountWithdrawn")
  | "receipt" =>
      return .receipt (← str j "withdrawer") (← nat j "nonce") (← str j "demander")
        (← nat j "amountDemanded") (← str j "directory")
  | k => throw s!"unknown action kind {k}"

def block (j : Json) : Except String Block := do
  let recipient ← match ← field j "recipient" with
    | .null => pure none
    | r => some <$> r.getStr?
  return { actions := ← (← (← field j "actions").getArr?).toList.mapM action
           reward := ← nat j "reward"
           recipient }

/-- Same entries, ignoring order (keys are distinct in both). -/
def sameMap [DecidableEq κ] [DecidableEq ν] (a b : Map κ ν) : Bool :=
  a.length == b.length && a.all (b.contains ·)

def sameState (a b : State) : Bool :=
  sameMap a.balances b.balances && sameMap a.deposits b.deposits &&
    sameMap a.receipts b.receipts

def showState (s : State) : String :=
  s!"balances {repr s.balances}, deposits {repr s.deposits}, receipts {repr s.receipts}"

/-- `none` when the case conforms, otherwise why not. -/
def checkCase (j : Json) : Except String (Option String) := do
  let dir ← str j "dir"
  let pr ← pairs (← field j "parentReceipts") receiptKey Json.getStr?
  let prev ← state (← field j "prev")
  let b ← block (← field j "block")
  let impl ← match ← field j "result" with
    | .null => pure none
    | r => some <$> state r
  return match applyBlock dir pr prev b, impl with
  | none, none => none
  | some s, some t => if sameState s t then none
      else some s!"post-states differ\n    model: {showState s}\n    impl:  {showState t}"
  | some _, none => some "the model accepts a block the implementation rejects"
  | none, some _ => some "the model rejects a block the implementation accepts"

end TraceCheck

open TraceCheck in
def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "usage: tracecheck <trace.json>..."
    return 2
  let mut cases := 0
  let mut failures := 0
  for path in args do
    let text ← IO.FS.readFile path
    let j ← IO.ofExcept (Json.parse text)
    let arr ← IO.ofExcept j.getArr?
    let mut bad := 0
    for i in [0:arr.size] do
      cases := cases + 1
      match checkCase arr[i]! with
      | .error e =>
          bad := bad + 1
          IO.println s!"{path} case {i}: malformed: {e}"
      | .ok (some why) =>
          bad := bad + 1
          IO.println s!"{path} case {i}: FAIL ({(arr[i]!.getObjValD "violates").compress}): {why}"
      | .ok none => pure ()
    IO.println s!"{path}: {if bad == 0 then "pass" else "FAIL"} ({arr.size} cases)"
    failures := failures + bad
  IO.println s!"{cases - failures}/{cases} cases conform"
  return if failures == 0 then 0 else 1
