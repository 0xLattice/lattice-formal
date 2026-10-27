import Lean.Data.Json
import LatticeProofs.Asert

/-!
# ASERT vector check

Replays ASERT vectors recorded from Lattice's real
`ChainSpec.calculateAsertTarget` (`AsertVectorExportTests`) through the
model's `calculateAsertTarget`. A vector conforms when the model does not
trap and returns the same target.

    lake exe asertcheck <asert-vectors.json>...
-/

open Lean Lattice.Asert

namespace AsertCheck

def field (j : Json) (k : String) : Except String String := do (← j.getObjVal? k).getStr?

def nat (j : Json) (k : String) : Except String Nat := do
  let s ← field j k
  match s.toNat? with
  | some n => return n
  | none => throw s!"{k}: not a natural number: {s}"

def int (j : Json) (k : String) : Except String Int := do
  let s ← field j k
  match s.toInt? with
  | some n => return n
  | none => throw s!"{k}: not an integer: {s}"

def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

/-- A target: exactly 64 lowercase hex digits. -/
def hex (j : Json) (k : String) : Except String Nat := do
  let s ← field j k
  unless s.length = 64 do throw s!"{k}: expected 64 hex digits: {s}"
  s.toList.foldlM (fun acc c => match hexDigit c with
    | some d => pure (acc * 16 + d)
    | none => throw s!"{k}: not hex: {s}") 0

/-- `none` when the vector conforms, otherwise why not. -/
def checkVector (j : Json) : Except String (Option String) := do
  let spec : Spec := ⟨← nat j "targetBlockTime", ← nat j "halfLife"⟩
  let expected ← hex j "nextTarget"
  let got := calculateAsertTarget spec (← hex j "anchorTarget") (← int j "anchorTimestamp")
    (← nat j "anchorHeight") (← int j "blockTimestamp") (← nat j "blockHeight")
  return match got with
  | some t => if t = expected then none else some s!"model {t}, implementation {expected}"
  | none => some s!"the model traps; implementation {expected}"

end AsertCheck

open AsertCheck in
def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "usage: asertcheck <asert-vectors.json>..."
    return 2
  let mut total := 0
  let mut failures := 0
  for path in args do
    let j ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
    let arr ← IO.ofExcept j.getArr?
    let mut bad := 0
    for v in arr do
      total := total + 1
      let name := (v.getObjValD "name").compress
      match checkVector v with
      | .error e =>
          bad := bad + 1
          IO.println s!"{path} {name}: malformed: {e}"
      | .ok (some why) =>
          bad := bad + 1
          if bad ≤ 20 then IO.println s!"{path} {name}: FAIL: {why}"
      | .ok none => pure ()
    IO.println s!"{path}: {if bad == 0 then "pass" else "FAIL"} ({arr.size} vectors)"
    failures := failures + bad
  IO.println s!"{total - failures}/{total} vectors conform"
  return if failures == 0 then 0 else 1
