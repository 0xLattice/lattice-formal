import LatticeProofs.Work

/-!
# Transaction child commitments and derived child grinds

Four rules, each modelled from where it is stated:

* **`child/X = C@P`** (`Block.validateChildCommitments`, Lattice 56.1.0).
  The spec does not state this rule, so it is modelled from the code: a
  general-state action writing `child/X` = `C@P` makes its block valid only if
  the block's children index holds exactly `C` at `X` and the block's
  `prevState` is `P`. Two actions on one key in a block are a state conflict
  (`GeneralState.proveAndUpdateState`); §6.3 does not say what two actions on
  one key do, so that rule is from the code too.
* **A proof is a header path** (spec §5.3 steps 2–4, §9.5): every link is a
  `children[d]` edge whose child anchors at its carrier's `prevState`, and the
  root's grind must meet the terminal's target. Composition
  (`ChildBlockProof.composing(hop:)`, lattice-node's `extending`) keeps the
  upstream root and appends the hop's directories; the spec is silent on it.
* **Credit by location** (spec §9.1): one credit per `(grind root, block)`,
  repeated observations ratcheting to the strongest.
* **Run binding** (spec §9.10, `ChainTree.applyParentRun`): a run of carrier
  `K` credits the committed child `C` only if `C.parentState == K.prevState`.

Text (CIDs, keys, values) is a list of characters. The code compares UTF-8
bytes; `@` is ASCII and never a UTF-8 continuation byte, so splitting
characters at `@` splits the bytes at the same place.
-/

namespace Lattice.ChildCommit

abbrev Text := List Char

/-! ## `child/X = C@P` (code: spec silent) -/

/-- A general-state action (§6.3): `newValue = none` is a delete. -/
structure Action where
  key : Text
  oldValue : Option Text
  newValue : Option Text
deriving DecidableEq

/-- What the commitment rule reads of a carrier block: its header's
`prevState`, the general actions of its transaction bodies in order, and its
children index (directory → child block CID) with the index's
well-formedness. Nothing of any child block: a child is named by CID only. -/
structure Carrier where
  prevState : Text
  actions : List Action
  children : List (Text × Text)
  childrenWellFormed : Bool

/-- `CHILD_COMMITMENT_KEY_PREFIX`. -/
def childPrefix : Text := "child/".toList

/-- `Block.childCommitments(in:)`, one action: its `(directory, value)` when
the key starts with `child/` and the action writes a value. A delete commits
nothing. -/
def commitment (a : Action) : Option (Text × Text) :=
  match a.newValue with
  | some v => if childPrefix.isPrefixOf a.key then some (a.key.drop childPrefix.length, v) else none
  | none => none

/-- Every commitment the bodies make, in order. -/
def commitments (as : List Action) : List (Text × Text) := as.filterMap commitment

/-- Split at the first `@`: what precedes it, and what follows if there is one. -/
def splitSep : Text → Text × Option Text
  | [] => ([], none)
  | ch :: cs =>
    if ch = '@' then ([], some cs)
    else match splitSep cs with
      | (a, r) => (ch :: a, r)

/-- `Block.childCommitmentValue`: `C@P` split at its one separator; none
unless there is exactly one and both sides are non-empty. -/
def commitValue (v : Text) : Option (Text × Text) :=
  match splitSep v with
  | (c, some p) => if c ≠ [] ∧ p ≠ [] ∧ '@' ∉ p then some (c, p) else none
  | (_, none) => none

/-- `Block.validateChildCommitments`: with no commitment the block passes
without reading its index; otherwise the index is well-formed and every
commitment's value parses as `C@P` with `P` the block's `prevState` and `C`
exactly the index entry at its directory. -/
def commitsValid (b : Carrier) : Bool :=
  let cs := commitments b.actions
  if cs.isEmpty then true
  else b.childrenWellFormed && cs.all fun xv =>
    match commitValue xv.2 with
    | some (c, p) => p == b.prevState && b.children.lookup xv.1 == some c
    | none => false

/-- `GeneralState.proveAndUpdateState`: a second action on a key already
touched in the block is `conflictingActions`. -/
def KeysDistinct (b : Carrier) : Prop := (b.actions.map Action.key).Nodup

/-- The two rules of a carrier's validity this model keeps. -/
def Valid (b : Carrier) : Prop := KeysDistinct b ∧ commitsValid b = true

instance (b : Carrier) : Decidable (Valid b) :=
  inferInstanceAs (Decidable ((b.actions.map Action.key).Nodup ∧ commitsValid b = true))

/-! ## Proofs as header paths (spec §5.3, §9.5) -/

/-- The header fields a proof walk reads (§5.3 steps 2–4). -/
structure Header where
  cid : Text
  target : Nat
  prevState : Text
  parentState : Text
  children : List (Text × Text)

/-- One vertical edge: `B.children[d]` is `N`, and `N` anchors at `B`'s
committed `prevState` (§5.3 step 3, `verifySecuringWork`). -/
def Link (B : Header) (d : Text) (N : Header) : Prop :=
  B.children.lookup d = some N.cid ∧ N.parentState = B.prevState

/-- A proof: the grind root and the path of `(directory, header)` hops below
it. `ChildBlockProof` carries the same path as CAS entries keyed by CID; a
header here stands for the content its CID binds. -/
structure Proof where
  root : Header
  hops : List (Text × Header)

def linksFrom : Header → List (Text × Header) → Prop
  | _, [] => True
  | B, (d, N) :: rest => Link B d N ∧ linksFrom N rest

def terminalFrom : Header → List (Text × Header) → Header
  | B, [] => B
  | _, (_, N) :: rest => terminalFrom N rest

/-- Every link of the path holds. -/
def Proof.Valid (p : Proof) : Prop := linksFrom p.root p.hops

/-- The block the path ends at. -/
def Proof.terminal (p : Proof) : Header := terminalFrom p.root p.hops

/-- The blocks below the root, in path order. -/
def Proof.blocks (p : Proof) : List Header := p.hops.map Prod.snd

/-- `ChildBlockProof.generate(rootHeader: B, childDirectory: d)` for the
block `C` that `B` commits at `d`. -/
def hop (B : Header) (d : Text) (C : Header) : Proof := ⟨B, [(d, C)]⟩

/-- `composing(hop:)`: the upstream root, then the upstream path, then the
hop's (`directoryPath + hop.directoryPath`). The hop's own root is not kept:
the walk reaches it as the upstream's terminal. -/
def Proof.compose (p q : Proof) : Proof := ⟨p.root, p.hops ++ q.hops⟩

/-- `verifySecuringWork` under grind hash `h`: a non-empty path, every link
valid, ending at `C`, and `h` meets `C`'s target. -/
def VerifiesAt (h : Nat) (p : Proof) (C : Header) : Prop :=
  p.hops ≠ [] ∧ p.Valid ∧ p.terminal = C ∧ Work.Meets C.target h

/-- A proof verifies for `C` under its own root's grind (`pow` is
`proofOfWorkHash`). -/
def Verifies (pow : Header → Nat) (p : Proof) (C : Header) : Prop :=
  VerifiesAt (pow p.root) p C

/-! ## Credit by location (spec §9.1) -/

/-- Credited work at each location `(grind root, block)`; `0` is none. -/
abbrev Credits := Text → Text → Nat

/-- A repeated observation at a location keeps the strongest quantity. -/
def Credits.insert (m : Credits) (g b : Text) (w : Nat) : Credits :=
  fun g' b' => if g' = g ∧ b' = b then max (m g b) w else m g' b'

/-- One verified credit event: from a peer proof, a carrier's derivation, a
restart's boot pass, or anything else that names grind `root` at `block`. -/
structure Credit where
  root : Text
  block : Text
  work : Nat

def applyAll (m : Credits) (es : List Credit) : Credits :=
  es.foldl (fun m e => m.insert e.root e.block e.work) m

/-! ## Run binding (spec §9.10) -/

/-- A committed child block's header fields the run rule reads. -/
structure Child where
  cid : Text
  parentState : Text

/-- `applyParentRun`, one committer `K` into directory `X`: `K` commits `C`
(`K.children[X]`) and `C` anchors at `K`'s entering state; the credit is
`runWork(K, X) − grindWork(K)`. -/
def runCredit (K : Carrier) (X : Text) (C : Child) (run grind : Nat) : Option Nat :=
  if K.children.lookup X = some C.cid ∧ C.parentState = K.prevState then some (run - grind) else none

end Lattice.ChildCommit
