import LatticeProofs.MerkleBatchProofs

/-! Non-vacuity of the batch theorems: concrete batches on which the batch
succeeds and fails, checked by evaluation. Each state is built from the empty
state by batches (`Reachable`, so canonical by `reachable_canonical`); the
digest is a stand-in, not collision resistant, and only compares tries built
here. -/

namespace Lattice.Merkle.BatchExamples
open Lattice.Merkle

abbrev Rt := Root Char Nat UInt64

def h : Enc Char Nat UInt64 → UInt64
  | .node p v ks => hash (p.map Char.toNat, v, ks.map fun (c, d) => (c.toNat, d))
  | .root n ks => hash (n, ks.map fun (c, d) => (c.toNat, d))

def w (k : String) (o : Op Nat) : List Char × Op Nat := (k.toList, o)

/-- The state holding these entries, built by one batch from the empty state. -/
def build (es : List (String × Nat)) : Rt :=
  ((Root.empty : Rt).batch (es.map fun (k, v) => w k (.insert v))).getD Root.empty

def dig (r : Option Rt) : Option UInt64 := r.map (·.digest h)

def read (r : Option Rt) (k : String) : Option (Option Nat) := r.map (·.toMap k.toList)

/-- What the theorems compare: the batch, the writes one after another in
both orders, and the batch on the proof, which commits to the same root. -/
def agrees (s : Rt) (ws : Batch Char Nat) : Bool :=
  dig (s.batch ws) == dig (s.applyAll ws) &&
  dig (s.batch ws) == dig (s.applyAll ws.reverse) &&
  ((Root.prove h ws s).map (·.digest h) == (if (s.batch ws).isSome then some (s.digest h) else
    (Root.prove h ws s).map (·.digest h))) &&
  dig ((Root.prove h ws s).bind (·.batch ws)) == dig (s.batch ws)

/-! K and K/c: an update at a key and an insertion beneath it, in one batch
(the batch cashew refused when a child's proof inherited the parent's own
write). -/

def s1 := build [("ab", 1), ("x", 2)]
def ws1 := [w "ab" (.update 5), w "abc" (.insert 7)]

#guard (s1.batch ws1).isSome
#guard (Root.prove h ws1 s1).isSome
#guard agrees s1 ws1
#guard read (s1.batch ws1) "ab" == some (some 5)
#guard read (s1.batch ws1) "abc" == some (some 7)
#guard read (s1.batch ws1) "x" == some (some 2)

/-! An insertion at a value-less branch point, with writes beneath it: the
branch node's children are transformed too. -/

def s2 := build [("ab", 1), ("ac", 2)]
def ws2 := [w "a" (.insert 3), w "ab" .delete, w "ad" (.insert 4)]

#guard (s2.batch ws2).isSome
#guard (Root.prove h ws2 s2).isSome
#guard agrees s2 ws2
#guard read (s2.batch ws2) "a" == some (some 3)
#guard read (s2.batch ws2) "ab" == some none
#guard read (s2.batch ws2) "ac" == some (some 2)
#guard read (s2.batch ws2) "ad" == some (some 4)

/-! Deletions that leave a value-less node with one child: the node collapses
into the child, which the proof resolves only because it expands. -/

def s3 := build [("ab", 1), ("ac", 2), ("ad", 3)]
def ws3 := [w "ac" .delete, w "ad" .delete]

#guard (s3.batch ws3).isSome
#guard agrees s3 ws3
#guard dig (s3.batch ws3) == some ((build [("ab", 1)]).digest h)
#guard dig ((Root.prove h ws3 s3).bind (·.batch ws3)) == some ((build [("ab", 1)]).digest h)

/-! Failing batches: the batch, the writes one after another, and (for a
write needing a value) the proof all refuse. -/

#guard (s1.batch [w "zz" .delete]).isNone
#guard (s1.applyAll [w "zz" .delete]).isNone
#guard (Root.prove h [w "zz" .delete] s1).isNone
#guard (s1.batch [w "ab" (.insert 9), w "q" (.insert 1)]).isNone
#guard (s1.applyAll [w "q" (.insert 1), w "ab" (.insert 9)]).isNone
#guard (s1.batch [w "" (.insert 9)]).isNone
-- a deletion at a value-less node: the proof is built, the batch refuses
#guard (Root.prove h [w "a" .delete] s2).isSome
#guard (s2.batch [w "a" .delete]).isNone

/-! A batch on a partial trie: the root's children left as stubs refuse a
write beneath them; the proof does not. -/

def stubbed (s : Rt) : Rt := ⟨s.count, s.kids.stubs h⟩

#guard (stubbed s1).digest h == s1.digest h
#guard ((stubbed s1).batch ws1).isNone

end Lattice.Merkle.BatchExamples
