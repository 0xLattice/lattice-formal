/-!
# Merkle state commitments: cashew's compressed radix trie

A model of how Lattice commits to each sub-state (§2, §3.4, §6.1): the
sub-state is a cashew `MerkleDictionary` (cashew 5.0.3), a path-compressed
radix trie keyed by characters, and the block commits to the CID of its root.

* The root holds a `count` and children keyed by a key's first character; it
  has no prefix and no value. An inner node holds a `prefix`, an optional
  `value` and children keyed by the next character, encoded as an array
  sorted by that character. A child link is the CID of the child's encoding.
* A partially resolved trie stands in for a proof: a child is either a node
  (fetched, its hash checked) or a stub that names only the child's digest.
* A transition walks the touched path. It fails closed when it needs a
  stub's contents, enforces its precondition (insertion at an absent key,
  update and deletion at a present one), splits a prefix on insertion,
  collapses on deletion, and recomputes digests bottom-up; the root's
  `count` moves by arithmetic.

Abstracted: a key character is any `K` with decidable equality and a strict
order (the implementation's keys are visible ASCII, ordered by code point);
the digest of a node is an abstract `H` applied to the node's fields with its
children's digests in place (DAG-CBOR bytes and the CID's multibase text are
not modelled); collision resistance is the hypothesis that `H` is injective.
-/

namespace Lattice.Merkle

/-- What a node's CID is computed from: its encoded fields, with each child
link replaced by the child's digest. -/
inductive Enc (K V D : Type) where
  | node (pfx : List K) (val : Option V) (kids : List (K × D))
  | root (count : Int) (kids : List (K × D))

mutual
/-- A partially resolved trie node: resolved, or a stub naming its digest. -/
inductive Trie (K V D : Type) where
  | stub (d : D)
  | node (pfx : List K) (val : Option V) (kids : Kids K V D)

/-- A node's children, in encoding order. -/
inductive Kids (K V D : Type) where
  | nil
  | cons (c : K) (t : Trie K V D) (rest : Kids K V D)
end

/-- The root of a sub-state (a `MerkleDictionary`): a count and children. -/
structure Root (K V D : Type) where
  count : Int
  kids : Kids K V D

variable {K V D : Type}

/-! ## Digests -/

mutual
def Trie.digest (H : Enc K V D → D) : Trie K V D → D
  | .stub d => d
  | .node p v ks => H (.node p v (ks.digests H))

def Kids.digests (H : Enc K V D → D) : Kids K V D → List (K × D)
  | .nil => []
  | .cons c t rest => (c, t.digest H) :: rest.digests H
end

/-- The sub-state's commitment: the CID of the root. -/
def Root.digest (H : Enc K V D → D) (s : Root K V D) : D :=
  H (.root s.count (s.kids.digests H))

/-- The empty map: a root with count `0` and no children. -/
def Root.empty : Root K V D := ⟨0, .nil⟩

/-! ## Fully resolved tries -/

mutual
def Trie.Full : Trie K V D → Prop
  | .stub _ => False
  | .node _ _ ks => ks.Full

def Kids.Full : Kids K V D → Prop
  | .nil => True
  | .cons _ t rest => t.Full ∧ rest.Full
end

def Root.Full (s : Root K V D) : Prop := s.kids.Full

/-! ## Comparing a node's prefix with the rest of a key -/

/-- How the rest of a key `k` meets a node's prefix `p`. -/
inductive Split (K : Type) where
  /-- `k = p` -/
  | equal
  /-- `k = p ++ c :: r` -/
  | keyLonger (c : K) (r : List K)
  /-- `p = k ++ c :: r` -/
  | keyShorter (c : K) (r : List K)
  /-- `k = q ++ a :: ka`, `p = q ++ b :: pb`, `a ≠ b` -/
  | diverge (q : List K) (a : K) (ka : List K) (b : K) (pb : List K)

def Split.cons (x : K) : Split K → Split K
  | .diverge q a ka b pb => .diverge (x :: q) a ka b pb
  | s => s

variable [DecidableEq K]

/-- `split p k` compares a node's prefix `p` with the rest of a key `k`
(cashew `compareSlices`, `commonPrefix`). -/
def split : List K → List K → Split K
  | [], [] => .equal
  | [], c :: r => .keyLonger c r
  | c :: r, [] => .keyShorter c r
  | b :: pb, a :: ka => if a = b then (split pb ka).cons a else .diverge [] a ka b pb

/-- `dropPrefix p k = some r` when `k = p ++ r`. -/
def dropPrefix : List K → List K → Option (List K)
  | [], k => some k
  | _ :: _, [] => none
  | b :: p, a :: k => if b = a then dropPrefix p k else none

/-! ## Reads -/

/-- A read of a partial trie: the value, its absence, or a stub on the path
(the implementation's `try? get` turns the last into absent). -/
inductive Read (V : Type) where
  | found (v : V)
  | absent
  | unknown

def Read.ofOption : Option V → Read V
  | some v => .found v
  | none => .absent

mutual
/-- `lookup t k`: the value at the rest of a key `k`, which starts at node `t`
(cashew `RadixNode.get`). -/
def Trie.lookup : Trie K V D → List K → Read V
  | .stub _, _ => .unknown
  | .node p v ks, k =>
    match dropPrefix p k with
    | none => .absent
    | some [] => .ofOption v
    | some (c :: r) => ks.lookup c r

/-- Find the child for character `c` and read `c :: r` in it. -/
def Kids.lookup : Kids K V D → K → List K → Read V
  | .nil, _, _ => .absent
  | .cons c' t rest, c, r => if c' = c then t.lookup (c :: r) else rest.lookup c r
end

/-- `MerkleDictionary.get`: the empty key holds nothing. -/
def Root.lookup (s : Root K V D) : List K → Read V
  | [] => .absent
  | c :: r => s.kids.lookup c r

/-- The map a trie stands for (stubs read as absent; on a full trie they do
not occur). -/
def Root.toMap (s : Root K V D) (k : List K) : Option V :=
  match s.lookup k with
  | .found v => some v
  | _ => none

/-! ## Transitions -/

/-- A write at one key (cashew `Transform`). -/
inductive Op (V : Type) where
  | insert (v : V)
  | update (v : V)
  | delete

/-- The write's precondition on the current value (cashew `proof()`:
insertion needs no value, mutation and deletion need one). -/
def Op.pre : Op V → Option V → Prop
  | .insert _, cur => cur = none
  | .update _, cur => cur ≠ none
  | .delete, cur => cur ≠ none

/-- The value the write leaves. -/
def Op.post : Op V → Option V
  | .insert v => some v
  | .update v => some v
  | .delete => none

/-- How the root's `count` moves. -/
def Op.delta : Op V → Int
  | .insert _ => 1
  | .update _ => 0
  | .delete => -1

/-- The write on the abstract map: `none` when its precondition fails. -/
def Op.applyMap (o : Op V) (k : List K) (m : List K → Option V) :
    Option (List K → Option V) :=
  match o, m k with
  | .insert _, none => some fun k' => if k' = k then o.post else m k'
  | .insert _, some _ => none
  | _, none => none
  | _, some _ => some fun k' => if k' = k then o.post else m k'

def leaf (k : List K) (v : V) : Trie K V D := .node k (some v) .nil

variable [LT K] [DecidableRel (α := K) (· < ·)]

/-- Insert a child at its place in character order. -/
def Kids.ins (c : K) (t : Trie K V D) : Kids K V D → Kids K V D
  | .nil => .cons c t .nil
  | .cons c' t' rest =>
    if c < c' then .cons c t (.cons c' t' rest) else .cons c' t' (rest.ins c t)

/-- cashew `collapsed`: no children deletes the node, one child merges into
the node (and must be resolved), several stay under a value-less node. -/
def collapse (p : List K) : Kids K V D → Option (Option (Trie K V D))
  | .nil => some none
  | .cons _ (.stub _) .nil => none
  | .cons _ (.node p' v' ks') .nil => some (some (.node (p ++ p') v' ks'))
  | ks@(.cons _ _ (.cons _ _ _)) => some (some (.node p none ks))

/-- The result of descending into a node's children. -/
inductive Step (K V D : Type) where
  /-- no child for the character -/
  | missing
  /-- the write failed beneath -/
  | fail
  /-- the new children, and whether the touched child was deleted -/
  | done (ks : Kids K V D) (removed : Bool)

mutual
/-- One write at the rest of a key `k`, which starts at node `t` (cashew
`RadixNode.transform` for one key). `none`: the write fails (a stub it
needs, or its precondition); `some none`: the node is deleted. -/
def Trie.apply (o : Op V) : Trie K V D → List K → Option (Option (Trie K V D))
  | .stub _, _ => none
  | .node p val ks, k =>
    match split p k with
    | .equal =>
      match o, val with
      | .insert v, none => some (some (.node p (some v) ks))
      | .update v, some _ => some (some (.node p (some v) ks))
      | .delete, some _ => collapse p ks
      | _, _ => none
    | .keyLonger c r =>
      match ks.descend o c r with
      | .missing =>
        match o with
        | .insert v => some (some (.node p val (ks.ins c (leaf (c :: r) v))))
        | _ => none
      | .fail => none
      | .done ks' removed =>
        if removed ∧ val = none then collapse p ks' else some (some (.node p val ks'))
    | .keyShorter c r =>
      match o with
      | .insert v => some (some (.node k (some v) (.cons c (.node (c :: r) val ks) .nil)))
      | _ => none
    | .diverge q a ka b pb =>
      match o with
      | .insert v =>
        some (some (.node q none ((Kids.cons b (.node (b :: pb) val ks) .nil).ins a
          (leaf (a :: ka) v))))
      | _ => none

/-- Descend into the child for character `c` with the rest `c :: r`. -/
def Kids.descend (o : Op V) : Kids K V D → K → List K → Step K V D
  | .nil, _, _ => .missing
  | .cons c' t rest, c, r =>
    if c' = c then
      match t.apply o (c :: r) with
      | none => .fail
      | some none => .done rest true
      | some (some t') => .done (.cons c' t' rest) false
    else
      match rest.descend o c r with
      | .done ks removed => .done (.cons c' t ks) removed
      | s => s
end

/-- One write at key `k` on a sub-state root (cashew
`MerkleDictionary.transform`): the empty key is refused, the root never
collapses, and `count` moves by the write's delta. -/
def Root.apply (o : Op V) (k : List K) (s : Root K V D) : Option (Root K V D) :=
  match k with
  | [] => none
  | c :: r =>
    match s.kids.descend o c r with
    | .missing =>
      match o with
      | .insert v => some ⟨s.count + 1, s.kids.ins c (leaf (c :: r) v)⟩
      | _ => none
    | .fail => none
    | .done ks _ => some ⟨s.count + o.delta, ks⟩

/-- A batch of writes applied one after another. -/
def Root.applyAll : List (List K × Op V) → Root K V D → Option (Root K V D)
  | [], s => some s
  | (k, o) :: ws, s => do Root.applyAll ws (← s.apply o k)

/-! ## Canonical form -/

/-- A node's prefix starts with the character it is filed under. -/
def Trie.HeadIs (c : K) : Trie K V D → Prop
  | .stub _ => False
  | .node p _ _ => p.head? = some c

def Kids.keys : Kids K V D → List K
  | .nil => []
  | .cons c _ rest => c :: rest.keys

def Kids.length : Kids K V D → Nat
  | .nil => 0
  | .cons _ _ rest => rest.length + 1

mutual
/-- The shape every transition from the empty root keeps (and the decoder
does not check): every node is resolved, has a nonempty prefix, holds a value
or at least two children; children are filed under their prefix's first
character, in strictly increasing order. -/
def Trie.Canon : Trie K V D → Prop
  | .stub _ => False
  | .node p v ks => p ≠ [] ∧ (v ≠ none ∨ 2 ≤ ks.length) ∧ ks.Canon

def Kids.Canon : Kids K V D → Prop
  | .nil => True
  | .cons c t rest => t.HeadIs c ∧ t.Canon ∧ rest.Canon ∧ ∀ c' ∈ rest.keys, c < c'
end

mutual
/-- The number of values in a trie. -/
def Trie.size : Trie K V D → Nat
  | .stub _ => 0
  | .node _ v ks => (if v = none then 0 else 1) + ks.size

def Kids.size : Kids K V D → Nat
  | .nil => 0
  | .cons _ t rest => t.size + rest.size
end

/-- A canonical root: canonical children, and a `count` equal to the number
of entries (cashew never checks it; it holds because every transition moves
it by its delta). -/
def Root.Canon (s : Root K V D) : Prop := s.kids.Canon ∧ s.count = s.kids.size

end Lattice.Merkle
