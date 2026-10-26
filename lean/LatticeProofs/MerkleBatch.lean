import LatticeProofs.Merkle

/-!
# Batched writes: cashew's one-pass transform and its proof

Lattice does not write a sub-state one key at a time. Each block builds one
`[[String]: SparseMerkleProof]` and one `[[String]: Transform]` per sub-state
(`*State+Transition.swift`), with at most one write per key, resolves the
partial trie with `proof(paths:)` and applies every write in a single
`transform(transforms:)` (cashew 5.0.3). This file models both passes as
cashew implements them: recursive, with each child given only the writes
beneath it.

* A batch is a list of keyed writes (`Batch`). cashew holds it in an
  `ArrayTrie<Transform>`; Lattice's state keys are single path segments, so
  the nested-dictionary branches (`hasNestedWrites`, writes into a `Header`
  value) never fire and are not modelled. The writes a node sees are keyed
  relative to the start of its prefix.
* `childPrefix(for: c)` is the compressed path of the write trie's child for
  `c`: `c` followed by the longest common prefix of the rest of the keys
  under `c` (`childPrefix`). `traverse(path: q)` keeps the writes extending
  `q`, with `q` removed (`Batch.under`); `traverseChild(c)` keeps the writes
  starting with `c` (`Batch.at`); `get([""])` is the write at the empty
  relative key (`Batch.get [] `).
* `RadixNode.transform` compares `childPrefix` with the node's prefix: equal
  (`transformExactMatch`), longer (`transformChildLonger`), shorter
  (`transformPrefixLonger`) or divergent (`transformDivergent`).
  `transformChildren` transforms each existing child that has writes, keeps
  the others, and builds each new child with `insertAll`.
* A write that fails, or that needs a stub's contents, fails the whole batch.

Termination is on the total length of the batch's keys, then on the size of
the trie: every step into a child consumes at least one character of every
key it passes on.
-/

namespace Lattice.Merkle

variable {K V D : Type}

/-- Writes keyed relative to a position in the trie (cashew
`ArrayTrie<Transform>` of single-segment paths). -/
abbrev Batch (K V : Type) := List (List K × Op V)

/-- The total length of the keys, plus one per write: the termination
measure. -/
def Batch.tot : Batch K V → Nat
  | [] => 0
  | (k, _) :: ws => k.length + 1 + Batch.tot ws

/-- The root's `count` moves by the sum of the writes' deltas (cashew
`MerkleDictionary.transform` sums `childValues()`). -/
def Batch.delta : Batch K V → Int
  | [] => 0
  | (_, o) :: ws => o.delta + Batch.delta ws

/-- One write per key (Lattice builds a batch as a dictionary). -/
def Batch.Nodup (ws : Batch K V) : Prop := (ws.map (·.1)).Nodup

mutual
def Trie.weight : Trie K V D → Nat
  | .stub _ => 1
  | .node _ _ ks => ks.weight + 1

def Kids.weight : Kids K V D → Nat
  | .nil => 1
  | .cons _ t rest => t.weight + rest.weight + 1
end

variable [DecidableEq K]

/-- The write at key `k` (`ArrayTrie.get`). -/
def Batch.get : Batch K V → List K → Option (Op V)
  | [], _ => none
  | (k', o) :: ws, k => if k' = k then some o else Batch.get ws k

/-- The writes starting with `c`, keys kept (`traverseChild`). -/
def Batch.at (c : K) : Batch K V → Batch K V
  | [] => []
  | (k, o) :: ws => if k.head? = some c then (k, o) :: Batch.at c ws else Batch.at c ws

/-- The writes extending `q`, with `q` removed (`traverse(path:)`). -/
def Batch.under (q : List K) : Batch K V → Batch K V
  | [] => []
  | (k, o) :: ws =>
    match dropPrefix q k with
    | some r => (r, o) :: Batch.under q ws
    | none => Batch.under q ws

/-- The first characters of the nonempty keys, each once
(`childCharacters()`). -/
def Batch.heads : Batch K V → List K
  | [] => []
  | ([], _) :: ws => Batch.heads ws
  | (c :: _, _) :: ws => if c ∈ Batch.heads ws then Batch.heads ws else c :: Batch.heads ws

/-- The longest common prefix of two keys. -/
def lcp : List K → List K → List K
  | a :: x, b :: y => if a = b then a :: lcp x y else []
  | _, _ => []

/-- The longest common prefix of the keys. -/
def Batch.common : Batch K V → List K
  | [] => []
  | [(k, _)] => k
  | (k, _) :: ws => lcp k (Batch.common ws)

/-- `childPrefix(for: c)`: the compressed path of the write trie's child for
`c`, for writes that all start with `c`. -/
def childPrefix (c : K) (ws : Batch K V) : List K := c :: (ws.under [c]).common

/-- An update or a deletion: what `proof()` refuses at a key that is not in
the trie. -/
def Op.needsValue : Op V → Bool
  | .insert _ => false
  | _ => true

def Op.isDelete : Op V → Bool
  | .delete => true
  | _ => false

/-! ## Termination -/

theorem lex_left {a a' b b' : Nat} (h : a' < a) :
    Prod.Lex (· < ·) (· < ·) (a', b') (a, b) := Prod.Lex.left _ _ h

theorem lex_right {a a' b b' : Nat} (h1 : a' ≤ a) (h2 : b' < b) :
    Prod.Lex (· < ·) (· < ·) (a', b') (a, b) := by
  rcases Nat.lt_or_eq_of_le h1 with h | rfl
  · exact Prod.Lex.left _ _ h
  · exact Prod.Lex.right _ h2

theorem Batch.tot_at_le (c : K) : ∀ ws : Batch K V, (ws.at c).tot ≤ ws.tot
  | [] => Nat.le_refl _
  | (k, o) :: ws => by
    have := Batch.tot_at_le c ws
    simp only [Batch.at]; split <;> simp only [Batch.tot] <;> omega

theorem dropPrefix_length : ∀ {q k r : List K}, dropPrefix q k = some r → r.length + q.length = k.length
  | [], k, r, h => by simp [dropPrefix] at h; subst h; simp
  | _ :: _, [], _, h => by simp [dropPrefix] at h
  | b :: q, a :: k, r, h => by
    simp only [dropPrefix] at h
    split at h
    · have := dropPrefix_length h; simp; omega
    · simp at h

theorem Batch.tot_under_lt {q : List K} (hq : q ≠ []) :
    ∀ ws : Batch K V, (ws.under q).tot + (if ws = [] then 0 else 1) ≤ ws.tot
  | [] => by simp [Batch.under, Batch.tot]
  | (k, o) :: ws => by
    have ih := Batch.tot_under_lt hq ws
    have hq' : 0 < q.length := List.length_pos_iff.2 hq
    simp only [Batch.under, reduceCtorEq, ite_false]
    split
    · next r h =>
      have := dropPrefix_length h
      simp only [Batch.tot]; split at ih <;> omega
    · simp only [Batch.tot]; split at ih <;> omega

variable [LT K] [DecidableRel (α := K) (· < ·)]

/-! ## The transform -/

mutual
/-- cashew `insertAll(childChar: c, transforms: ws)`: a subtree of fresh
nodes holding writes that all start with `c`, where nothing exists yet; every
write must be an insertion. -/
def insertAll (c : K) (ws : Batch K V) : Option (Trie K V D) :=
  if ws = [] then none else
  let q := childPrefix c ws
  let T := ws.under q
  match insertKids T T.heads .nil with
  | none => none
  | some ks =>
    match T.get [] with
    | some (.insert v) => some (.node q (some v) ks)
    | some _ => none
    | none => some (.node q none ks)
termination_by (ws.tot, 0)
decreasing_by
  all_goals simp_wf
  have h := Batch.tot_under_lt (q := childPrefix c ws) (by simp [childPrefix]) ws
  have hne : ¬ ws = [] := by assumption
  simp only [hne, ite_false] at h
  exact lex_left (by omega)

/-- Add a fresh child, built by `insertAll`, for each character in `chs`. -/
def insertKids (T : Batch K V) : List K → Kids K V D → Option (Kids K V D)
  | [], ks => some ks
  | ch :: chs, ks =>
    match insertKids T chs ks, insertAll ch (T.at ch) with
    | some ks', some t => some (ks'.ins ch t)
    | _, _ => none
termination_by chs _ => (T.tot, chs.length + 1)
decreasing_by
  all_goals simp_wf
  all_goals first
    | exact lex_right (Nat.le_refl _) (by omega)
    | exact lex_right (Batch.tot_at_le _ _) (by omega)
end

mutual
/-- cashew `RadixNode.transform(transforms:)`: the writes `ws` at a node, keyed
relative to the start of its prefix. `none`: the batch fails; `some none`: the
node is deleted. -/
def Trie.batch : Trie K V D → Batch K V → Option (Option (Trie K V D))
  | .stub _, _ => none
  | .node [] _ _, _ => none
  | .node (c :: p') v ks, ws =>
    let p := c :: p'
    let W := ws.at c
    if W = [] then none else
    let q := childPrefix c W
    match split p q with
    | .equal =>
      -- transformExactMatch
      let T := W.under p
      match Kids.transform ks T with
      | none => none
      | some ks' =>
        match T.get [], v with
        | some (.update x), some _ => some (some (.node p (some x) ks'))
        | some .delete, some _ => collapse p ks'
        | some (.insert x), none => some (some (.node p (some x) ks'))
        | some _, _ => none
        | none, some _ => some (some (.node p v ks'))
        | none, none => collapse p ks'
    | .keyLonger c' _ =>
      -- transformChildLonger: every write goes beneath the child for `c'`
      let T := W.under p
      if c' ∈ ks.keys then
        match Kids.batchOld ks T with
        | none => none
        | some ks' =>
          if c' ∉ ks'.keys ∧ v = none then collapse p ks' else some (some (.node p v ks'))
      else
        match insertAll c' T with
        | none => none
        | some n => some (some (.node p v (ks.ins c' n)))
    | .keyShorter e rest =>
      -- transformPrefixLonger: the node, cut after `q`, is the one existing
      -- child of a value-less node with prefix `q`
      let T := W.under q
      match Kids.transform (.cons e (.node (e :: rest) v ks) .nil) T with
      | none => none
      | some ks' =>
        match T.get [] with
        | some (.insert x) => some (some (.node q (some x) ks'))
        | some _ => none
        | none => collapse q ks'
    | .diverge cm a _ b pb =>
      -- transformDivergent
      match insertAll a ((W.under cm).at a) with
      | none => none
      | some n => some (some (.node cm none ((Kids.cons b (.node (b :: pb) v ks) .nil).ins a n)))
termination_by t ws => (ws.tot, t.weight)
decreasing_by
  all_goals simp_wf
  all_goals
    have h2 := Batch.tot_at_le c ws
    first
    | have h1 := Batch.tot_under_lt (q := c :: p') (by simp) (Batch.at c ws)
      have hne : ¬ Batch.at c ws = [] := by assumption
      simp only [hne, ite_false] at h1
      exact lex_left (by omega)
    | have h1 := Batch.tot_under_lt (q := childPrefix c (Batch.at c ws)) (by simp [childPrefix])
        (Batch.at c ws)
      have hne : ¬ Batch.at c ws = [] := by assumption
      simp only [hne, ite_false] at h1
      exact lex_left (by omega)

/-- cashew `transformChildren`: transform each existing child that has
writes, keep the others, and add a child built by `insertAll` for each new
character. -/
def Kids.transform (ks : Kids K V D) (T : Batch K V) : Option (Kids K V D) :=
  match Kids.batchOld ks T with
  | none => none
  | some ks1 => insertKids T (T.heads.filter (· ∉ ks.keys)) ks1
termination_by (T.tot, ks.weight + 1)
decreasing_by
  all_goals simp_wf
  exact lex_right (Nat.le_refl _) (by omega)

/-- The existing children: each with writes beneath it is transformed (and
dropped if it is deleted), the others are kept as they are. -/
def Kids.batchOld : Kids K V D → Batch K V → Option (Kids K V D)
  | .nil, _ => some .nil
  | .cons c t rest, T =>
    match Kids.batchOld rest T with
    | none => none
    | some rest' =>
      if T.at c = [] then some (.cons c t rest')
      else
        match Trie.batch t (T.at c) with
        | none => none
        | some none => some rest'
        | some (some t') => some (.cons c t' rest')
termination_by ks T => (T.tot, ks.weight)
decreasing_by
  all_goals simp_wf
  all_goals first
    | exact lex_right (Nat.le_refl _) (by simp only [Kids.weight]; omega)
    | exact lex_right (Batch.tot_at_le _ _) (by simp only [Kids.weight]; omega)
end

/-- cashew `MerkleDictionary.transform(transforms:)`: a write at the empty key
is refused, the root never collapses, and `count` moves by the writes'
deltas. -/
def Root.batch (ws : Batch K V) (s : Root K V D) : Option (Root K V D) :=
  if ws.get [] = none then
    match Kids.transform s.kids ws with
    | none => none
    | some ks => some ⟨s.count + ws.delta, ks⟩
  else none

/-! ## The proof -/

/-- The paths a child is proven against (cashew `childPaths`:
`traverseChild`, with this node's own proof removed). -/
def Batch.childPaths (c : K) (E : Batch K V) : Batch K V := E.at c

/-- A child every write beneath which is a deletion: it may disappear. -/
def Batch.allDelete (E : Batch K V) (c : K) : Bool :=
  !(E.at c).isEmpty && (E.at c).all (·.2.isDelete)

/-- cashew `shouldExpandForBatchedDeletion`: whether the node, with value `v`,
children `ks` and the paths `E` beneath it, may be left without a value and
with one child, which a collapse must then read. The paths a child sees here
also hold the node's own proof (`traverseChild`), but the node's own proof is
then absent or a deletion, which changes neither count. -/
def expands (v : Option V) (ks : Kids K V D) (E : Batch K V) : Bool :=
  let del := (E.get []).any Op.isDelete
  if v.isSome && !del then false
  else (del || 0 < ks.keys.countP E.allDelete) && ks.keys.countP (!E.allDelete ·) ≤ 1

/-- A node resolved with its children's nodes (`resolveChildren` on a child
header). -/
def Trie.deep (H : Enc K V D → D) : Trie K V D → Trie K V D
  | .stub d => .stub d
  | .node p v ks => .node p v (ks.shallows H)

/-- `resolveGrandchildren`. -/
def Kids.deeps (H : Enc K V D → D) : Kids K V D → Kids K V D
  | .nil => .nil
  | .cons c t rest => .cons c (t.deep H) (rest.deeps H)

/-- No update or deletion beneath a character that has no child
(`proofForChildren` on a missing child). -/
def Batch.freshOk (ks : Kids K V D) (E : Batch K V) : Bool :=
  (E.heads.filter (· ∉ ks.keys)).all fun c => !(E.childPaths c).any (·.2.needsValue)

mutual
/-- cashew `RadixNode.proof(paths:)`, applied by Lattice to the trie
`resolve(paths:)` resolved along every key (`.targeted`): the partial trie
the transform then runs on, built from the full trie (the fetcher). A node is
resolved when a key reaches it; `deep` says it arrived with its children
resolved too (its parent expanded). An unresolved child is a stub. `none`:
`proof()` refuses. -/
def Trie.prove (H : Enc K V D → D) (deep : Bool) : Trie K V D → Batch K V → Option (Trie K V D)
  | .stub _, _ => none
  | .node p v ks, T =>
    let E := T.under p
    if E = [] then
      if T.any (·.2.needsValue) then none
      else some (.node p v (if deep then ks.shallows H else ks.stubs H))
    else if (T.filter fun w => w.1 ≠ [] ∧ dropPrefix p w.1 = none).any (·.2.needsValue) then none
    else
      match E.get [], v with
      | some (.update _), none => none
      | some (.insert _), some _ => none
      | own, _ =>
        let x := match own with
          | some (.update _) => false
          | some (.insert _) => false
          | _ => expands v ks E
        if E.freshOk ks then
          match Kids.prove H x deep ks E with
          | none => none
          | some ks' => some (.node p v ks')
        else none

/-- `proofForChildren` over the existing children: a child with paths
beneath it is proven against them (arriving resolved with its children when
this node expanded); the others stay as this node holds them. -/
def Kids.prove (H : Enc K V D → D) (x deep : Bool) : Kids K V D → Batch K V → Option (Kids K V D)
  | .nil, _ => some .nil
  | .cons c t rest, E =>
    match Kids.prove H x deep rest E with
    | none => none
    | some rest' =>
      if E.at c = [] then
        some (.cons c (if x then t.deep H else if deep then t.shallow H else .stub (t.digest H)) rest')
      else
        match Trie.prove H x t (E.childPaths c) with
        | none => none
        | some t' => some (.cons c t' rest')
end

/-- cashew `MerkleDictionary.proof(paths:)`. -/
def Root.prove (H : Enc K V D → D) (ws : Batch K V) (s : Root K V D) : Option (Root K V D) :=
  if ws.get [] = none ∧ ws.freshOk s.kids then
    match Kids.prove H false false s.kids ws with
    | none => none
    | some ks => some ⟨s.count, ks⟩
  else none

end Lattice.Merkle
