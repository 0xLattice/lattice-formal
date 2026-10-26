import LatticeProofs.MerkleLemmas

/-! The partial trie resolving a write's path commits to the same root, and
the write succeeds on it whenever it succeeds on the full trie (helpers for
`MerkleProofs.lean`). -/

set_option linter.unusedSectionVars false

namespace Lattice.Merkle

variable {K V D : Type} {H : Enc K V D → D}

/-! ## Stubbing keeps digests -/

theorem Kids.digests_stubs : ∀ (ks : Kids K V D), (ks.stubs H).digests H = ks.digests H
  | .nil => rfl
  | .cons c t rest => by simp [Kids.stubs, Kids.digests, Trie.digest, Kids.digests_stubs rest]

theorem Trie.digest_shallow : ∀ (t : Trie K V D), (t.shallow H).digest H = t.digest H
  | .stub _ => rfl
  | .node p v ks => by simp [Trie.shallow, Trie.digest, Kids.digests_stubs]

theorem Kids.digests_shallows : ∀ (ks : Kids K V D), (ks.shallows H).digests H = ks.digests H
  | .nil => rfl
  | .cons c t rest => by
    simp [Kids.shallows, Kids.digests, Trie.digest_shallow, Kids.digests_shallows rest]

variable [DecidableEq K]

mutual
theorem Trie.digest_witness : ∀ (k : List K) (t : Trie K V D), (t.witness H k).digest H = t.digest H
  | _, .stub _ => rfl
  | k, .node p v ks => by
    simp only [Trie.witness, Trie.digest]
    split
    · rw [Kids.digests_witness]
    · rw [Kids.digests_shallows]
theorem Kids.digests_witness :
    ∀ (c : K) (r : List K) (ks : Kids K V D), (ks.witness H c r).digests H = ks.digests H
  | _, _, .nil => rfl
  | c, r, .cons c' t rest => by
    simp only [Kids.witness]
    split
    · simp [Kids.digests, Trie.digest_witness, Kids.digests_shallows]
    · simp [Kids.digests, Trie.digest_shallow, Kids.digests_witness c r rest]
end

theorem Root.digest_witness (k : List K) (s : Root K V D) : (s.witness H k).digest H = s.digest H := by
  cases k <;> simp [Root.witness, Root.digest, Kids.digests_shallows, Kids.digests_witness]

/-! ## The write succeeds on the witness -/

def Trie.IsNode : Trie K V D → Prop
  | .stub _ => False
  | .node _ _ _ => True

/-- Every child is resolved (its own children may be stubs). -/
def Kids.TopNodes : Kids K V D → Prop
  | .nil => True
  | .cons _ t rest => t.IsNode ∧ rest.TopNodes

theorem Kids.topNodes_shallows : ∀ {ks : Kids K V D}, ks.Full → (ks.shallows H).TopNodes
  | .nil, _ => trivial
  | .cons _ (.stub _) _, h => h.1.elim
  | .cons _ (.node _ _ _) rest, h => ⟨trivial, Kids.topNodes_shallows (ks := rest) h.2⟩

variable [LT K] [DecidableRel (α := K) (· < ·)]

theorem Kids.topNodes_ins {c : K} {t : Trie K V D} (ht : t.IsNode) :
    ∀ {ks : Kids K V D}, ks.TopNodes → (ks.ins c t).TopNodes
  | .nil, _ => ⟨ht, trivial⟩
  | .cons _ _ rest, h => by
    simp only [Kids.ins]
    split
    · exact ⟨ht, h⟩
    · exact ⟨h.1, Kids.topNodes_ins ht (ks := rest) h.2⟩

theorem collapse_topNodes {p : List K} {ks : Kids K V D} (h : ks.TopNodes) :
    collapse p ks ≠ none := by
  match ks, h with
  | .nil, _ => simp [collapse]
  | .cons _ (.stub _) .nil, h => exact h.1.elim
  | .cons _ (.node _ _ _) .nil, _ => simp [collapse]
  | .cons _ _ (.cons _ _ _), _ => simp [collapse]

theorem collapse_isNode {p : List K} {ks : Kids K V D} {t : Trie K V D}
    (h : collapse p ks = some (some t)) : t.IsNode := by
  match ks, h with
  | .nil, h => simp [collapse] at h
  | .cons _ (.stub _) .nil, h => simp [collapse] at h
  | .cons _ (.node _ _ _) .nil, h => simp only [collapse, Option.some.injEq] at h; subst h; trivial
  | .cons _ _ (.cons _ _ _), h => simp only [collapse, Option.some.injEq] at h; subst h; trivial

/-- A write leaves a node or deletes it. -/
theorem Trie.apply_isNode (o : Op V) {t t' : Trie K V D} {k : List K}
    (h : t.apply o k = some (some t')) : t'.IsNode := by
  cases t with
  | stub _ => simp [Trie.apply] at h
  | node pp v ks =>
    simp only [Trie.apply] at h
    split at h
    · split at h <;> first | (simp only [Option.some.injEq] at h; subst h; trivial)
                           | exact collapse_isNode h | simp at h
    · split at h
      · split at h
        · simp only [Option.some.injEq] at h; subst h; trivial
        · simp at h
      · simp at h
      · split at h
        · exact collapse_isNode h
        · simp only [Option.some.injEq] at h; subst h; trivial
    · split at h
      · simp only [Option.some.injEq] at h; subst h; trivial
      · simp at h
    · split at h
      · simp only [Option.some.injEq] at h; subst h; trivial
      · simp at h

mutual
theorem Trie.apply_witness (o : Op V) :
    ∀ (t : Trie K V D) (k : List K) (r : Option (Trie K V D)), t.Full → t.apply o k = some r →
      (t.witness H k).apply o k ≠ none
  | .stub _, _, _, hf, _ => hf.elim
  | .node pp v ks, k, r, hf, h => by
    have hs := split_holds pp k
    simp only [Trie.witness, Trie.apply] at h ⊢
    cases hsp : split pp k with
    | equal =>
      rw [hsp] at hs; simp only [Split.Holds] at hs; subst hs
      rw [dropPrefix_eq_some.2 (List.append_nil _).symm]
      simp only [hsp] at h ⊢
      cases o <;> cases v <;> simp_all [collapse_topNodes (Kids.topNodes_shallows (H := H) hf)]
    | keyLonger c rr =>
      rw [hsp] at hs; simp only [Split.Holds] at hs; subst hs
      rw [dropPrefix_append_self]
      simp only [hsp] at h ⊢
      have ⟨hm, hdn⟩ := Kids.descend_witness o ks c rr hf
      cases hd : ks.descend o c rr with
      | missing =>
        rw [hd] at h; rw [hm hd]
        cases o <;> simp_all
      | fail => rw [hd] at h; simp at h
      | done ks1 b =>
        obtain ⟨ks1', b', e1, e2⟩ := hdn ks1 b hd
        rw [e1]
        simp only
        split
        · exact collapse_topNodes e2
        · simp
    | keyShorter c rr =>
      simp only [hsp] at h ⊢
      cases o <;> simp_all
    | diverge q a ka b pb =>
      simp only [hsp] at h ⊢
      cases o <;> simp_all
theorem Kids.descend_witness (o : Op V) :
    ∀ (ks : Kids K V D) (c : K) (rr : List K), ks.Full →
      (ks.descend o c rr = .missing → (ks.witness H c rr).descend o c rr = .missing) ∧
      (∀ ks1 b, ks.descend o c rr = .done ks1 b →
        ∃ ks1' b', (ks.witness H c rr).descend o c rr = .done ks1' b' ∧ ks1'.TopNodes)
  | .nil, _, _, _ => ⟨fun _ => rfl, by simp [Kids.descend]⟩
  | .cons c' t rest, c, rr, hf => by
    simp only [Kids.witness]
    by_cases hcc : c' = c
    · subst hcc
      simp only [ite_true, Kids.descend]
      refine ⟨fun h => by split at h <;> simp at h, fun ks1 b h => ?_⟩
      cases ha : t.apply o (c' :: rr) with
      | none => rw [ha] at h; simp at h
      | some r =>
        have hw := Trie.apply_witness o t (c' :: rr) r hf.1 ha
        cases hwa : (t.witness H (c' :: rr)).apply o (c' :: rr) with
        | none => exact absurd hwa hw
        | some r' =>
          rw [ha] at h
          cases r' with
          | none => exact ⟨_, _, rfl, Kids.topNodes_shallows hf.2⟩
          | some t'' => exact ⟨_, _, rfl, Trie.apply_isNode o hwa, Kids.topNodes_shallows hf.2⟩
    · simp only [hcc, ite_false, Kids.descend]
      have ⟨hm, hdn⟩ := Kids.descend_witness o rest c rr hf.2
      have hsh : (t.shallow H).IsNode := by
        cases t with
        | stub _ => exact hf.1.elim
        | node _ _ _ => trivial
      refine ⟨fun h => ?_, fun ks1 b h => ?_⟩
      · cases hr : rest.descend o c rr with
        | missing => simp [hm hr]
        | fail => rw [hr] at h; simp at h
        | done => rw [hr] at h; simp at h
      · cases hr : rest.descend o c rr with
        | missing => rw [hr] at h; simp at h
        | fail => rw [hr] at h; simp at h
        | done ks2 b2 =>
          rw [hr] at h
          simp only [Step.done.injEq] at h; obtain ⟨rfl, rfl⟩ := h
          obtain ⟨ks2', b2', e1, e2⟩ := hdn ks2 b2 hr
          refine ⟨.cons c' (t.shallow H) ks2', b2', by rw [e1], hsh, e2⟩
end

end Lattice.Merkle
