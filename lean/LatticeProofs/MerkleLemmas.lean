import LatticeProofs.Merkle

/-! Helper lemmas for `MerkleProofs.lean`. -/

set_option linter.unusedSectionVars false

namespace Lattice.Merkle

variable {K V D : Type} {H : Enc K V D → D}

/-! ## Equal digests, equal resolved contents -/

theorem node_digest_inv (hH : Function.Injective H) {p : List K} {v : Option V}
    {ks : Kids K V D} {t : Trie K V D} (ht : t.Full)
    (hd : (Trie.node p v ks).digest H = t.digest H) :
    ∃ ks', t = .node p v ks' ∧ ks.digests H = ks'.digests H ∧ ks'.Full := by
  cases t with
  | stub d => exact ht.elim
  | node p' v' ks' =>
    simp only [Trie.digest] at hd
    have := hH hd
    simp only [Enc.node.injEq] at this
    obtain ⟨rfl, rfl, h⟩ := this
    exact ⟨ks', rfl, h, ht⟩

theorem digests_cons_inv {c : K} {t : Trie K V D} {rest ks' : Kids K V D}
    (hd : (Kids.cons c t rest).digests H = ks'.digests H) :
    ∃ t' rest', ks' = .cons c t' rest' ∧ t.digest H = t'.digest H ∧
      rest.digests H = rest'.digests H := by
  cases ks' with
  | nil => simp [Kids.digests] at hd
  | cons c' t' rest' =>
    simp only [Kids.digests, List.cons.injEq, Prod.mk.injEq] at hd
    obtain ⟨⟨rfl, h1⟩, h2⟩ := hd
    exact ⟨t', rest', rfl, h1, h2⟩

theorem digests_nil_inv {ks' : Kids K V D} (hd : (Kids.nil : Kids K V D).digests H = ks'.digests H) :
    ks' = .nil := by
  cases ks' with
  | nil => rfl
  | cons => simp [Kids.digests] at hd

/-! ## Reads -/

variable [DecidableEq K]

mutual
theorem Trie.lookup_full : ∀ (t : Trie K V D) (k : List K), t.Full → t.lookup k ≠ .unknown
  | .stub _, _, h => h.elim
  | .node p v ks, k, h => by
    simp only [Trie.lookup]
    split
    · simp
    · cases v <;> simp [Read.ofOption]
    · exact Kids.lookup_full ks _ _ h
theorem Kids.lookup_full : ∀ (ks : Kids K V D) (c : K) (r : List K), ks.Full → ks.lookup c r ≠ .unknown
  | .nil, _, _, _ => by simp [Kids.lookup]
  | .cons c' t rest, c, r, h => by
    simp only [Kids.lookup]
    split
    · exact Trie.lookup_full t _ h.1
    · exact Kids.lookup_full rest c r h.2
end

mutual
theorem Trie.lookup_congr (hH : Function.Injective H) :
    ∀ (p t : Trie K V D) (k : List K), t.Full → p.digest H = t.digest H →
      p.lookup k ≠ .unknown → p.lookup k = t.lookup k
  | .stub _, _, _, _, _, hu => (hu rfl).elim
  | .node pp v ks, t, k, ht, hd, hu => by
    obtain ⟨ks', rfl, hks, hf⟩ := node_digest_inv hH ht hd
    simp only [Trie.lookup] at hu ⊢
    split
    · rfl
    · rfl
    · next c r heq =>
      rw [heq] at hu
      exact Kids.lookup_congr hH ks ks' c r hf hks hu
theorem Kids.lookup_congr (hH : Function.Injective H) :
    ∀ (ks ks' : Kids K V D) (c : K) (r : List K), ks'.Full → ks.digests H = ks'.digests H →
      ks.lookup c r ≠ .unknown → ks.lookup c r = ks'.lookup c r
  | .nil, ks', _, _, _, hd, _ => by rw [digests_nil_inv hd]
  | .cons c' t rest, ks', c, r, hf, hd, hu => by
    obtain ⟨t', rest', rfl, h1, h2⟩ := digests_cons_inv hd
    simp only [Kids.lookup] at hu ⊢
    split
    · next h => simp only [h, ite_true] at hu; exact Trie.lookup_congr hH t t' _ hf.1 h1 hu
    · next h => simp only [h, ite_false] at hu; exact Kids.lookup_congr hH rest rest' c r hf.2 h2 hu
end


/-! ## Writes -/

variable [LT K] [DecidableRel (α := K) (· < ·)]

theorem Kids.ins_congr {c : K} {t t' : Trie K V D} :
    ∀ {ks ks' : Kids K V D}, ks.digests H = ks'.digests H → t.digest H = t'.digest H →
      (ks.ins c t).digests H = (ks'.ins c t').digests H
  | .nil, ks', hd, ht => by
    obtain rfl := digests_nil_inv hd; simp [Kids.ins, Kids.digests, ht]
  | .cons c1 t1 rest, ks', hd, ht => by
    obtain ⟨t1', rest', rfl, h1, h2⟩ := digests_cons_inv hd
    simp only [Kids.ins]
    split
    · simp [Kids.digests, ht, h1, h2]
    · simp [Kids.digests, h1, Kids.ins_congr h2 ht]

theorem Kids.ins_full {c : K} {t : Trie K V D} (ht : t.Full) :
    ∀ {ks : Kids K V D}, ks.Full → (ks.ins c t).Full
  | .nil, _ => ⟨ht, trivial⟩
  | .cons c1 t1 rest, h => by
    simp only [Kids.ins]
    split
    · exact ⟨ht, h⟩
    · exact ⟨h.1, Kids.ins_full ht h.2⟩

theorem leaf_full (k : List K) (v : V) : (leaf k v : Trie K V D).Full := trivial

/-- Two results agree when both fail to the same deletion or name digests
that agree, and the second is fully resolved. -/
def Agree (H : Enc K V D → D) (r r' : Option (Trie K V D)) : Prop :=
  r.map (·.digest H) = r'.map (·.digest H) ∧ ∀ t ∈ r', t.Full

theorem collapse_congr (hH : Function.Injective H) {p : List K} {ks ks' : Kids K V D}
    (hf : ks'.Full) (hd : ks.digests H = ks'.digests H) {r : Option (Trie K V D)}
    (h : collapse p ks = some r) : ∃ r', collapse p ks' = some r' ∧ Agree H r r' := by
  match ks, h with
  | .nil, h =>
    obtain rfl := digests_nil_inv hd
    simp only [collapse, Option.some.injEq] at h
    subst h
    exact ⟨none, rfl, rfl, by simp⟩
  | .cons c (.node p' v' kk) .nil, h =>
    obtain ⟨t', rest', rfl, h1, h2⟩ := digests_cons_inv hd
    obtain rfl := digests_nil_inv h2
    obtain ⟨kk', rfl, hkk, hfk⟩ := node_digest_inv hH hf.1 h1
    simp only [collapse, Option.some.injEq] at h
    subst h
    exact ⟨_, rfl, by simp [Trie.digest, hkk], by simpa [Trie.Full] using hfk⟩
  | .cons c t (.cons c2 t2 rest), h =>
    obtain ⟨t', rest', rfl, h1, h2⟩ := digests_cons_inv hd
    obtain ⟨t2', rest2', rfl, h3, h4⟩ := digests_cons_inv h2
    simp only [collapse, Option.some.injEq] at h
    subst h
    refine ⟨some (.node p none (.cons c t' (.cons c2 t2' rest2'))), rfl, ?_, ?_⟩
    · simp [Trie.digest, Kids.digests, h1, h3, h4]
    · simpa [Trie.Full] using hf


theorem Agree.node {p : List K} {v : Option V} {ks ks' : Kids K V D}
    (hd : ks.digests H = ks'.digests H) (hf : ks'.Full) :
    Agree H (some (.node p v ks)) (some (.node p v ks')) :=
  ⟨by simp [Trie.digest, hd], by simpa [Trie.Full] using hf⟩

mutual
theorem Trie.apply_congr (hH : Function.Injective H) (o : Op V) :
    ∀ (p t : Trie K V D) (k : List K) (r : Option (Trie K V D)), t.Full →
      p.digest H = t.digest H → p.apply o k = some r → ∃ r', t.apply o k = some r' ∧ Agree H r r'
  | .stub _, _, _, _, _, _, h => by simp [Trie.apply] at h
  | .node pp v ks, t, k, r, ht, hd, h => by
    obtain ⟨ks', rfl, hks, hf⟩ := node_digest_inv hH ht hd
    simp only [Trie.apply] at h ⊢
    cases hs : split pp k with
    | equal =>
      simp only [hs] at h ⊢
      cases o <;> cases v <;> simp only [Option.some.injEq, reduceCtorEq] at h ⊢
      · subst h; exact ⟨_, rfl, Agree.node hks hf⟩
      · subst h; exact ⟨_, rfl, Agree.node hks hf⟩
      · exact collapse_congr hH hf hks h
    | keyLonger c rr =>
      simp only [hs] at h ⊢
      have ⟨hm, hdn⟩ := Kids.descend_congr hH o ks ks' c rr hf hks
      cases hdk : ks.descend o c rr with
      | missing =>
        rw [hdk] at h
        rw [hm hdk]
        cases o <;> simp only [Option.some.injEq, reduceCtorEq] at h ⊢
        subst h
        exact ⟨_, rfl, Agree.node (Kids.ins_congr hks rfl) (Kids.ins_full (leaf_full _ _) hf)⟩
      | fail => rw [hdk] at h; simp at h
      | done ks1 b =>
        rw [hdk] at h
        obtain ⟨ks1', h1, h2, h3⟩ := hdn ks1 b hdk
        rw [h1]
        simp only at h ⊢
        split
        · next hc => simp only [hc, and_self, ↓reduceIte] at h; exact collapse_congr hH h3 h2 h
        · next hc =>
          simp only [hc, ↓reduceIte, Option.some.injEq] at h
          subst h; exact ⟨_, rfl, Agree.node h2 h3⟩
    | keyShorter c rr =>
      simp only [hs] at h ⊢
      cases o <;> simp only [Option.some.injEq, reduceCtorEq] at h ⊢
      subst h
      exact ⟨_, rfl, ⟨by simp [Trie.digest, Kids.digests, hks], by simpa [Trie.Full, Kids.Full] using hf⟩⟩
    | diverge q a ka b pb =>
      simp only [hs] at h ⊢
      cases o <;> simp only [Option.some.injEq, reduceCtorEq] at h ⊢
      subst h
      refine ⟨_, rfl, Agree.node (Kids.ins_congr ?_ rfl) (Kids.ins_full (leaf_full _ _) ?_)⟩
      · simp [Kids.digests, Trie.digest, hks]
      · exact ⟨hf, trivial⟩
theorem Kids.descend_congr (hH : Function.Injective H) (o : Op V) :
    ∀ (ks ks' : Kids K V D) (c : K) (rr : List K), ks'.Full → ks.digests H = ks'.digests H →
      (ks.descend o c rr = .missing → ks'.descend o c rr = .missing) ∧
      (∀ ks1 b, ks.descend o c rr = .done ks1 b →
        ∃ ks1', ks'.descend o c rr = .done ks1' b ∧ ks1.digests H = ks1'.digests H ∧ ks1'.Full)
  | .nil, ks', _, _, _, hd => by
    obtain rfl := digests_nil_inv hd
    exact ⟨fun _ => rfl, by simp [Kids.descend]⟩
  | .cons c' t rest, ks', c, rr, hf, hd => by
    obtain ⟨t', rest', rfl, h1, h2⟩ := digests_cons_inv hd
    simp only [Kids.descend]
    split
    · next hc =>
      refine ⟨fun h => by split at h <;> simp at h, fun ks1 b h => ?_⟩
      cases ha : t.apply o (c :: rr) with
      | none => rw [ha] at h; simp at h
      | some r =>
        obtain ⟨r', ha', hr, hrf⟩ := Trie.apply_congr hH o t t' (c :: rr) r hf.1 h1 ha
        rw [ha] at h; rw [ha']
        cases r with
        | none =>
          simp only [Step.done.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          cases r' with
          | none => exact ⟨_, rfl, h2, hf.2⟩
          | some _ => simp at hr
        | some t1 =>
          simp only [Step.done.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          cases r' with
          | none => simp at hr
          | some t1' =>
            simp only [Option.map_some, Option.some.injEq] at hr
            exact ⟨_, rfl, by simp [Kids.digests, hr, h2], hrf t1' rfl, hf.2⟩
    · have ⟨hm, hdn⟩ := Kids.descend_congr hH o rest rest' c rr hf.2 h2
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
          simp only [Step.done.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨ks2', e1, e2, e3⟩ := hdn ks2 b2 hr
          refine ⟨.cons c' t' ks2', by rw [e1], by simp [Kids.digests, h1, e2], hf.1, e3⟩
end

end Lattice.Merkle
