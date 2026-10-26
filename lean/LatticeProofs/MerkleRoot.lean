import LatticeProofs.MerkleCanon
import LatticeProofs.MerkleWitness

/-! The node-level lemmas lifted to a sub-state root (helpers for
`MerkleProofs.lean`). -/

set_option linter.unusedSectionVars false

namespace Lattice.Merkle

variable {K V D : Type} {H : Enc K V D → D}

theorem Root.digest_inv (hH : Function.Injective H) {s s' : Root K V D}
    (h : s.digest H = s'.digest H) :
    s.count = s'.count ∧ s.kids.digests H = s'.kids.digests H := by
  have := hH h
  simpa [Enc.root.injEq] using this

variable [DecidableEq K]

theorem Root.lookup_full {s : Root K V D} (hs : s.Full) (k : List K) : s.lookup k ≠ .unknown := by
  cases k with
  | nil => simp [Root.lookup]
  | cons c r => exact Kids.lookup_full _ c r hs

theorem Root.lookup_congr (hH : Function.Injective H) {p s : Root K V D} (hs : s.Full)
    (hd : p.digest H = s.digest H) {k : List K} (hu : p.lookup k ≠ .unknown) :
    p.lookup k = s.lookup k := by
  cases k with
  | nil => rfl
  | cons c r => exact Kids.lookup_congr hH _ _ c r hs (Root.digest_inv hH hd).2 hu

variable [LT K] [DecidableRel (α := K) (· < ·)]

theorem Root.apply_congr (hH : Function.Injective H) (o : Op V) {p s p' : Root K V D}
    {k : List K} (hs : s.Full) (hd : p.digest H = s.digest H) (h : p.apply o k = some p') :
    ∃ s', s.apply o k = some s' ∧ p'.digest H = s'.digest H ∧ s'.Full := by
  obtain ⟨hc, hks⟩ := Root.digest_inv hH hd
  cases k with
  | nil => simp [Root.apply] at h
  | cons c r =>
    have ⟨hm, hdn⟩ := Kids.descend_congr hH o p.kids s.kids c r hs hks
    simp only [Root.apply] at h ⊢
    cases hdp : p.kids.descend o c r with
    | missing =>
      rw [hdp] at h; rw [hm hdp]
      cases o <;> simp only [Option.some.injEq, reduceCtorEq] at h ⊢
      subst h
      exact ⟨_, rfl, by simp [Root.digest, hc, Kids.ins_congr hks rfl],
        Kids.ins_full (leaf_full _ _) hs⟩
    | fail => rw [hdp] at h; simp at h
    | done ks1 b =>
      rw [hdp] at h
      obtain ⟨ks1', e1, e2, e3⟩ := hdn ks1 b hdp
      rw [e1]
      simp only [Option.some.injEq] at h ⊢
      subst h
      exact ⟨_, rfl, by simp [Root.digest, hc, e2], e3⟩

theorem Root.apply_resolved (o : Op V) {s s' : Root K V D} {k : List K}
    (h : s.apply o k = some s') : s.lookup k ≠ .unknown := by
  cases k with
  | nil => simp [Root.apply] at h
  | cons c r =>
    apply Kids.descend_resolved o s.kids c r
    intro hf
    simp [Root.apply, hf] at h

theorem Root.apply_correct (ho : StrictOrder K) (o : Op V) {s s' : Root K V D} {k : List K}
    (hs : s.Canon) (h : s.apply o k = some s') :
    o.pre (s.lookup k).toOption ∧
    (∀ k', s'.lookup k' = if k' = k then .ofOption o.post else s.lookup k') ∧ s'.Canon := by
  obtain ⟨hks, hcount⟩ := hs
  cases k with
  | nil => simp [Root.apply] at h
  | cons c r =>
    simp only [Root.apply] at h
    simp only [Root.lookup]
    cases hd : s.kids.descend o c r with
    | missing =>
      rw [hd] at h
      have hn := Kids.descend_missing o hd
      cases o with
      | update _ => simp at h
      | delete => simp at h
      | insert x =>
        simp only [Option.some.injEq] at h; subst h
        refine ⟨by simp [Op.pre, Kids.lookup_not_mem hn, Read.toOption], fun k' => ?_, ?_, ?_⟩
        · cases k' with
          | nil => simp
          | cons y z =>
            simp only
            rw [Kids.lookup_ins hn]
            by_cases hy : c = y
            · subst hy
              rw [lookup_leaf, Kids.lookup_not_mem hn]
              by_cases hz : z = r
              · subst hz; simp [Op.post, Read.ofOption]
              · simp [hz]
            · simp [hy, Ne.symm hy]
        · exact Kids.canon_ins ho leaf_canon.2 leaf_canon.1 hks hn
        · simp [Kids.size_ins, leaf_size, hcount]
    | fail => rw [hd] at h; simp at h
    | done ks1 b =>
      rw [hd] at h
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨hpre, hlk, hsz, hcan, -, -⟩ := Kids.descend_correct ho o s.kids c r ks1 b hks hd
      refine ⟨hpre, fun k' => ?_, hcan, ?_⟩
      · cases k' with
        | nil => simp
        | cons y z => exact hlk y z
      · simp only; rw [hsz, hcount]

theorem Root.apply_complete (ho : StrictOrder K) (o : Op V) {s : Root K V D} {k : List K}
    (hs : s.Canon) (hk : k ≠ []) (hpre : o.pre (s.lookup k).toOption) : s.apply o k ≠ none := by
  cases k with
  | nil => exact absurd rfl hk
  | cons c r =>
    simp only [Root.lookup] at hpre
    have hnf := Kids.descend_complete ho o s.kids c r hs.1 hpre
    simp only [Root.apply]
    cases hd : s.kids.descend o c r with
    | missing =>
      rw [Kids.lookup_not_mem (Kids.descend_missing o hd)] at hpre
      cases o <;> simp_all [Op.pre, Read.toOption]
    | fail => exact absurd hd hnf
    | done => simp

theorem Root.canon_unique (ho : StrictOrder K) {s1 s2 : Root K V D} (h1 : s1.Canon)
    (h2 : s2.Canon) (hl : ∀ k, s1.lookup k = s2.lookup k) : s1 = s2 := by
  have hk : s1.kids = s2.kids :=
    Kids.canon_unique ho h1.1 h2.1 (fun c z => hl (c :: z))
  cases s1; cases s2
  simp only at hk; subst hk
  have : _ = _ := h1.2.trans h2.2.symm
  simp only at this; subst this; rfl

theorem Root.apply_witness (o : Op V) {s s' : Root K V D} {k : List K} (hs : s.Full)
    (h : s.apply o k = some s') : (s.witness H k).apply o k ≠ none := by
  cases k with
  | nil => simp [Root.apply] at h
  | cons c r =>
    have ⟨hm, hdn⟩ := Kids.descend_witness (H := H) o s.kids c r hs
    simp only [Root.apply, Root.witness] at h ⊢
    cases hd : s.kids.descend o c r with
    | missing =>
      rw [hd] at h; rw [hm hd]
      cases o <;> simp_all
    | fail => rw [hd] at h; simp at h
    | done ks1 b =>
      obtain ⟨ks1', b', e1, -⟩ := hdn ks1 b hd
      rw [e1]; simp

end Lattice.Merkle
