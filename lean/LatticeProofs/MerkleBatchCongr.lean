import LatticeProofs.MerkleBatch
import LatticeProofs.MerkleLemmas

/-! A partial trie below a full one: the batch on the partial trie, when it
succeeds, gives a result below the full trie's (helpers for
`MerkleBatchProofs.lean`). -/

set_option linter.unusedSectionVars false

namespace Lattice.Merkle

variable {K V D : Type} {H : Enc K V D → D}

mutual
/-- `p` is `t` with some subtrees replaced by stubs naming their digests. -/
def Trie.Le (H : Enc K V D → D) : Trie K V D → Trie K V D → Prop
  | .stub d, t => d = t.digest H
  | .node p v ks, .node p' v' ks' => p = p' ∧ v = v' ∧ Kids.Le H ks ks'
  | .node _ _ _, .stub _ => False

def Kids.Le (H : Enc K V D → D) : Kids K V D → Kids K V D → Prop
  | .nil, .nil => True
  | .cons c t rest, .cons c' t' rest' => c = c' ∧ Trie.Le H t t' ∧ Kids.Le H rest rest'
  | _, _ => False
end

/-- Two batch results, the first below the second. -/
def OLe (H : Enc K V D → D) : Option (Trie K V D) → Option (Trie K V D) → Prop
  | none, none => True
  | some a, some b => Trie.Le H a b
  | _, _ => False

/-- A partial root below a full one. -/
def Root.Le (H : Enc K V D → D) (p s : Root K V D) : Prop := p.count = s.count ∧ Kids.Le H p.kids s.kids

mutual
theorem Trie.Le.refl : ∀ t : Trie K V D, Trie.Le H t t
  | .stub _ => rfl
  | .node _ _ ks => ⟨rfl, rfl, Kids.Le.refl ks⟩
theorem Kids.Le.refl : ∀ ks : Kids K V D, Kids.Le H ks ks
  | .nil => trivial
  | .cons _ t rest => ⟨rfl, Trie.Le.refl t, Kids.Le.refl rest⟩
end

mutual
theorem Trie.Le.digest : ∀ {t t' : Trie K V D}, Trie.Le H t t' → t.digest H = t'.digest H
  | .stub _, _, h => h
  | .node _ _ ks, .node _ _ ks', h => by
    obtain ⟨rfl, rfl, hk⟩ := h
    simp only [Trie.digest, Kids.Le.digests hk]
  | .node _ _ _, .stub _, h => h.elim
theorem Kids.Le.digests : ∀ {ks ks' : Kids K V D}, Kids.Le H ks ks' → ks.digests H = ks'.digests H
  | .nil, .nil, _ => rfl
  | .cons _ t rest, .cons _ t' rest', h => by
    obtain ⟨rfl, ht, hr⟩ := h
    simp only [Kids.digests, Trie.Le.digest ht, Kids.Le.digests hr]
  | .nil, .cons _ _ _, h => h.elim
  | .cons _ _ _, .nil, h => h.elim
end

theorem Kids.Le.keys : ∀ {ks ks' : Kids K V D}, Kids.Le H ks ks' → ks.keys = ks'.keys
  | .nil, .nil, _ => rfl
  | .cons _ _ rest, .cons _ _ rest', h => by
    obtain ⟨rfl, -, hr⟩ := h
    simp only [Kids.keys, Kids.Le.keys hr]
  | .nil, .cons _ _ _, h => h.elim
  | .cons _ _ _, .nil, h => h.elim

theorem Root.Le.digest {p s : Root K V D} (h : Root.Le H p s) : p.digest H = s.digest H := by
  simp only [Root.digest, h.1, Kids.Le.digests h.2]

mutual
/-- Equal digests and no collision put a partial trie below a full one. -/
theorem Trie.le_of_digest : ∀ {p s : Trie K V D}, NoCollision H (p.HasEnc H) (s.HasEnc H) →
    s.Full → p.digest H = s.digest H → Trie.Le H p s
  | .stub _, _, _, _, hd => hd
  | .node _ _ ks, s, hH, hs, hd => by
    obtain ⟨ks', rfl, hk, hf⟩ := node_digest_inv hH hs hd
    exact ⟨rfl, rfl, Kids.le_of_digests hH.kids hf hk⟩
theorem Kids.le_of_digests : ∀ {ks ks' : Kids K V D}, NoCollision H (ks.HasEnc H) (ks'.HasEnc H) →
    ks'.Full → ks.digests H = ks'.digests H → Kids.Le H ks ks'
  | .nil, ks', _, _, hd => by obtain rfl := digests_nil_inv hd; trivial
  | .cons _ t rest, ks', hH, hf, hd => by
    obtain ⟨t', rest', rfl, h1, h2⟩ := digests_cons_inv hd
    exact ⟨rfl, Trie.le_of_digest hH.head hf.1 h1, Kids.le_of_digests hH.tail hf.2 h2⟩
end

theorem Root.le_of_digest {p s : Root K V D} (hH : NoCollision H (p.HasEnc H) (s.HasEnc H))
    (hs : s.Full) (hd : p.digest H = s.digest H) : Root.Le H p s := by
  have := hH _ _ (Or.inl rfl) (Or.inl rfl) hd
  simp only [Enc.root.injEq] at this
  exact ⟨this.1, Kids.le_of_digests (hH.mono (fun _ h => Or.inr h) (fun _ h => Or.inr h)) hs this.2⟩

variable [DecidableEq K] [LT K] [DecidableRel (α := K) (· < ·)]

theorem Kids.ins_le {c : K} {t t' : Trie K V D} (ht : Trie.Le H t t') :
    ∀ {ks ks' : Kids K V D}, Kids.Le H ks ks' → Kids.Le H (ks.ins c t) (ks'.ins c t')
  | .nil, .nil, _ => ⟨rfl, ht, trivial⟩
  | .cons c1 _ _, .cons _ _ _, h => by
    obtain ⟨rfl, h1, h2⟩ := h
    simp only [Kids.ins]
    split
    · exact ⟨rfl, ht, rfl, h1, h2⟩
    · exact ⟨rfl, h1, Kids.ins_le ht h2⟩
  | .nil, .cons _ _ _, h => h.elim
  | .cons _ _ _, .nil, h => h.elim

theorem collapse_le {p : List K} {ks ks' : Kids K V D} (hk : Kids.Le H ks ks')
    {r : Option (Trie K V D)} (h : collapse p ks = some r) :
    ∃ r', collapse p ks' = some r' ∧ OLe H r r' := by
  match ks, ks', hk, h with
  | .nil, .nil, _, h =>
    simp only [collapse, Option.some.injEq] at h; subst h; exact ⟨none, rfl, trivial⟩
  | .cons c (.node p' v' kk) .nil, .cons _ t' .nil, hk, h =>
    obtain ⟨rfl, ht, -⟩ := hk
    match t', ht with
    | .node _ _ kk', ht =>
      obtain ⟨rfl, rfl, hkk⟩ := ht
      simp only [collapse, Option.some.injEq] at h; subst h
      exact ⟨_, rfl, rfl, rfl, hkk⟩
  | .cons c (.stub _) .nil, _, _, h => simp [collapse] at h
  | .cons c t (.cons c2 t2 rest), .cons _ t' (.cons _ t2' rest'), hk, h =>
    obtain ⟨rfl, h1, rfl, h3, h4⟩ := hk
    simp only [collapse, Option.some.injEq] at h; subst h
    exact ⟨_, rfl, rfl, rfl, rfl, h1, rfl, h3, h4⟩
  | .cons _ _ .nil, .nil, hk, _ => exact hk.elim
  | .cons _ _ .nil, .cons _ _ (.cons _ _ _), hk, _ => exact hk.2.2.elim
  | .cons _ _ (.cons _ _ _), .nil, hk, _ => exact hk.elim
  | .cons _ _ (.cons _ _ _), .cons _ _ .nil, hk, _ => exact hk.2.2.elim
  | .nil, .cons _ _ _, hk, _ => exact hk.elim

theorem insertKids_le (T : Batch K V) :
    ∀ (chs : List K) {ks ks' r : Kids K V D}, Kids.Le H ks ks' → insertKids T chs ks = some r →
      ∃ r', insertKids T chs ks' = some r' ∧ Kids.Le H r r'
  | [], ks, ks', r, hk, h => by
    rw [insertKids] at h ⊢; simp only [Option.some.injEq] at h; subst h; exact ⟨_, rfl, hk⟩
  | ch :: chs, ks, ks', r, hk, h => by
    rw [insertKids] at h ⊢
    cases h1 : insertKids T chs ks with
    | none => rw [h1] at h; simp at h
    | some k1 =>
      obtain ⟨k1', e1, e2⟩ := insertKids_le T chs hk h1
      rw [e1]
      cases h2 : (insertAll ch (T.at ch) : Option (Trie K V D)) with
      | none => rw [h1, h2] at h; simp at h
      | some t =>
        rw [h1, h2] at h; simp only [Option.some.injEq] at h; subst h
        exact ⟨_, rfl, Kids.ins_le (Trie.Le.refl t) e2⟩

theorem settle_le {p : List K} {v : Option V} {ks1 ks1' : Kids K V D} {g : Option (Op V)}
    {r : Option (Trie K V D)} (hk : Kids.Le H ks1 ks1')
    (h : (match (generalizing := false) g, v with
        | some (.update x), some _ => some (some (.node p (some x) ks1))
        | some .delete, some _ => collapse p ks1
        | some (.insert x), none => some (some (.node p (some x) ks1))
        | some _, _ => none
        | none, some _ => some (some (.node p v ks1))
        | none, none => collapse p ks1) = some r) :
    ∃ r', (match (generalizing := false) g, v with
        | some (.update x), some _ => some (some (.node p (some x) ks1'))
        | some .delete, some _ => collapse p ks1'
        | some (.insert x), none => some (some (.node p (some x) ks1'))
        | some _, _ => none
        | none, some _ => some (some (.node p v ks1'))
        | none, none => collapse p ks1') = some r' ∧ OLe H r r' := by
  cases g with
  | none =>
    cases v with
    | none => exact collapse_le hk h
    | some _ =>
      simp only [Option.some.injEq] at h; subst h; exact ⟨_, rfl, rfl, rfl, hk⟩
  | some o =>
    cases o <;> cases v <;> simp only [Option.some.injEq, reduceCtorEq] at h
    all_goals first
      | exact collapse_le hk h
      | (subst h; exact ⟨_, rfl, rfl, rfl, hk⟩)

theorem settle_short_le {q : List K} {ks1 ks1' : Kids K V D} {g : Option (Op V)}
    {r : Option (Trie K V D)} (hk : Kids.Le H ks1 ks1')
    (h : (match (generalizing := false) g with
        | some (.insert x) => some (some (Trie.node q (some x) ks1))
        | some _ => none
        | none => collapse q ks1) = some r) :
    ∃ r', (match (generalizing := false) g with
        | some (.insert x) => some (some (Trie.node q (some x) ks1'))
        | some _ => none
        | none => collapse q ks1') = some r' ∧ OLe H r r' := by
  cases g with
  | none => exact collapse_le hk h
  | some o =>
    cases o <;> simp only [Option.some.injEq, reduceCtorEq] at h
    subst h; exact ⟨_, rfl, rfl, rfl, hk⟩

mutual
theorem Trie.batch_le (p s : Trie K V D) (ws : Batch K V) (hle : Trie.Le H p s) :
    ∀ r, p.batch ws = some r → ∃ r', s.batch ws = some r' ∧ OLe H r r' := by
  match p, s, hle with
  | .stub _, _, _ => intro r h; rw [Trie.batch] at h; simp at h
  | .node _ _ _, .stub _, hle => exact hle.elim
  | .node [] _ _, .node _ _ _, _ => intro r h; rw [Trie.batch] at h; simp at h
  | .node (c :: p') v ks, .node _ _ ks', hle =>
    obtain ⟨rfl, rfl, hk⟩ := hle
    have hkeys := hk.keys
    rw [Trie.batch, Trie.batch]
    by_cases hW : ws.at c = []
    · simp [hW]
    simp only [hW, ite_false]
    cases hsp : split (c :: p') (childPrefix c (ws.at c)) with
    | equal =>
      simp only
      intro r h
      cases ht : ks.transform ((ws.at c).under (c :: p')) with
      | none => rw [ht] at h; simp at h
      | some ks1 =>
        rw [ht] at h; dsimp only at h
        obtain ⟨ks1', e1, e2⟩ := Kids.transform_le ks ks' _ hk ks1 ht
        rw [e1]; dsimp only
        exact settle_le e2 h
    | keyLonger c' r' =>
      simp only [← hkeys]
      split
      · intro r h
        cases hb : ks.batchOld ((ws.at c).under (c :: p')) with
        | none => rw [hb] at h; simp at h
        | some ks1 =>
          rw [hb] at h; dsimp only at h
          obtain ⟨ks1', e1, e2⟩ := Kids.batchOld_le ks ks' _ hk ks1 hb
          rw [e1]; dsimp only
          rw [← e2.keys]
          split
          · split at h
            · exact collapse_le e2 h
            · contradiction
          · split at h
            · contradiction
            · simp only [Option.some.injEq] at h; subst h; exact ⟨_, rfl, rfl, rfl, e2⟩
      · intro r h
        cases hi : (insertAll c' ((ws.at c).under (c :: p')) : Option (Trie K V D)) with
        | none => rw [hi] at h; simp at h
        | some n =>
          rw [hi] at h; dsimp only at h; simp only [Option.some.injEq] at h; subst h
          exact ⟨_, rfl, rfl, rfl, Kids.ins_le (Trie.Le.refl n) hk⟩
    | keyShorter e rest =>
      simp only
      intro r h
      cases ht : Kids.transform (.cons e (.node (e :: rest) v ks) .nil)
          ((ws.at c).under (childPrefix c (ws.at c))) with
      | none => rw [ht] at h; simp at h
      | some ks1 =>
        rw [ht] at h; dsimp only at h
        obtain ⟨ks1', e1, e2⟩ := Kids.transform_le (.cons e (.node (e :: rest) v ks) .nil)
          (.cons e (.node (e :: rest) v ks') .nil) _ ⟨rfl, ⟨rfl, rfl, hk⟩, trivial⟩ ks1 ht
        rw [e1]; dsimp only
        exact settle_short_le e2 h
    | diverge cm a ka b pb =>
      simp only
      intro r h
      cases hi : (insertAll a (((ws.at c).under cm).at a) : Option (Trie K V D)) with
      | none => rw [hi] at h; simp at h
      | some n =>
        rw [hi] at h; dsimp only at h; simp only [Option.some.injEq] at h; subst h
        exact ⟨_, rfl, rfl, rfl,
          Kids.ins_le (Trie.Le.refl n) (⟨rfl, ⟨rfl, rfl, hk⟩, trivial⟩ :
            Kids.Le H (.cons b (.node (b :: pb) v ks) .nil) (.cons b (.node (b :: pb) v ks') .nil))⟩
termination_by (ws.tot, p.weight)
decreasing_by
  all_goals simp_wf
  all_goals
    have h2 := Batch.tot_at_le c ws
    first
    | have h1 := Batch.tot_under_lt (q := c :: p') (by simp) (Batch.at c ws)
      simp only [hW, ite_false] at h1
      exact lex_left (by omega)
    | have h1 := Batch.tot_under_lt (q := childPrefix c (Batch.at c ws)) (by simp [childPrefix])
        (Batch.at c ws)
      simp only [hW, ite_false] at h1
      exact lex_left (by omega)

theorem Kids.transform_le (ks ks' : Kids K V D) (T : Batch K V) (hk : Kids.Le H ks ks') :
    ∀ r, ks.transform T = some r → ∃ r', ks'.transform T = some r' ∧ Kids.Le H r r' := by
  intro r h
  rw [Kids.transform] at h ⊢
  cases hb : ks.batchOld T with
  | none => rw [hb] at h; simp at h
  | some ks1 =>
    rw [hb] at h; dsimp only at h
    obtain ⟨ks1', e1, e2⟩ := Kids.batchOld_le ks ks' T hk ks1 hb
    rw [e1]; dsimp only
    rw [← hk.keys]
    exact insertKids_le T _ e2 h
termination_by (T.tot, ks.weight + 1)
decreasing_by
  all_goals simp_wf
  exact lex_right (Nat.le_refl _) (by omega)

theorem Kids.batchOld_le (ks ks' : Kids K V D) (T : Batch K V) (hk : Kids.Le H ks ks') :
    ∀ r, ks.batchOld T = some r → ∃ r', ks'.batchOld T = some r' ∧ Kids.Le H r r' := by
  match ks, ks', hk with
  | .nil, .nil, _ =>
    intro r h; rw [Kids.batchOld] at h ⊢; simp only [Option.some.injEq] at h; subst h
    exact ⟨_, rfl, trivial⟩
  | .nil, .cons _ _ _, hk => exact hk.elim
  | .cons _ _ _, .nil, hk => exact hk.elim
  | .cons c t rest, .cons _ t' rest', hk =>
    obtain ⟨rfl, ht, hr⟩ := hk
    intro r h
    rw [Kids.batchOld] at h ⊢
    cases hb : rest.batchOld T with
    | none => rw [hb] at h; simp at h
    | some r1 =>
      rw [hb] at h; dsimp only at h
      obtain ⟨r1', e1, e2⟩ := Kids.batchOld_le rest rest' T hr r1 hb
      rw [e1]; dsimp only
      by_cases hat : T.at c = []
      · simp only [hat, ite_true, Option.some.injEq] at h; subst h
        simp only [hat, ite_true]
        exact ⟨_, rfl, rfl, ht, e2⟩
      · simp only [hat, ite_false] at h ⊢
        cases htb : t.batch (T.at c) with
        | none => rw [htb] at h; simp at h
        | some x =>
          rw [htb] at h
          obtain ⟨x', f1, f2⟩ := Trie.batch_le t t' (T.at c) ht x htb
          rw [f1]
          match x, x', f2 with
          | none, none, _ => simp only [Option.some.injEq] at h; subst h; exact ⟨_, rfl, e2⟩
          | some a, some b, f2 =>
            simp only [Option.some.injEq] at h; subst h; exact ⟨_, rfl, rfl, f2, e2⟩
          | none, some _, f2 => exact f2.elim
          | some _, none, f2 => exact f2.elim
termination_by (T.tot, ks.weight)
decreasing_by
  all_goals simp_wf
  all_goals first
    | exact lex_right (Nat.le_refl _) (by simp only [Kids.weight]; omega)
    | exact lex_right (Batch.tot_at_le _ _) (by simp only [Kids.weight]; omega)
end

/-- The root batch on a partial root below a full one. -/
theorem Root.batch_le {p s p' : Root K V D} {ws : Batch K V} (hle : Root.Le H p s)
    (h : p.batch ws = some p') : ∃ s', s.batch ws = some s' ∧ Root.Le H p' s' := by
  unfold Root.batch at h ⊢
  split at h
  · next hg =>
    simp only [hg, ite_true]
    cases ht : p.kids.transform ws with
    | none => rw [ht] at h; simp at h
    | some ks =>
      rw [ht] at h; simp only [Option.some.injEq] at h; subst h
      obtain ⟨ks', e1, e2⟩ := Kids.transform_le p.kids s.kids ws hle.2 ks ht
      rw [e1]
      exact ⟨_, rfl, by simp only [hle.1], e2⟩
  · simp at h

end Lattice.Merkle
