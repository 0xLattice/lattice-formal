import LatticeProofs.MerkleBatchCanon
import LatticeProofs.MerkleBatchCongr
import LatticeProofs.MerkleWitness

/-! The partial trie cashew's `proof(paths:)` builds for a batch: below the
full trie, built whenever the batch succeeds, and enough to run the batch
(helpers for `MerkleBatchProofs.lean`). -/

set_option linter.unusedSectionVars false

namespace Lattice.Merkle

variable {K V D : Type} [DecidableEq K] [LT K] [DecidableRel (α := K) (· < ·)]
variable {H : Enc K V D → D}

/-! ## The proof is below the full trie -/

theorem Kids.stubs_le : ∀ ks : Kids K V D, Kids.Le H (ks.stubs H) ks
  | .nil => trivial
  | .cons _ _ rest => ⟨rfl, rfl, Kids.stubs_le rest⟩

theorem Trie.shallow_le : ∀ t : Trie K V D, Trie.Le H (t.shallow H) t
  | .stub _ => rfl
  | .node _ _ ks => ⟨rfl, rfl, Kids.stubs_le ks⟩

theorem Kids.shallows_le : ∀ ks : Kids K V D, Kids.Le H (ks.shallows H) ks
  | .nil => trivial
  | .cons _ t rest => ⟨rfl, Trie.shallow_le t, Kids.shallows_le rest⟩

theorem Trie.deep_le : ∀ t : Trie K V D, Trie.Le H (t.deep H) t
  | .stub _ => rfl
  | .node _ _ ks => ⟨rfl, rfl, Kids.shallows_le ks⟩

mutual
theorem Trie.prove_le : ∀ (deep : Bool) (t : Trie K V D) (T : Batch K V) (t' : Trie K V D),
    Trie.prove H deep t T = some t' → Trie.Le H t' t
  | _, .stub _, _, _, h => by simp [Trie.prove] at h
  | deep, .node p v ks, T, t', h => by
    simp only [Trie.prove] at h
    split at h
    · split at h
      · simp at h
      · simp only [Option.some.injEq] at h; subst h
        refine ⟨rfl, rfl, ?_⟩
        cases deep
        · exact Kids.stubs_le ks
        · exact Kids.shallows_le ks
    · split at h
      · simp at h
      · split at h
        · simp at h
        · simp at h
        · split at h
          · cases hk : Kids.prove H _ deep ks (T.under p) with
            | none => rw [hk] at h; simp at h
            | some ks' =>
              rw [hk] at h; simp only [Option.some.injEq] at h; subst h
              exact ⟨rfl, rfl, Kids.prove_le _ deep ks _ ks' hk⟩
          · simp at h
theorem Kids.prove_le : ∀ (x deep : Bool) (ks : Kids K V D) (E : Batch K V) (ks' : Kids K V D),
    Kids.prove H x deep ks E = some ks' → Kids.Le H ks' ks
  | _, _, .nil, _, _, h => by simp only [Kids.prove, Option.some.injEq] at h; subst h; trivial
  | x, deep, .cons c t rest, E, ks', h => by
    simp only [Kids.prove] at h
    cases hr : Kids.prove H x deep rest E with
    | none => rw [hr] at h; simp at h
    | some rest' =>
      rw [hr] at h; dsimp only at h
      have ih := Kids.prove_le x deep rest E rest' hr
      split at h
      · simp only [Option.some.injEq] at h; subst h
        refine ⟨rfl, ?_, ih⟩
        cases x
        · cases deep
          · exact rfl
          · exact Trie.shallow_le t
        · exact Trie.deep_le t
      · cases ht : Trie.prove H x t (E.childPaths c) with
        | none => rw [ht] at h; simp at h
        | some t' =>
          rw [ht] at h; simp only [Option.some.injEq] at h; subst h
          exact ⟨rfl, Trie.prove_le x t _ t' ht, ih⟩
end

/-! ## The proof is built whenever the batch succeeds -/

theorem Op.not_pre_none {o : Op V} (h : o.needsValue = true) : ¬ o.pre none := by
  cases o <;> simp_all [Op.needsValue, Op.pre]

theorem Batch.drop_none_of_under_nil {p : List K} {T : Batch K V} (hE : T.under p = [])
    {w : List K × Op V} (hw : w ∈ T) : dropPrefix p w.1 = none := by
  cases h : dropPrefix p w.1 with
  | none => rfl
  | some r =>
    have : (r, w.2) ∈ T.under p := Batch.mem_under.2 (by rw [← dropPrefix_eq_some.1 h]; exact hw)
    rw [hE] at this; simp at this

theorem Batch.freshOk_false {ks : Kids K V D} {E : Batch K V} (h : E.freshOk ks = false) :
    ∃ w ∈ E, ∃ c z, w.1 = c :: z ∧ c ∉ ks.keys ∧ w.2.needsValue = true := by
  unfold Batch.freshOk at h
  rw [List.all_eq_false] at h
  obtain ⟨c, hc, hb⟩ := h
  rw [List.mem_filter] at hc
  obtain ⟨hc, hk⟩ := hc
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_eq_false, Batch.childPaths] at hb
  obtain ⟨⟨k, o⟩, hw, hv⟩ := List.any_eq_true.1 hb
  obtain ⟨hwE, hh⟩ := Batch.mem_at.1 hw
  cases k with
  | nil => simp at hh
  | cons c' z =>
    simp only [List.head?_cons, Option.some.injEq] at hh; subst hh
    exact ⟨_, hwE, c', z, rfl, by simpa using hk, hv⟩

mutual
theorem Trie.prove_none (ho : StrictOrder K) : ∀ (deep : Bool) (t : Trie K V D) (T : Batch K V),
    t.Canon → Trie.prove H deep t T = none → ∃ w ∈ T, ¬ w.2.pre (t.lookup w.1).toOption
  | _, .stub _, _, htc, _ => htc.elim
  | deep, .node p v ks, T, htc, h => by
    obtain ⟨-, -, hks⟩ := htc
    simp only [Trie.prove] at h
    split at h
    · next hE =>
      split at h
      · next ha =>
        obtain ⟨w, hw, hv⟩ := List.any_eq_true.1 ha
        refine ⟨w, hw, ?_⟩
        rw [lookup_node_none (Batch.drop_none_of_under_nil hE hw)]
        exact Op.not_pre_none hv
      · simp at h
    · next hE =>
      split at h
      · next ha =>
        obtain ⟨w, hw, hv⟩ := List.any_eq_true.1 ha
        obtain ⟨hw, -, hd⟩ := by simpa using List.mem_filter.1 hw
        refine ⟨w, hw, ?_⟩
        rw [lookup_node_none hd]
        exact Op.not_pre_none hv
      · have hown : ∀ o, (T.under p).get [] = some o → (p, o) ∈ T := fun o hg => by
          rw [Batch.get_under, List.append_nil] at hg; exact Batch.mem_of_get hg
        have hlp : (Trie.node p v ks).lookup p = .ofOption v :=
          lookup_node_nil (dropPrefix_eq_some.2 (List.append_nil _).symm)
        split at h
        · exact ⟨_, hown _ (by assumption), by rw [hlp]; simp [Op.pre, Read.ofOption, Read.toOption]⟩
        · exact ⟨_, hown _ (by assumption), by rw [hlp]; simp [Op.pre, Read.ofOption, Read.toOption]⟩
        · split at h
          · cases hk : Kids.prove H _ deep ks (T.under p) with
            | some ks' => rw [hk] at h; simp at h
            | none =>
              obtain ⟨⟨k, o⟩, hw, ⟨y, -, hy⟩, hp⟩ := Kids.prove_none ho _ deep ks (T.under p) hks hk
              cases k with
              | nil => simp at hy
              | cons y' z =>
                refine ⟨_, Batch.mem_under.1 hw, ?_⟩
                rw [lookup_node_cons (dropPrefix_append_self _ _)]
                exact hp
          · next hf =>
            obtain ⟨⟨k, o⟩, hw, c, z, rfl, hc, hv⟩ := Batch.freshOk_false (Bool.eq_false_of_ne_true hf)
            refine ⟨_, Batch.mem_under.1 hw, ?_⟩
            rw [lookup_node_cons (dropPrefix_append_self _ _), Kids.lookup_not_mem hc]
            exact Op.not_pre_none hv
theorem Kids.prove_none (ho : StrictOrder K) : ∀ (x deep : Bool) (ks : Kids K V D) (E : Batch K V),
    ks.Canon → Kids.prove H x deep ks E = none →
    ∃ w ∈ E, (∃ y ∈ ks.keys, w.1.head? = some y) ∧ ¬ w.2.pre (ks.read w.1).toOption
  | _, _, .nil, _, _, h => by simp [Kids.prove] at h
  | x, deep, .cons c t rest, E, ⟨h1, h2, h3, h4⟩, h => by
    have hnm : c ∉ rest.keys := fun h => ho.irrefl c (h4 c h)
    simp only [Kids.prove] at h
    cases hr : Kids.prove H x deep rest E with
    | none =>
      obtain ⟨⟨k, o⟩, hw, ⟨y, hy, hk⟩, hp⟩ := Kids.prove_none ho x deep rest E h3 hr
      cases k with
      | nil => simp at hk
      | cons y' z =>
        simp only [List.head?_cons, Option.some.injEq] at hk; subst hk
        have hyc : c ≠ y' := fun e => hnm (e ▸ hy)
        refine ⟨_, hw, ⟨y', by simp [Kids.keys, hy], rfl⟩, ?_⟩
        rw [Kids.read_cons, ite_eq_right_of_eq_false _ _ (eq_false hyc)]; exact hp
    | some rest' =>
      rw [hr] at h; dsimp only at h
      split at h
      · simp at h
      · cases ht : Trie.prove H x t (E.childPaths c) with
        | some _ => rw [ht] at h; simp at h
        | none =>
          obtain ⟨⟨k, o⟩, hw, hp⟩ := Trie.prove_none ho x t (E.childPaths c) h2 ht
          obtain ⟨hwE, hh⟩ := Batch.mem_at.1 hw
          cases k with
          | nil => simp at hh
          | cons y z =>
            simp only [List.head?_cons, Option.some.injEq] at hh; subst hh
            refine ⟨(y :: z, o), hwE, ⟨y, by simp [Kids.keys], rfl⟩, ?_⟩
            simpa [Kids.read_cons] using hp
end

theorem Root.prove_none (ho : StrictOrder K) {ws : Batch K V} {s : Root K V D} (hs : s.kids.Canon)
    (h : Root.prove H ws s = none) : ∃ w ∈ ws, w.1 = [] ∨ ¬ w.2.pre (s.toMap w.1) := by
  unfold Root.prove at h
  split at h
  · cases hk : Kids.prove H false false s.kids ws with
    | some _ => rw [hk] at h; simp at h
    | none =>
      obtain ⟨⟨k, o⟩, hw, ⟨y, -, hy⟩, hp⟩ := Kids.prove_none ho false false s.kids ws hs hk
      cases k with
      | nil => simp at hy
      | cons y' z => exact ⟨_, hw, Or.inr hp⟩
  · next hc =>
    by_cases hg : ws.get [] = none
    · have hf : ws.freshOk s.kids = false := by
        cases hf : ws.freshOk s.kids
        · rfl
        · exact absurd ⟨hg, hf⟩ hc
      obtain ⟨⟨k, o⟩, hw, c, z, rfl, hc, hv⟩ := Batch.freshOk_false hf
      refine ⟨_, hw, Or.inr ?_⟩
      show ¬ o.pre (s.kids.lookup c z).toOption
      rw [Kids.lookup_not_mem hc]; exact Op.not_pre_none hv
    · cases hg' : ws.get [] with
      | none => exact absurd hg' hg
      | some o => exact ⟨_, Batch.mem_of_get hg', Or.inl rfl⟩

/-! ## The proof suffices -/

theorem Trie.batch_isNode {t t' : Trie K V D} {ws : Batch K V} (h : t.batch ws = some (some t')) :
    t'.IsNode := by
  match t with
  | .stub _ => rw [Trie.batch] at h; simp at h
  | .node [] _ _ => rw [Trie.batch] at h; simp at h
  | .node (c :: p') v ks =>
    rw [Trie.batch] at h; dsimp only at h
    split at h
    · simp at h
    · split at h
      all_goals (repeat' split at h)
      all_goals first
        | (simp only [Option.some.injEq, reduceCtorEq] at h; done)
        | (simp only [Option.some.injEq] at h; subst h; trivial)
        | exact collapse_isNode h

theorem insertAll_isNode {c : K} {ws : Batch K V} {t : Trie K V D} (h : insertAll c ws = some t) :
    t.IsNode := by
  rw [insertAll] at h
  split at h
  · simp at h
  · dsimp only at h
    repeat' split at h
    all_goals first
      | (simp only [Option.some.injEq, reduceCtorEq] at h; done)
      | (simp only [Option.some.injEq] at h; subst h; trivial)

theorem insertKids_any (T : Batch K V) :
    ∀ (chs : List K) {ks r : Kids K V D}, insertKids T chs ks = some r → ∀ ks' : Kids K V D,
      ∃ r', insertKids T chs ks' = some r' ∧ (ks'.TopNodes → r'.TopNodes) ∧
        r'.length = ks'.length + chs.length
  | [], ks, r, h, ks' => by
    rw [insertKids] at h; exact ⟨ks', by rw [insertKids], id, rfl⟩
  | ch :: chs, ks, r, h, ks' => by
    rw [insertKids] at h
    cases h1 : insertKids T chs ks with
    | none => rw [h1] at h; simp at h
    | some k1 =>
      cases h2 : (insertAll ch (T.at ch) : Option (Trie K V D)) with
      | none => rw [h1, h2] at h; simp at h
      | some t =>
        obtain ⟨k1', e1, e2, e3⟩ := insertKids_any T chs h1 ks'
        refine ⟨k1'.ins ch t, by rw [insertKids, e1, h2], fun h => Kids.topNodes_ins
          (insertAll_isNode h2) (e2 h), by rw [Kids.length_ins, e3]; simp; omega⟩

theorem collapse_two {p : List K} {ks : Kids K V D} (h : 2 ≤ ks.length) : collapse p ks ≠ none := by
  match ks, h with
  | .nil, h => simp [Kids.length] at h
  | .cons _ _ .nil, h => simp [Kids.length] at h
  | .cons _ _ (.cons _ _ _), _ => simp [collapse]

theorem Kids.Le.length : ∀ {ks ks' : Kids K V D}, Kids.Le H ks ks' → ks.length = ks'.length
  | .nil, .nil, _ => rfl
  | .cons _ _ rest, .cons _ _ rest', h => by simp [Kids.length, Kids.Le.length h.2.2]
  | .nil, .cons _ _ _, h => h.elim
  | .cons _ _ _, .nil, h => h.elim

theorem Kids.prove_nil (d : Bool) : ∀ ks : Kids K V D,
    Kids.prove H false d ks [] = some (if d then ks.shallows H else ks.stubs H)
  | .nil => by cases d <;> rfl
  | .cons c t rest => by
    rw [Kids.prove, Kids.prove_nil d rest]
    cases d <;> simp [Batch.at, Kids.shallows, Kids.stubs]

theorem expands_nil {v : Option V} {ks : Kids K V D} : expands v ks [] = false := by
  simp [expands, Batch.get, Batch.allDelete, Batch.at]

/-- The batch's deletions may leave the node without a value and with one
child only when `expands` says so. -/
theorem expands_false {v : Option V} {ks : Kids K V D} {E : Batch K V}
    (hown : E.get [] = some .delete ∨ (E.get [] = none ∧ v = none))
    (hv : v = none → 2 ≤ ks.length) (h : expands v ks E = false) :
    2 ≤ ks.keys.countP (fun c => !E.allDelete c) := by
  have hl := Kids.length_eq_keys ks
  have hs : ks.keys.length = ks.keys.countP E.allDelete + ks.keys.countP (fun c => !E.allDelete c) := by
    have := List.length_eq_countP_add_countP (l := ks.keys) E.allDelete
    simpa using this
  unfold expands at h
  rcases hown with hg | ⟨hg, rfl⟩
  · simp [hg, Op.isDelete] at h
    omega
  · simp [hg] at h
    by_cases hx : ∃ x ∈ ks.keys, E.allDelete x = true
    · obtain ⟨x, hx, hd⟩ := hx; have := h x hx hd; omega
    · have h0 : ks.keys.countP E.allDelete = 0 :=
        List.countP_eq_zero.2 fun x hx' hd => hx ⟨x, hx', hd⟩
      have := hv rfl
      omega

/-- A child each of whose writes is a deletion is the only kind the batch
may drop. -/
theorem Kids.batchOld_survive (ho : StrictOrder K) : ∀ (ks : Kids K V D) (E : Batch K V),
    ks.Canon → E.Nodup → ∀ k1, ks.batchOld E = some k1 →
      ks.keys.countP (fun c => !E.allDelete c) ≤ k1.length
  | .nil, _, _, _, _, _ => by simp [Kids.keys]
  | .cons c t rest, E, ⟨h1, h2, h3, h4⟩, hn, k1, h => by
    rw [Kids.batchOld] at h
    cases hr : rest.batchOld E with
    | none => rw [hr] at h; simp at h
    | some r1 =>
      rw [hr] at h; dsimp only at h
      have ih := Kids.batchOld_survive ho rest E h3 hn r1 hr
      simp only [Kids.keys, List.countP_cons]
      split at h
      · simp only [Option.some.injEq] at h; subst h
        simp only [Kids.length]; split <;> omega
      · next hne =>
        cases ht : t.batch (E.at c) with
        | none => rw [ht] at h; simp at h
        | some y =>
          rw [ht] at h
          cases y with
          | some t' =>
            simp only [Option.some.injEq] at h; subst h
            simp only [Kids.length]; split <;> omega
          | none =>
            simp only [Option.some.injEq] at h; subst h
            have hall : E.allDelete c = true := by
              simp only [Batch.allDelete, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
                List.all_eq_true]
              refine ⟨hne, fun w hw => ?_⟩
              cases hd : w.2.isDelete
              · exfalso
                obtain ⟨-, l1, -⟩ := (Trie.batch_spec ho t (E.at c) c h2 h1 (Batch.nodup_at hn) hne
                  (fun w hw => (Batch.mem_at.1 hw).2)).2 none ht
                have := l1 w.1
                rw [Batch.upd_of_get_some (Batch.get_of_mem (Batch.nodup_at hn) hw)] at this
                cases ho' : w.2 <;> simp_all [Op.isDelete, Op.post, Trie.lookupOpt, Read.ofOption]
              · rfl
            simp [hall]; omega

/-- The shape of the proof at a node the batch reaches. -/
theorem Trie.prove_node {deep : Bool} {P : List K} {v : Option V} {ks : Kids K V D} {T : Batch K V}
    {tP : Trie K V D} (h : Trie.prove H deep (.node P v ks) T = some tP) :
    ∃ x ksP, tP = .node P v ksP ∧ Kids.prove H x deep ks (T.under P) = some ksP ∧
      ((T.under P).get [] = none ∨ (T.under P).get [] = some .delete →
        x = expands v ks (T.under P)) := by
  simp only [Trie.prove] at h
  split at h
  · next hE =>
    split at h
    · simp at h
    · simp only [Option.some.injEq] at h; subst h
      refine ⟨false, _, rfl, ?_, fun _ => by rw [hE, expands_nil]⟩
      rw [hE, Kids.prove_nil]
  · split at h
    · simp at h
    · split at h
      · simp at h
      · simp at h
      · next own _ h1 h2 =>
        split at h
        · cases hk : Kids.prove H _ deep ks (T.under P) with
          | none => rw [hk] at h; simp at h
          | some ks' =>
            rw [hk] at h; simp only [Option.some.injEq] at h; subst h
            refine ⟨_, ks', rfl, hk, fun hg => ?_⟩
            rcases hg with hg | hg <;> simp [hg]
        · simp at h

theorem settle_live {p : List K} {v : Option V} {ks1 ks1' : Kids K V D} {g : Option (Op V)}
    {r : Option (Trie K V D)}
    (h : (match (generalizing := false) g, v with
        | some (.update x), some _ => some (some (.node p (some x) ks1))
        | some .delete, some _ => collapse p ks1
        | some (.insert x), none => some (some (.node p (some x) ks1))
        | some _, _ => none
        | none, some _ => some (some (.node p v ks1))
        | none, none => collapse p ks1) = some r)
    (hcol : g = some .delete ∨ (g = none ∧ v = none) → collapse p ks1' ≠ none) :
    (match (generalizing := false) g, v with
        | some (.update x), some _ => some (some (.node p (some x) ks1'))
        | some .delete, some _ => collapse p ks1'
        | some (.insert x), none => some (some (.node p (some x) ks1'))
        | some _, _ => none
        | none, some _ => some (some (.node p v ks1'))
        | none, none => collapse p ks1') ≠ none := by
  cases g with
  | none =>
    cases v with
    | none => exact hcol (Or.inr ⟨rfl, rfl⟩)
    | some _ => simp
  | some o =>
    cases o <;> cases v <;> simp only [reduceCtorEq] at h
    all_goals first
      | exact hcol (Or.inl rfl)
      | simp

theorem settle_short_live {q : List K} {ks1 ks1' : Kids K V D} {g : Option (Op V)}
    {r : Option (Trie K V D)}
    (h : (match (generalizing := false) g with
        | some (.insert x) => some (some (Trie.node q (some x) ks1))
        | some _ => none
        | none => collapse q ks1) = some r)
    (hcol : collapse q ks1' ≠ none) :
    (match (generalizing := false) g with
        | some (.insert x) => some (some (Trie.node q (some x) ks1'))
        | some _ => none
        | none => collapse q ks1') ≠ none := by
  cases g with
  | none => exact hcol
  | some o => cases o <;> simp only [reduceCtorEq] at h <;> simp

mutual
/-- At a node of the proof whose children are proven against the writes `E`
beneath it, the batch `W` (any batch whose writes beneath the node are `E`)
succeeds on the proof when it succeeds on the full trie. -/
theorem Node.live (ho : StrictOrder K) (c0 : K) (p' : List K) (v : Option V)
    (ksF ksP : Kids K V D) (E W : Batch K V) (x deep : Bool)
    (hv : v ≠ none ∨ 2 ≤ ksF.length) (hks : ksF.Canon) (hn : W.Nodup) (hne : W ≠ [])
    (hc : ∀ w ∈ W, w.1.head? = some c0) (hE : W.under (c0 :: p') = E)
    (hpr : Kids.prove H x deep ksF E = some ksP)
    (hx : E.get [] = none ∨ E.get [] = some .delete → x = expands v ksF E)
    (r : Option (Trie K V D)) (hr : (Trie.node (c0 :: p') v ksF).batch W = some r) :
    (Trie.node (c0 :: p') v ksP).batch W ≠ none := by
  have hle := Kids.prove_le x deep ksF E ksP hpr
  have hW : W.at c0 = W := Batch.at_of_all hc
  have hEn : E.Nodup := hE ▸ Batch.nodup_under hn
  have hq := childPrefix_prefix hc
  have K1 := fun k1 hb => Kids.prove_live ho x deep ksF ksP E hks hEn hpr k1 hb
  -- the children the proof keeps match the full trie's, one for one
  have hK : ∀ k1, ksF.batchOld E = some k1 → ∃ k1', ksP.batchOld E = some k1' ∧
      (x = true ∨ deep = true → k1'.TopNodes) ∧ k1'.length = k1.length ∧ k1'.keys = k1.keys := by
    intro k1 hb
    obtain ⟨k1', e1, e2⟩ := K1 k1 hb
    obtain ⟨k1'', f1, f2⟩ := Kids.batchOld_le ksP ksF E hle k1' e1
    rw [hb, Option.some.injEq] at f1; subst f1
    exact ⟨k1', e1, e2, f2.length, f2.keys⟩
  -- without resolved children, the collapse finds at least two
  have hwide : ∀ k1, ksF.batchOld E = some k1 → x = false →
      (E.get [] = some .delete ∨ (E.get [] = none ∧ v = none)) → 2 ≤ k1.length := by
    intro k1 hb hx0 hown
    have h1 := expands_false hown (fun h0 => hv.resolve_left (by simp [h0]))
      (by rw [← hx (hown.elim Or.inr fun h => Or.inl h.1)]; exact hx0)
    have h2 := Kids.batchOld_survive ho ksF E hks hEn k1 hb
    omega
  have hs := split_holds (c0 :: p') (childPrefix c0 W)
  rw [Trie.batch]; dsimp only; rw [hW]
  rw [Trie.batch] at hr; dsimp only at hr; rw [hW] at hr
  simp only [hne, ite_false] at hr ⊢
  revert hr
  cases hsp : split (c0 :: p') (childPrefix c0 W) with
  | equal =>
    dsimp only; rw [hE]; intro hr
    cases ht : ksF.transform E with
    | none => rw [ht] at hr; simp at hr
    | some k2 =>
      rw [ht] at hr; dsimp only at hr
      rw [Kids.transform] at ht
      cases hb : ksF.batchOld E with
      | none => rw [hb] at ht; simp at ht
      | some k1 =>
        rw [hb] at ht; dsimp only at ht
        obtain ⟨k1', e1, e2, e3, -⟩ := hK k1 hb
        obtain ⟨k2', g1, g2, g3⟩ := insertKids_any E _ ht k1'
        have hT : ksP.transform E = some k2' := by
          rw [Kids.transform, e1]; dsimp only; rw [hle.keys]; exact g1
        rw [hT]; dsimp only
        refine settle_live hr fun hown => ?_
        by_cases hxd : x = true ∨ deep = true
        · exact collapse_topNodes (g2 (e2 hxd))
        · apply collapse_two
          have := hwide k1 hb (by cases x <;> simp_all) hown
          omega
  | keyLonger c' r' =>
    rw [hsp] at hs; simp only [Split.Holds] at hs
    have hg0 : E.get [] = none := by
      rw [← hE, Batch.get_under, List.append_nil, Batch.get_eq_none]
      intro w hw he
      obtain ⟨u, hu⟩ := hq w hw
      rw [hs, he] at hu; simp at hu
    dsimp only; rw [hE, hle.keys]; intro hr
    split
    · next hck =>
      simp only [hck, ite_true] at hr
      cases hb : ksF.batchOld E with
      | none => rw [hb] at hr; simp at hr
      | some k1 =>
        rw [hb] at hr; dsimp only at hr
        obtain ⟨k1', e1, e2, e3, e4⟩ := hK k1 hb
        rw [e1]; dsimp only; rw [e4]
        split
        · next hcv =>
          by_cases hxd : x = true ∨ deep = true
          · exact collapse_topNodes (e2 hxd)
          · apply collapse_two
            have := hwide k1 hb (by cases x <;> simp_all) (Or.inr ⟨hg0, hcv.2⟩)
            omega
        · simp
    · next hck =>
      simp only [hck, ite_false] at hr
      cases hi : (insertAll c' E : Option (Trie K V D)) with
      | none => rw [hi] at hr; simp at hr
      | some n => simp
  | keyShorter e rest =>
    rw [hsp] at hs; simp only [Split.Holds] at hs
    dsimp only; intro hr
    cases ht : Kids.transform (.cons e (.node (e :: rest) v ksF) .nil) (W.under (childPrefix c0 W)) with
    | none => rw [ht] at hr; simp at hr
    | some k2 =>
      rw [ht] at hr; dsimp only at hr
      rw [Kids.transform] at ht
      cases hb : Kids.batchOld (.cons e (.node (e :: rest) v ksF) .nil) (W.under (childPrefix c0 W)) with
      | none => rw [hb] at ht; simp at ht
      | some k1 =>
        rw [hb] at ht; dsimp only at ht
        -- the cut node, transformed on the proof
        have hk1 : ∃ k1', Kids.batchOld (.cons e (.node (e :: rest) v ksP) .nil)
            (W.under (childPrefix c0 W)) = some k1' ∧ k1'.TopNodes := by
          rw [Kids.batchOld] at hb ⊢
          rw [Kids.batchOld] at hb ⊢
          dsimp only at hb ⊢
          split
          · exact ⟨_, rfl, trivial, trivial⟩
          · next hat =>
            simp only [hat, ite_false] at hb
            cases hy : Trie.batch (.node (e :: rest) v ksF) ((W.under (childPrefix c0 W)).at e) with
            | none => rw [hy] at hb; simp at hb
            | some y =>
              have hl := Node.live ho e rest v ksF ksP E ((W.under (childPrefix c0 W)).at e) x deep
                hv hks (Batch.nodup_at (Batch.nodup_under hn)) hat (fun w hw => (Batch.mem_at.1 hw).2)
                (by rw [Batch.under_at, Batch.under_under, ← hs, hE]) hpr hx y hy
              cases hy' : Trie.batch (.node (e :: rest) v ksP) ((W.under (childPrefix c0 W)).at e) with
              | none => exact absurd hy' hl
              | some y' =>
                cases y' with
                | none => exact ⟨_, rfl, trivial⟩
                | some t'' => exact ⟨_, rfl, Trie.batch_isNode hy', trivial⟩
        obtain ⟨k1', e1, e2⟩ := hk1
        obtain ⟨k2', g1, g2, -⟩ := insertKids_any _ _ ht k1'
        rw [Kids.transform, e1]; dsimp only
        rw [show (Kids.cons e (Trie.node (e :: rest) v ksP) Kids.nil).keys =
          (Kids.cons e (Trie.node (e :: rest) v ksF) Kids.nil).keys from rfl, g1]
        dsimp only
        exact settle_short_live hr (collapse_topNodes (g2 e2))
  | diverge cm a ka b pb =>
    dsimp only; intro hr
    cases hi : (insertAll a ((W.under cm).at a) : Option (Trie K V D)) with
    | none => rw [hi] at hr; simp at hr
    | some n => simp
termination_by (W.tot, ksF.weight + 1)
decreasing_by
  all_goals simp_wf
  · have h1 := Batch.tot_under_lt (q := c0 :: p') (by simp) W
    rw [hE] at h1
    exact lex_right (by split at h1 <;> omega) (by omega)
  · have h1 := Batch.tot_under_lt (q := childPrefix c0 W) (by simp [childPrefix]) W
    have h2 := Batch.tot_at_le e (W.under (childPrefix c0 W))
    simp only [hne, ite_false] at h1
    exact lex_left (by omega)

/-- The children of a proof node, transformed: on the proof, the children the
batch touches succeed as on the full trie, and every child is resolved when
the node expanded or arrived resolved with its children. -/
theorem Kids.prove_live (ho : StrictOrder K) (x deep : Bool) (ksF ksP : Kids K V D)
    (E : Batch K V) (hks : ksF.Canon) (hn : E.Nodup) (hpr : Kids.prove H x deep ksF E = some ksP)
    (k1 : Kids K V D) (hb : ksF.batchOld E = some k1) :
    ∃ k1', ksP.batchOld E = some k1' ∧ (x = true ∨ deep = true → k1'.TopNodes) := by
  match ksF, hks, ksP, hpr, k1, hb with
  | .nil, _, ksP, hpr, _, _ =>
    simp only [Kids.prove, Option.some.injEq] at hpr; subst hpr
    exact ⟨.nil, by rw [Kids.batchOld], fun _ => trivial⟩
  | .cons c t rest, ⟨h1, h2, h3, h4⟩, ksP, hpr, k1, hb =>
    rw [Kids.prove] at hpr
    cases hr : Kids.prove H x deep rest E with
    | none => rw [hr] at hpr; simp at hpr
    | some rest' =>
      rw [hr] at hpr; dsimp only at hpr
      rw [Kids.batchOld] at hb
      cases hbr : rest.batchOld E with
      | none => rw [hbr] at hb; simp at hb
      | some r1 =>
        rw [hbr] at hb; dsimp only at hb
        obtain ⟨r1', e1, e2⟩ := Kids.prove_live ho x deep rest rest' E h3 hn hr r1 hbr
        match ht : t, h1, h2, hpr, hb with
        | .stub _, _, h2, _, _ => exact h2.elim
        | .node [] _ _, _, h2, _, _ => exact (h2.1 rfl).elim
        | .node (c1 :: p1) v1 ks1, h1, h2, hpr, hb =>
          simp only [Trie.HeadIs, List.head?_cons, Option.some.injEq] at h1; subst h1
          obtain ⟨-, hv1, hks1⟩ := h2
          split at hpr
          · next hat =>
            simp only [Option.some.injEq] at hpr; subst hpr
            refine ⟨_, by rw [Kids.batchOld, e1]; simp only [hat, ite_true]; rfl, fun hxd => ?_⟩
            simp only [Kids.TopNodes]
            refine ⟨?_, e2 hxd⟩
            cases x <;> cases deep <;> simp_all [Trie.deep, Trie.shallow, Trie.IsNode]
          · next hat =>
            cases htp : Trie.prove H x (.node (c1 :: p1) v1 ks1) (E.childPaths c1) with
            | none => rw [htp] at hpr; simp at hpr
            | some tP =>
              rw [htp] at hpr; simp only [Option.some.injEq] at hpr; subst hpr
              obtain ⟨x', ksP', rfl, hk, hx'⟩ := Trie.prove_node htp
              simp only [hat, ite_false] at hb
              cases hy : Trie.batch (.node (c1 :: p1) v1 ks1) (E.at c1) with
              | none => rw [hy] at hb; simp at hb
              | some y =>
                have hl := Node.live ho c1 p1 v1 ks1 ksP' _ (E.at c1) x' x hv1 hks1
                  (Batch.nodup_at hn) hat (fun w hw => (Batch.mem_at.1 hw).2) rfl hk hx' y hy
                cases hy' : Trie.batch (.node (c1 :: p1) v1 ksP') (E.at c1) with
                | none => exact absurd hy' hl
                | some y' =>
                  cases y' with
                  | none =>
                    exact ⟨r1', by rw [Kids.batchOld, e1]; dsimp only; simp only [hat, ite_false]; rw [hy'],
                      e2⟩
                  | some t'' =>
                    refine ⟨Kids.cons c1 t'' r1', by
                      rw [Kids.batchOld, e1]; dsimp only; simp only [hat, ite_false]; rw [hy'], fun hxd => ?_⟩
                    simp only [Kids.TopNodes]; exact ⟨Trie.batch_isNode hy', e2 hxd⟩
termination_by (E.tot, ksF.weight)
decreasing_by
  all_goals simp_wf
  · exact lex_right (Nat.le_refl _) (by simp only [Kids.weight]; omega)
  · exact lex_right (Batch.tot_at_le _ _) (by simp only [ht, Kids.weight, Trie.weight]; omega)
end

theorem Root.prove_le {ws : Batch K V} {s p : Root K V D} (h : Root.prove H ws s = some p) :
    Root.Le H p s := by
  unfold Root.prove at h
  split at h
  · cases hk : Kids.prove H false false s.kids ws with
    | none => rw [hk] at h; simp at h
    | some ks =>
      rw [hk] at h; simp only [Option.some.injEq] at h; subst h
      exact ⟨rfl, Kids.prove_le false false s.kids ws ks hk⟩
  · simp at h

theorem Root.prove_live (ho : StrictOrder K) {ws : Batch K V} {s p s' : Root K V D}
    (hs : s.kids.Canon) (hn : ws.Nodup) (hp : Root.prove H ws s = some p)
    (hb : s.batch ws = some s') : p.batch ws ≠ none := by
  unfold Root.prove at hp
  split at hp
  · next hc =>
    cases hk : Kids.prove H false false s.kids ws with
    | none => rw [hk] at hp; simp at hp
    | some ks =>
      rw [hk] at hp; simp only [Option.some.injEq] at hp; subst hp
      unfold Root.batch at hb ⊢
      simp only [hc.1, ite_true] at hb ⊢
      cases ht : s.kids.transform ws with
      | none => rw [ht] at hb; simp at hb
      | some k2 =>
        rw [Kids.transform] at ht
        cases hb1 : s.kids.batchOld ws with
        | none => rw [hb1] at ht; simp at ht
        | some k1 =>
          rw [hb1] at ht; dsimp only at ht
          obtain ⟨k1', e1, -⟩ := Kids.prove_live ho false false s.kids ks ws hs hn hk k1 hb1
          obtain ⟨k2', g1, -, -⟩ := insertKids_any ws _ ht k1'
          rw [Kids.transform, e1]; dsimp only
          rw [(Kids.prove_le false false s.kids ws ks hk).keys, g1]
          simp
  · simp at hp

end Lattice.Merkle
