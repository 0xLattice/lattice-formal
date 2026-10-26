import LatticeProofs.MerkleLemmas

/-! Canonical tries: writes keep the canonical form and do what they say on
the map (helpers for `MerkleProofs.lean`). -/

set_option linter.unusedSectionVars false

namespace Lattice.Merkle

variable {K V D : Type} [DecidableEq K] [LT K] [DecidableRel (α := K) (· < ·)]

def Trie.lookupOpt : Option (Trie K V D) → List K → Read V
  | none, _ => .absent
  | some t, k => t.lookup k

def Trie.sizeOpt : Option (Trie K V D) → Nat
  | none => 0
  | some t => t.size

@[simp] theorem Read.toOption_ofOption (x : Option V) : (Read.ofOption x).toOption = x := by
  cases x <;> rfl

theorem Read.ofOption_inj {x y : Option V} (h : Read.ofOption x = Read.ofOption y) : x = y := by
  have := congrArg Read.toOption h; simpa using this

@[simp] theorem Read.ofOption_ne_unknown (x : Option V) : Read.ofOption x ≠ .unknown := by
  cases x <;> simp [Read.ofOption]

/-! ## Children -/

theorem Kids.lookup_not_mem {c : K} {r : List K} :
    ∀ {ks : Kids K V D}, c ∉ ks.keys → ks.lookup c r = .absent
  | .nil, _ => rfl
  | .cons c' t rest, h => by
    simp only [Kids.keys, List.mem_cons, not_or] at h
    simp only [Kids.lookup, Ne.symm h.1, ite_false]
    exact Kids.lookup_not_mem h.2

theorem Kids.mem_keys_ins {c x : K} {t : Trie K V D} :
    ∀ {ks : Kids K V D}, x ∈ (ks.ins c t).keys ↔ x = c ∨ x ∈ ks.keys
  | .nil => by simp [Kids.ins, Kids.keys]
  | .cons c' t' rest => by
    simp only [Kids.ins]
    split
    · simp [Kids.keys]
    · simp only [Kids.keys, List.mem_cons, Kids.mem_keys_ins]
      constructor
      · rintro (h | h | h) <;> simp [h]
      · rintro (h | h | h) <;> simp [h]

theorem Kids.length_ins {c : K} {t : Trie K V D} :
    ∀ {ks : Kids K V D}, (ks.ins c t).length = ks.length + 1
  | .nil => rfl
  | .cons c' t' rest => by
    simp only [Kids.ins]
    split
    · rfl
    · simp [Kids.length, Kids.length_ins]

theorem Kids.size_ins {c : K} {t : Trie K V D} :
    ∀ {ks : Kids K V D}, (ks.ins c t).size = ks.size + t.size
  | .nil => by simp [Kids.ins, Kids.size]
  | .cons c' t' rest => by
    simp only [Kids.ins]
    split
    · simp [Kids.size]; omega
    · simp [Kids.size, Kids.size_ins]; omega

theorem Kids.lookup_ins {c x : K} {r : List K} {t : Trie K V D} :
    ∀ {ks : Kids K V D}, c ∉ ks.keys →
      (ks.ins c t).lookup x r = if c = x then t.lookup (x :: r) else ks.lookup x r
  | .nil, _ => by simp [Kids.ins, Kids.lookup]
  | .cons c' t' rest, h => by
    simp only [Kids.keys, List.mem_cons, not_or] at h
    simp only [Kids.ins]
    split
    · simp [Kids.lookup]
    · simp only [Kids.lookup, Kids.lookup_ins h.2]
      by_cases h1 : c' = x
      · subst h1; simp [h.1]
      · simp [h1]

theorem Kids.canon_ins (ho : StrictOrder K) {c : K} {t : Trie K V D}
    (ht : t.HeadIs c) (htc : t.Canon) :
    ∀ {ks : Kids K V D}, ks.Canon → c ∉ ks.keys → (ks.ins c t).Canon
  | .nil, _, _ => ⟨ht, htc, trivial, by simp [Kids.keys]⟩
  | .cons c' t' rest, h, hn => by
    simp only [Kids.keys, List.mem_cons, not_or] at hn
    simp only [Kids.ins]
    split
    · next hlt =>
      refine ⟨ht, htc, h, ?_⟩
      simp only [Kids.keys, List.mem_cons]
      rintro x (rfl | hx)
      · exact hlt
      · exact ho.trans hlt (h.2.2.2 x hx)
    · next hlt =>
      have hgt : c' < c := by
        rcases ho.total c c' with h1 | h1 | h1
        · exact absurd h1 hlt
        · exact absurd h1 hn.1
        · exact h1
      refine ⟨h.1, h.2.1, Kids.canon_ins ho ht htc h.2.2.1 hn.2, ?_⟩
      intro x hx
      rcases Kids.mem_keys_ins.1 hx with rfl | hx
      · exact hgt
      · exact h.2.2.2 x hx

theorem Kids.Canon.not_mem (ho : StrictOrder K) {c : K} {t : Trie K V D} {rest : Kids K V D}
    (h : (Kids.cons c t rest).Canon) : c ∉ rest.keys :=
  fun hc => ho.irrefl c (h.2.2.2 c hc)

/-! ## Reads on a canonical node -/

theorem Trie.lookup_headIs {c : K} {t : Trie K V D} (ht : t.HeadIs c) :
    ∀ {k : List K}, k.head? ≠ some c → t.lookup k = .absent := by
  intro k hk
  cases t with
  | stub _ => exact ht.elim
  | node p v ks =>
    simp only [Trie.HeadIs] at ht
    obtain ⟨p', rfl⟩ : ∃ p', p = c :: p' := by
      cases p with
      | nil => simp at ht
      | cons a p' => simp at ht; exact ⟨p', by rw [ht]⟩
    apply lookup_node_none
    cases k with
    | nil => rfl
    | cons a k => exact dropPrefix_cons_ne _ _ (fun h => hk (by simp [h]))

theorem lookup_node_val {p k : List K} {v v' : Option V} {ks : Kids K V D} :
    (Trie.node p v' ks).lookup k =
      if k = p then .ofOption v' else (Trie.node p v ks).lookup k := by
  cases h : dropPrefix p k with
  | none =>
    have : k ≠ p := fun e => by
      subst e; have := dropPrefix_append_self k []; simp [h] at this
    rw [lookup_node_none h, lookup_node_none h]; simp [this]
  | some r =>
    obtain rfl := dropPrefix_eq_some.1 h
    cases r with
    | nil => rw [lookup_node_nil h]; simp
    | cons c r =>
      rw [lookup_node_cons h, lookup_node_cons h]; simp

theorem lookup_node_append {p p' k : List K} {v : Option V} {ks : Kids K V D} :
    (Trie.node (p ++ p') v ks).lookup k =
      match dropPrefix p k with
      | none => .absent
      | some k2 => (Trie.node p' v ks).lookup k2 := by
  cases h : dropPrefix p k with
  | none => exact lookup_node_none (by simp [dropPrefix_append, h])
  | some k2 => simp [Trie.lookup, dropPrefix_append, h]


theorem lookup_node_none_nil {p k : List K} : (Trie.node p none (.nil : Kids K V D)).lookup k = .absent := by
  cases h : dropPrefix p k with
  | none => exact lookup_node_none h
  | some r =>
    cases r with
    | nil => rw [lookup_node_nil h]; rfl
    | cons c r => rw [lookup_node_cons h]; rfl

theorem ne_nil_of_head {p : List K} {c : K} (h : p.head? = some c) : p ≠ [] := by
  rintro rfl; simp at h

/-! ## Collapse -/

theorem collapse_correct {p : List K} {c0 : K} (hp : p.head? = some c0) :
    ∀ {ks : Kids K V D} {r : Option (Trie K V D)}, ks.Canon → collapse p ks = some r →
      (∀ k, Trie.lookupOpt r k = (Trie.node p none ks).lookup k) ∧
      Trie.sizeOpt r = ks.size ∧ (∀ t ∈ r, t.Canon ∧ t.HeadIs c0)
  | .nil, r, _, h => by
    simp only [collapse, Option.some.injEq] at h
    subst h
    exact ⟨fun k => lookup_node_none_nil.symm, rfl, by simp⟩
  | .cons c (.stub _) .nil, r, _, h => by simp [collapse] at h
  | .cons c (.node p' v' ks') .nil, r, hc, h => by
    simp only [collapse, Option.some.injEq] at h
    subst h
    obtain ⟨hh, ⟨hp', hv', hks'⟩, -, -⟩ := hc
    refine ⟨fun k => ?_, ?_, ?_⟩
    · simp only [Trie.lookupOpt]
      rw [lookup_node_append]
      cases h : dropPrefix p k with
      | none => simp [lookup_node_none h]
      | some k2 =>
        cases k2 with
        | nil =>
          rw [lookup_node_nil h]; simp only
          rw [Trie.lookup_headIs hh (k := []) (by simp)]; rfl
        | cons y z =>
          rw [lookup_node_cons h]
          simp only [Kids.lookup]
          split
          · next e => subst e; rfl
          · next e =>
            rw [Trie.lookup_headIs hh (by simpa [eq_comm] using e)]
    · simp [Trie.sizeOpt, Trie.size, Kids.size]
    · intro t ht
      simp only [Option.mem_def, Option.some.injEq] at ht
      subst ht
      refine ⟨⟨by simp [ne_nil_of_head hp], hv', hks'⟩, ?_⟩
      simp only [Trie.HeadIs]
      cases p with
      | nil => simp at hp
      | cons a p => simpa using hp
  | .cons c t (.cons c2 t2 rest), r, hc, h => by
    simp only [collapse, Option.some.injEq] at h
    subst h
    refine ⟨fun k => rfl, by simp [Trie.sizeOpt, Trie.size], ?_⟩
    intro t' ht
    simp only [Option.mem_def, Option.some.injEq] at ht
    subst ht
    exact ⟨⟨ne_nil_of_head hp, Or.inr (by simp [Kids.length]), hc⟩, hp⟩


theorem lookup_leaf {p k : List K} {x : V} :
    (leaf p x : Trie K V D).lookup k = if k = p then .found x else .absent := by
  unfold leaf
  rw [lookup_node_val (v := none), lookup_node_none_nil]; rfl

/-- A node whose children read differently only at `c :: rr` reads
differently only at `p ++ c :: rr`. -/
theorem lookup_node_kids {p : List K} {v : Option V} {ks ks1 : Kids K V D} {c : K}
    {rr : List K} {X : Read V}
    (h : ∀ y z, ks1.lookup y z = if y :: z = c :: rr then X else ks.lookup y z) (k' : List K) :
    (Trie.node p v ks1).lookup k' =
      if k' = p ++ c :: rr then X else (Trie.node p v ks).lookup k' := by
  cases hk : dropPrefix p k' with
  | none =>
    have : k' ≠ p ++ c :: rr := fun e => by subst e; simp [dropPrefix_append_self] at hk
    rw [lookup_node_none hk, lookup_node_none hk]; simp [this]
  | some r =>
    obtain rfl := dropPrefix_eq_some.1 hk
    cases r with
    | nil =>
      rw [lookup_node_nil hk, lookup_node_nil hk]; simp
    | cons y z =>
      rw [lookup_node_cons hk, lookup_node_cons hk, h]; simp only [List.append_right_inj]

theorem Kids.descend_missing (o : Op V) {c : K} {rr : List K} :
    ∀ {ks : Kids K V D}, ks.descend o c rr = .missing → c ∉ ks.keys
  | .nil, _ => by simp [Kids.keys]
  | .cons c' t rest, h => by
    simp only [Kids.descend] at h
    split at h
    · split at h <;> simp at h
    · next hc =>
      have : rest.descend o c rr = .missing := by
        revert h; cases rest.descend o c rr <;> simp
      simp [Kids.keys, Ne.symm hc, Kids.descend_missing o this]

theorem leaf_canon {c : K} {r : List K} {x : V} :
    (leaf (c :: r) x : Trie K V D).Canon ∧ (leaf (c :: r) x : Trie K V D).HeadIs c :=
  ⟨⟨by simp, by simp, trivial⟩, rfl⟩

theorem leaf_size {p : List K} {x : V} : (leaf p x : Trie K V D).size = 1 := by
  simp [leaf, Trie.size, Kids.size]


/-! ## A write on a canonical trie -/

mutual
theorem Trie.apply_correct (ho : StrictOrder K) (o : Op V) :
    ∀ (t : Trie K V D) (k : List K) (c0 : K) (r : Option (Trie K V D)),
      t.Canon → t.HeadIs c0 → k.head? = some c0 → t.apply o k = some r →
      o.pre (t.lookup k).toOption ∧
      (∀ k', Trie.lookupOpt r k' = if k' = k then .ofOption o.post else t.lookup k') ∧
      (Trie.sizeOpt r : Int) = t.size + o.delta ∧
      (∀ t' ∈ r, t'.Canon ∧ t'.HeadIs c0)
  | .stub _, _, _, _, hc, _, _, _ => hc.elim
  | .node pp v ks, k, c0, r, hc, hh, hk, h => by
    obtain ⟨hpp, hv, hks⟩ := hc
    have hs := split_holds pp k
    simp only [Trie.HeadIs] at hh
    simp only [Trie.apply] at h
    cases hsp : split pp k with
    | equal =>
      rw [hsp] at hs; simp only [Split.Holds] at hs; subst hs
      simp only [hsp] at h
      rw [lookup_node_nil (dropPrefix_eq_some.2 (List.append_nil _).symm)]
      cases o with
      | insert x =>
        cases v with
        | some _ => simp at h
        | none =>
          simp only [Option.some.injEq] at h; subst h
          refine ⟨rfl, fun k' => ?_, ?_, ?_⟩
          · simp only [Trie.lookupOpt]; rw [lookup_node_val (v := none)]; rfl
          · simp [Trie.sizeOpt, Trie.size, Op.delta]; omega
          · intro t' ht'; simp only [Option.mem_def, Option.some.injEq] at ht'; subst ht'
            exact ⟨⟨hpp, Or.inl (by simp), hks⟩, hh⟩
      | update x =>
        cases v with
        | none => simp at h
        | some y =>
          simp only [Option.some.injEq] at h; subst h
          refine ⟨by simp [Op.pre, Read.ofOption, Read.toOption], fun k' => ?_, ?_, ?_⟩
          · simp only [Trie.lookupOpt]; rw [lookup_node_val (v := some y)]; rfl
          · simp [Trie.sizeOpt, Trie.size, Op.delta]
          · intro t' ht'; simp only [Option.mem_def, Option.some.injEq] at ht'; subst ht'
            exact ⟨⟨hpp, Or.inl (by simp), hks⟩, hh⟩
      | delete =>
        cases v with
        | none => simp at h
        | some y =>
          simp only at h
          obtain ⟨h1, h2, h3⟩ := collapse_correct hh hks h
          refine ⟨by simp [Op.pre, Read.ofOption, Read.toOption], fun k' => ?_, ?_, h3⟩
          · rw [h1, lookup_node_val (v := some y)]; rfl
          · rw [h2]; simp [Trie.size, Op.delta]; omega
    | keyLonger c rr =>
      rw [hsp] at hs; simp only [Split.Holds] at hs; subst hs
      simp only [hsp] at h
      rw [lookup_node_cons (dropPrefix_append_self _ _)]
      cases hd : ks.descend o c rr with
      | missing =>
        rw [hd] at h
        have hn := Kids.descend_missing o hd
        cases o with
        | update _ => simp at h
        | delete => simp at h
        | insert x =>
          simp only [Option.some.injEq] at h; subst h
          refine ⟨by simp [Op.pre, Kids.lookup_not_mem hn, Read.toOption], fun k' => ?_, ?_, ?_⟩
          · simp only [Trie.lookupOpt]
            apply lookup_node_kids _ k'
            intro y z
            rw [Kids.lookup_ins hn]
            by_cases hy : c = y
            · subst hy
              rw [lookup_leaf, Kids.lookup_not_mem hn]
              by_cases hz : z = rr
              · subst hz; simp [Op.post, Read.ofOption]
              · simp [hz]
            · simp [hy, Ne.symm hy]
          · simp [Trie.sizeOpt, Trie.size, Kids.size_ins, leaf_size, Op.delta]; omega
          · intro t' ht'; simp only [Option.mem_def, Option.some.injEq] at ht'; subst ht'
            refine ⟨⟨hpp, ?_, Kids.canon_ins ho leaf_canon.2 leaf_canon.1 hks hn⟩, hh⟩
            rcases hv with hv | hv
            · exact Or.inl hv
            · exact Or.inr (by rw [Kids.length_ins]; omega)
      | fail => rw [hd] at h; simp at h
      | done ks1 b =>
        rw [hd] at h
        obtain ⟨hpre, hlk, hsz, hcan, -, hlen⟩ := Kids.descend_correct ho o ks c rr ks1 b hks hd
        refine ⟨hpre, ?_⟩
        simp only at h
        split at h
        · next hb =>
          obtain ⟨rfl, rfl⟩ := hb
          obtain ⟨h1, h2, h3⟩ := collapse_correct hh hcan h
          refine ⟨fun k' => ?_, ?_, h3⟩
          · rw [h1]; exact lookup_node_kids hlk k'
          · rw [h2]; simp [Trie.size] at hsz ⊢; omega
        · next hb =>
          simp only [Option.some.injEq] at h; subst h
          refine ⟨fun k' => lookup_node_kids hlk k', ?_, ?_⟩
          · simp [Trie.sizeOpt, Trie.size]; omega
          · intro t' ht'; simp only [Option.mem_def, Option.some.injEq] at ht'; subst ht'
            refine ⟨⟨hpp, ?_, hcan⟩, hh⟩
            cases b with
            | false => simp at hlen; rw [hlen]; exact hv
            | true => exact Or.inl (fun e => hb ⟨rfl, e⟩)
    | keyShorter c rr =>
      rw [hsp] at hs; simp only [Split.Holds] at hs; subst hs
      simp only [hsp] at h
      rw [lookup_node_none (dropPrefix_of_keyShorter rfl)]
      cases o with
      | update _ => simp at h
      | delete => simp at h
      | insert x =>
        simp only [Option.some.injEq] at h; subst h
        refine ⟨rfl, fun k' => ?_, ?_, ?_⟩
        · simp only [Trie.lookupOpt]
          rw [lookup_node_append (p := k)]
          cases hk' : dropPrefix k k' with
          | none =>
            have : k' ≠ k := fun e => by subst e; simp [dropPrefix_eq_some.2 (List.append_nil k').symm] at hk'
            rw [lookup_node_none hk']; simp [this]
          | some r =>
            obtain rfl := dropPrefix_eq_some.1 hk'
            cases r with
            | nil => rw [lookup_node_nil hk']; simp [Op.post]
            | cons y z =>
              rw [lookup_node_cons hk']
              have hne : ¬ (k ++ y :: z = k) := by simp
              simp only [Kids.lookup, hne, ite_false]
              by_cases hy : c = y
              · subst hy; simp
              · simp only [hy, ite_false]
                rw [lookup_node_none (dropPrefix_cons_ne _ _ hy)]
        · simp [Trie.sizeOpt, Trie.size, Kids.size, Op.delta]; omega
        · intro t' ht'; simp only [Option.mem_def, Option.some.injEq] at ht'; subst ht'
          refine ⟨⟨ne_nil_of_head hk, Or.inl (by simp), ⟨rfl, ⟨by simp, hv, hks⟩, trivial,
            by simp [Kids.keys]⟩⟩, hk⟩
    | diverge q a ka b pb =>
      rw [hsp] at hs; simp only [Split.Holds] at hs
      obtain ⟨rfl, rfl, hab⟩ := hs
      simp only [hsp] at h
      rw [lookup_node_none (dropPrefix_of_diverge rfl rfl hab)]
      have hq : q.head? = some c0 := by
        cases q with
        | nil => simp at hk hh; exact absurd (hk.trans hh.symm) hab
        | cons x q => simpa using hk
      have hab' : a ∉ (Kids.cons b (Trie.node (b :: pb) v ks) .nil).keys := by
        simp [Kids.keys, hab]
      cases o with
      | update _ => simp at h
      | delete => simp at h
      | insert x =>
        simp only [Option.some.injEq] at h; subst h
        refine ⟨rfl, fun k' => ?_, ?_, ?_⟩
        · simp only [Trie.lookupOpt]
          rw [lookup_node_append (p := q)]
          cases hk' : dropPrefix q k' with
          | none =>
            have : k' ≠ q ++ a :: ka := fun e => by subst e; simp [dropPrefix_append_self] at hk'
            rw [lookup_node_none hk']; simp [this]
          | some r =>
            obtain rfl := dropPrefix_eq_some.1 hk'
            simp only [List.append_right_inj]
            cases r with
            | nil =>
              rw [lookup_node_nil hk', lookup_node_none (dropPrefix_cons_nil _ _)]; simp [Read.ofOption]
            | cons y z =>
              rw [lookup_node_cons hk', Kids.lookup_ins hab']
              by_cases hy : a = y
              · subst hy
                rw [lookup_leaf, lookup_node_none (dropPrefix_cons_ne _ _ (Ne.symm hab))]
                by_cases hz : z = ka
                · subst hz; simp [Op.post, Read.ofOption]
                · simp [hz]
              · simp only [hy, ite_false, Kids.lookup]
                have : ¬ (y :: z = a :: ka) := by simp [Ne.symm hy]
                simp only [this, ite_false]
                by_cases hy2 : b = y
                · simp [hy2]
                · simp only [hy2, ite_false]
                  rw [lookup_node_none (dropPrefix_cons_ne _ _ hy2)]
        · simp [Trie.sizeOpt, Trie.size, Kids.size_ins, leaf_size, Kids.size, Op.delta]
        · intro t' ht'; simp only [Option.mem_def, Option.some.injEq] at ht'; subst ht'
          refine ⟨⟨ne_nil_of_head hq, Or.inr (by simp [Kids.length_ins, Kids.length]), ?_⟩, hq⟩
          exact Kids.canon_ins ho leaf_canon.2 leaf_canon.1
            ⟨rfl, ⟨by simp, hv, hks⟩, trivial, by simp [Kids.keys]⟩ hab'

theorem Kids.descend_correct (ho : StrictOrder K) (o : Op V) :
    ∀ (ks : Kids K V D) (c : K) (rr : List K) (ks1 : Kids K V D) (b : Bool),
      ks.Canon → ks.descend o c rr = .done ks1 b →
      o.pre (ks.lookup c rr).toOption ∧
      (∀ y z, ks1.lookup y z = if y :: z = c :: rr then .ofOption o.post else ks.lookup y z) ∧
      (ks1.size : Int) = ks.size + o.delta ∧ ks1.Canon ∧ (∀ x ∈ ks1.keys, x ∈ ks.keys) ∧
      ks1.length + (if b then 1 else 0) = ks.length
  | .nil, _, _, _, _, _, h => by simp [Kids.descend] at h
  | .cons c' t rest, c, rr, ks1, b, hc, h => by
    simp only [Kids.descend] at h
    by_cases hcc : c' = c
    · subst hcc
      simp only [ite_true] at h
      have hl : (Kids.cons c' t rest).lookup c' rr = t.lookup (c' :: rr) := by simp [Kids.lookup]
      have hnm := Kids.Canon.not_mem ho hc
      cases ha : t.apply o (c' :: rr) with
      | none => rw [ha] at h; simp at h
      | some r =>
        rw [ha] at h
        obtain ⟨hpre, hlk, hsz, hcan⟩ := Trie.apply_correct ho o t (c' :: rr) c' r hc.2.1 hc.1 rfl ha
        rw [hl]
        refine ⟨hpre, ?_⟩
        cases r with
        | none =>
          simp only [Step.done.injEq] at h; obtain ⟨rfl, rfl⟩ := h
          refine ⟨fun y z => ?_, ?_, hc.2.2.1, by simp [Kids.keys]; intro x hx; exact Or.inr hx,
            by simp [Kids.length]⟩
          · simp only [Kids.lookup]
            by_cases hy : c' = y
            · subst hy
              have := hlk (c' :: z)
              simp only [Trie.lookupOpt] at this
              rw [Kids.lookup_not_mem hnm, this]
              simp
            · have : ¬ (y :: z = c' :: rr) := by simp [Ne.symm hy]
              simp [hy, this]
          · simp [Trie.sizeOpt] at hsz; simp [Kids.size]; omega
        | some t' =>
          simp only [Step.done.injEq] at h; obtain ⟨rfl, rfl⟩ := h
          obtain ⟨hc1, hc2⟩ := hcan t' rfl
          refine ⟨fun y z => ?_, ?_, ⟨hc2, hc1, hc.2.2.1, hc.2.2.2⟩, fun x hx => hx,
            by simp [Kids.length]⟩
          · simp only [Kids.lookup]
            by_cases hy : c' = y
            · subst hy
              have := hlk (c' :: z)
              simp only [Trie.lookupOpt] at this
              rw [this]; simp
            · have : ¬ (y :: z = c' :: rr) := by simp [Ne.symm hy]
              simp [hy, this]
          · simp [Trie.sizeOpt] at hsz; simp [Kids.size]; omega
    · simp only [hcc, ite_false] at h
      cases hr : rest.descend o c rr with
      | missing => rw [hr] at h; simp at h
      | fail => rw [hr] at h; simp at h
      | done ks2 b2 =>
        rw [hr] at h
        simp only [Step.done.injEq] at h; obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hpre, hlk, hsz, hcan, hkeys, hlen⟩ :=
          Kids.descend_correct ho o rest c rr ks2 b2 hc.2.2.1 hr
        have hl : (Kids.cons c' t rest).lookup c rr = rest.lookup c rr := by simp [Kids.lookup, hcc]
        rw [hl]
        refine ⟨hpre, fun y z => ?_, ?_, ⟨hc.1, hc.2.1, hcan, fun x hx => hc.2.2.2 x (hkeys x hx)⟩,
          ?_, ?_⟩
        · simp only [Kids.lookup]
          by_cases hy : c' = y
          · subst hy
            have : ¬ (c' :: z = c :: rr) := by simp [hcc]
            simp [this]
          · simp [hy, hlk]
        · simp [Kids.size]; omega
        · simp only [Kids.keys, List.mem_cons]
          rintro x (rfl | hx)
          · exact Or.inl rfl
          · exact Or.inr (hkeys x hx)
        · simp [Kids.length] at hlen ⊢; omega
end

mutual
theorem Trie.Canon.full : ∀ {t : Trie K V D}, t.Canon → t.Full
  | .stub _, h => h.elim
  | .node _ _ ks, h => Kids.Canon.full (ks := ks) h.2.2
theorem Kids.Canon.full : ∀ {ks : Kids K V D}, ks.Canon → ks.Full
  | .nil, _ => trivial
  | .cons _ t rest, h => ⟨Trie.Canon.full (t := t) h.2.1, Kids.Canon.full (ks := rest) h.2.2.1⟩
end

theorem collapse_ne_none {p : List K} {ks : Kids K V D} (h : ks.Canon) : collapse p ks ≠ none := by
  match ks, h with
  | .nil, _ => simp [collapse]
  | .cons _ (.stub _) .nil, h => exact h.2.1.elim
  | .cons _ (.node _ _ _) .nil, _ => simp [collapse]
  | .cons _ _ (.cons _ _ _), _ => simp [collapse]

/-! ## Completeness: a write whose precondition holds succeeds -/

mutual
theorem Trie.apply_complete (ho : StrictOrder K) (o : Op V) :
    ∀ (t : Trie K V D) (k : List K) (c0 : K), t.Canon → t.HeadIs c0 → k.head? = some c0 →
      o.pre (t.lookup k).toOption → t.apply o k ≠ none
  | .stub _, _, _, hc, _, _, _ => hc.elim
  | .node pp v ks, k, c0, hc, hh, hk, hpre => by
    obtain ⟨hpp, hv, hks⟩ := hc
    have hs := split_holds pp k
    simp only [Trie.apply]
    cases hsp : split pp k with
    | equal =>
      rw [hsp] at hs; simp only [Split.Holds] at hs; subst hs
      rw [lookup_node_nil (dropPrefix_eq_some.2 (List.append_nil _).symm)] at hpre
      cases o <;> cases v <;> simp_all [Op.pre, Read.ofOption, Read.toOption, collapse_ne_none]
    | keyLonger c rr =>
      rw [hsp] at hs; simp only [Split.Holds] at hs; subst hs
      rw [lookup_node_cons (dropPrefix_append_self _ _)] at hpre
      have hnf := Kids.descend_complete ho o ks c rr hks hpre
      cases hd : ks.descend o c rr with
      | missing =>
        have hn := Kids.descend_missing o hd
        rw [Kids.lookup_not_mem hn] at hpre
        cases o <;> simp_all [Op.pre, Read.toOption]
      | fail => exact absurd hd hnf
      | done ks1 b =>
        have hcan := (Kids.descend_correct ho o ks c rr ks1 b hks hd).2.2.2.1
        simp only [hd]
        split
        · exact collapse_ne_none hcan
        · simp
    | keyShorter c rr =>
      rw [hsp] at hs; simp only [Split.Holds] at hs; subst hs
      rw [lookup_node_none (dropPrefix_of_keyShorter rfl)] at hpre
      cases o <;> simp_all [Op.pre, Read.toOption]
    | diverge q a ka b pb =>
      rw [hsp] at hs; simp only [Split.Holds] at hs
      obtain ⟨rfl, rfl, hab⟩ := hs
      rw [lookup_node_none (dropPrefix_of_diverge rfl rfl hab)] at hpre
      cases o <;> simp_all [Op.pre, Read.toOption]
theorem Kids.descend_complete (ho : StrictOrder K) (o : Op V) :
    ∀ (ks : Kids K V D) (c : K) (rr : List K), ks.Canon → o.pre (ks.lookup c rr).toOption →
      ks.descend o c rr ≠ .fail
  | .nil, _, _, _, _ => by simp [Kids.descend]
  | .cons c' t rest, c, rr, hc, hpre => by
    simp only [Kids.descend]
    by_cases hcc : c' = c
    · subst hcc
      simp only [Kids.lookup, ite_true] at hpre
      have := Trie.apply_complete ho o t (c' :: rr) c' hc.2.1 hc.1 rfl hpre
      simp only [ite_true]
      cases ha : t.apply o (c' :: rr) with
      | none => exact absurd ha this
      | some r => cases r <;> simp
    · simp only [Kids.lookup, hcc, ite_false] at hpre ⊢
      have := Kids.descend_complete ho o rest c rr hc.2.2.1 hpre
      cases hr : rest.descend o c rr <;> simp_all
end

/-! ## Uniqueness: a canonical trie is a function of its map -/

theorem found_prefix {p k : List K} {v : Option V} {ks : Kids K V D} {x : V}
    (h : (Trie.node p v ks).lookup k = .found x) : ∃ r, k = p ++ r := by
  cases hk : dropPrefix p k with
  | none => rw [lookup_node_none hk] at h; cases h
  | some r => exact ⟨r, dropPrefix_eq_some.1 hk⟩

theorem head_of_found {c : K} {t : Trie K V D} (ht : t.HeadIs c) {k : List K} {x : V}
    (h : t.lookup k = .found x) : ∃ z, k = c :: z := by
  cases k with
  | nil => rw [Trie.lookup_headIs ht (by simp)] at h; cases h
  | cons a z =>
    by_cases ha : a = c
    · exact ⟨z, by rw [ha]⟩
    · rw [Trie.lookup_headIs ht (by simpa using ha)] at h; cases h

mutual
theorem Trie.exists_found : ∀ {t : Trie K V D}, t.Canon → ∃ k x, t.lookup k = .found x
  | .stub _, h => h.elim
  | .node p v ks, ⟨_, hv, hks⟩ => by
    cases v with
    | some x => exact ⟨p, x, lookup_node_nil (dropPrefix_eq_some.2 (List.append_nil _).symm)⟩
    | none =>
      have hne : ks ≠ .nil := by
        rintro rfl; simp [Kids.length] at hv
      obtain ⟨c, z, x, hx⟩ := Kids.exists_found hks hne
      exact ⟨p ++ c :: z, x, by rw [lookup_node_cons (dropPrefix_append_self _ _)]; exact hx⟩
theorem Kids.exists_found :
    ∀ {ks : Kids K V D}, ks.Canon → ks ≠ .nil → ∃ c z x, ks.lookup c z = .found x
  | .nil, _, h => absurd rfl h
  | .cons c t rest, hc, _ => by
    obtain ⟨k, x, hx⟩ := Trie.exists_found hc.2.1
    obtain ⟨z, rfl⟩ := head_of_found hc.1 hx
    exact ⟨c, z, x, by simp [Kids.lookup, hx]⟩
end

/-- A value-less canonical node holds two keys that part right after its prefix. -/
theorem two_found (ho : StrictOrder K) {p : List K} {ks : Kids K V D}
    (hc : (Trie.node p none ks).Canon) :
    ∃ a za xa b zb xb, a ≠ b ∧ (Trie.node p none ks).lookup (p ++ a :: za) = .found xa ∧
      (Trie.node p none ks).lookup (p ++ b :: zb) = .found xb := by
  obtain ⟨_, hv, hks⟩ := hc
  match ks, hv, hks with
  | .nil, hv, _ => simp [Kids.length] at hv
  | .cons _ _ .nil, hv, _ => simp [Kids.length] at hv
  | .cons a ta (.cons b tb rest), _, hks =>
    have hab : a ≠ b := fun e => ho.irrefl a (by
      have := hks.2.2.2 b (by simp [Kids.keys]); rwa [← e] at this)
    obtain ⟨ka, xa, hxa⟩ := Trie.exists_found hks.2.1
    obtain ⟨za, rfl⟩ := head_of_found hks.1 hxa
    obtain ⟨kb, xb, hxb⟩ := Trie.exists_found hks.2.2.1.2.1
    obtain ⟨zb, rfl⟩ := head_of_found hks.2.2.1.1 hxb
    refine ⟨a, za, xa, b, zb, xb, hab, ?_, ?_⟩
    · rw [lookup_node_cons (dropPrefix_append_self _ _)]; simp [Kids.lookup, hxa]
    · rw [lookup_node_cons (dropPrefix_append_self _ _)]; simp [Kids.lookup, hab, hxb]

/-- Two canonical nodes with the same reads: neither prefix strictly extends
the other. -/
theorem prefix_not_strict (ho : StrictOrder K) {p1 p2 : List K} {v1 v2 : Option V}
    {ks1 ks2 : Kids K V D} (hc1 : (Trie.node p1 v1 ks1).Canon)
    (hl : ∀ k, (Trie.node p1 v1 ks1).lookup k = (Trie.node p2 v2 ks2).lookup k)
    {x : K} {d : List K} (hp : p2 = p1 ++ x :: d) : False := by
  cases v1 with
  | some y =>
    have h := hl p1
    rw [lookup_node_nil (dropPrefix_eq_some.2 (List.append_nil _).symm)] at h
    obtain ⟨r, hr⟩ := found_prefix h.symm
    have := congrArg List.length hr
    subst hp; simp at this
  | none =>
    obtain ⟨a, za, xa, b, zb, xb, hab, ha, hb⟩ := two_found ho hc1
    rw [hl] at ha hb
    obtain ⟨ra, hra⟩ := found_prefix ha
    obtain ⟨rb, hrb⟩ := found_prefix hb
    subst hp
    simp only [List.append_assoc, List.append_right_inj, List.cons_append, List.cons.injEq] at hra hrb
    exact hab (hra.1.trans hrb.1.symm)

mutual
theorem Trie.canon_unique (ho : StrictOrder K) :
    ∀ {t1 t2 : Trie K V D}, t1.Canon → t2.Canon → (∀ k, t1.lookup k = t2.lookup k) → t1 = t2
  | .stub _, _, h, _, _ => h.elim
  | .node _ _ _, .stub _, _, h, _ => h.elim
  | .node p1 v1 ks1, .node p2 v2 ks2, hc1, hc2, hl => by
    have hp : p1 = p2 := by
      obtain ⟨k, x, hx⟩ := Trie.exists_found hc1
      obtain ⟨r1, hr1⟩ := found_prefix hx
      rw [hl] at hx
      obtain ⟨r2, hr2⟩ := found_prefix hx
      rw [hr1] at hr2
      rcases List.append_eq_append_iff.1 hr2 with ⟨as, h1, -⟩ | ⟨bs, h1, -⟩
      · cases as with
        | nil => simpa using h1.symm
        | cons x d => exact (prefix_not_strict ho hc1 hl h1).elim
      · cases bs with
        | nil => simpa using h1
        | cons x d => exact (prefix_not_strict ho hc2 (fun k => (hl k).symm) h1).elim
    subst hp
    have hv : v1 = v2 := by
      have h := hl p1
      rw [lookup_node_nil (dropPrefix_eq_some.2 (List.append_nil _).symm),
        lookup_node_nil (dropPrefix_eq_some.2 (List.append_nil _).symm)] at h
      exact Read.ofOption_inj h
    subst hv
    have hk := Kids.canon_unique ho hc1.2.2 hc2.2.2 (fun c z => by
      have h := hl (p1 ++ c :: z)
      rwa [lookup_node_cons (dropPrefix_append_self _ _),
        lookup_node_cons (dropPrefix_append_self _ _)] at h)
    rw [hk]
theorem Kids.canon_unique (ho : StrictOrder K) :
    ∀ {ks1 ks2 : Kids K V D}, ks1.Canon → ks2.Canon →
      (∀ c z, ks1.lookup c z = ks2.lookup c z) → ks1 = ks2
  | .nil, .nil, _, _, _ => rfl
  | .nil, .cons _ _ _, _, hc2, hl => by
    obtain ⟨c, z, x, hx⟩ := Kids.exists_found hc2 (by simp)
    rw [← hl] at hx; cases hx
  | .cons _ _ _, .nil, hc1, _, hl => by
    obtain ⟨c, z, x, hx⟩ := Kids.exists_found hc1 (by simp)
    rw [hl] at hx; cases hx
  | .cons c1 t1 r1, .cons c2 t2 r2, hc1, hc2, hl => by
    -- The least characters agree: the smaller one would be missing from the other side.
    have least : ∀ {a b : K} {ta tb : Trie K V D} {ra rb : Kids K V D},
        (Kids.cons a ta ra).Canon → (Kids.cons b tb rb).Canon →
        (∀ c z, (Kids.cons a ta ra).lookup c z = (Kids.cons b tb rb).lookup c z) → ¬ a < b := by
      intro a b ta tb ra rb ha hb hl hab
      have hn : a ∉ (Kids.cons b tb rb).keys := by
        simp only [Kids.keys, List.mem_cons, not_or]
        refine ⟨fun e => ho.irrefl a (by rw [e] at hab ⊢; exact hab), fun hm => ?_⟩
        exact ho.irrefl a (ho.trans hab (hb.2.2.2 a hm))
      obtain ⟨k, x, hx⟩ := Trie.exists_found ha.2.1
      obtain ⟨z, rfl⟩ := head_of_found ha.1 hx
      have h := hl a z
      rw [Kids.lookup_not_mem hn] at h
      simp [Kids.lookup, hx] at h
    have hc : c1 = c2 := by
      rcases ho.total c1 c2 with h | h | h
      · exact (least hc1 hc2 hl h).elim
      · exact h
      · exact (least hc2 hc1 (fun c z => (hl c z).symm) h).elim
    subst hc
    have ht : t1 = t2 := Trie.canon_unique ho hc1.2.1 hc2.2.1 (fun k => by
      by_cases hk : k.head? = some c1
      · obtain ⟨z, rfl⟩ : ∃ z, k = c1 :: z := by
          cases k with
          | nil => simp at hk
          | cons a z => simp at hk; exact ⟨z, by rw [hk]⟩
        have h := hl c1 z
        simpa [Kids.lookup] using h
      · rw [Trie.lookup_headIs hc1.1 hk, Trie.lookup_headIs hc2.1 hk])
    subst ht
    have hr : r1 = r2 := Kids.canon_unique ho hc1.2.2.1 hc2.2.2.1 (fun c z => by
      by_cases hcc : c1 = c
      · subst hcc
        rw [Kids.lookup_not_mem (Kids.Canon.not_mem ho hc1),
          Kids.lookup_not_mem (Kids.Canon.not_mem ho hc2)]
      · have h := hl c z
        simpa [Kids.lookup, hcc] using h)
    rw [hr]
end

end Lattice.Merkle
