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

end Lattice.Merkle
