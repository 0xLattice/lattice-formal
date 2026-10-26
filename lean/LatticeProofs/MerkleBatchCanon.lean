import LatticeProofs.MerkleBatchLemmas
import LatticeProofs.MerkleCanon

/-! A batch on a canonical trie: it succeeds exactly when every write's
precondition holds, does what its writes say on the map, and leaves the trie
canonical (helpers for `MerkleBatchProofs.lean`). -/

set_option linter.unusedSectionVars false

namespace Lattice.Merkle

variable {K V D : Type} [DecidableEq K] [LT K] [DecidableRel (α := K) (· < ·)]

theorem Batch.prefix_of_get {ws : Batch K V} {q k : List K} {o : Op V}
    (hq : ∀ w ∈ ws, q <+: w.1) (h : ws.get k = some o) : ∃ r, k = q ++ r := by
  obtain ⟨r, hr⟩ := hq _ (Batch.mem_of_get h)
  exact ⟨r, hr.symm⟩

theorem Batch.get_none_of_drop {ws : Batch K V} {q k : List K}
    (hq : ∀ w ∈ ws, q <+: w.1) (h : dropPrefix q k = none) : ws.get k = none := by
  cases hg : ws.get k with
  | none => rfl
  | some o =>
    obtain ⟨r, rfl⟩ := Batch.prefix_of_get hq hg
    simp [dropPrefix_append_self] at h

theorem Kids.length_eq_keys : ∀ (ks : Kids K V D), ks.length = ks.keys.length
  | .nil => rfl
  | .cons _ _ rest => by simp [Kids.length, Kids.keys, Kids.length_eq_keys rest]

/-! ## Fresh subtrees -/

mutual
theorem insertAll_spec (ho : StrictOrder K) (c : K) (ws : Batch K V) (hn : ws.Nodup)
    (hc : ∀ w ∈ ws, w.1.head? = some c) (hne : ws ≠ []) :
    (insertAll (D := D) c ws = none → ∃ w ∈ ws, ¬ w.2.pre none) ∧
    (∀ t, insertAll (D := D) c ws = some t → (∀ w ∈ ws, w.2.pre none) ∧
      (∀ k, t.lookup k = ws.upd (fun _ => .absent) k) ∧ t.Canon ∧ t.HeadIs c) := by
  have hq := childPrefix_prefix hc
  have hT : (ws.under (childPrefix c ws)).Nodup := Batch.nodup_under hn
  have hh : ∀ ch ∈ (ws.under (childPrefix c ws)).heads,
      (ws.under (childPrefix c ws)).at ch ≠ [] := by
    intro ch hch he
    obtain ⟨w, hw, hwc⟩ := Batch.mem_heads.1 hch
    exact Batch.at_eq_nil.1 he w hw hwc
  have IH := insertKids_spec ho (ws.under (childPrefix c ws)) (ws.under (childPrefix c ws)).heads
    (.nil : Kids K V D) hT Batch.nodup_heads (by simp [Kids.keys]) trivial hh
  -- every write is the node's own (at `q`) or beneath a head
  have hsplit : ∀ w ∈ ws, ∃ r, w.1 = childPrefix c ws ++ r ∧ (w.2 = (r, w.2).2) ∧
      (r, w.2) ∈ ws.under (childPrefix c ws) := by
    rintro ⟨k, o⟩ hw
    obtain ⟨r, rfl⟩ := hq _ hw
    exact ⟨r, rfl, rfl, Batch.mem_under.2 hw⟩
  have hq0 : (childPrefix c ws).head? = some c := rfl
  rw [insertAll]
  simp only [hne, ite_false]
  constructor
  · intro h
    split at h
    · next hk =>
      obtain ⟨⟨r, o⟩, hw, -, hpre⟩ := IH.1 hk
      exact ⟨_, Batch.mem_under.1 hw, hpre⟩
    · next ks hk =>
      cases hg : (ws.under (childPrefix c ws)).get [] with
      | none => rw [hg] at h; simp at h
      | some o =>
        rw [hg] at h
        refine ⟨_, Batch.mem_under.1 (Batch.mem_of_get hg), ?_⟩
        cases o with
        | insert v => simp at h
        | _ => simp [Op.pre]
  · intro t h
    split at h
    · simp at h
    · next ks hk =>
      obtain ⟨hpre, hlk, hcan, hkeys, hlen⟩ := IH.2 ks hk
      have hpre' : ∀ w ∈ ws.under (childPrefix c ws), w.1 ≠ [] → w.2.pre none := by
        rintro ⟨r, o⟩ hw hr
        cases r with
        | nil => exact absurd rfl hr
        | cons y z => exact hpre _ hw ⟨y, Batch.mem_heads.2 ⟨_, hw, rfl⟩, rfl⟩
      -- reads beneath the node
      have hkid : ∀ y z, ks.lookup y z =
          ws.upd (fun _ => .absent) (childPrefix c ws ++ y :: z) := by
        intro y z
        rw [hlk]
        split
        · simp only [Batch.upd, Batch.get_under]
        · next hy =>
          have : (ws.under (childPrefix c ws)).get (y :: z) = none := by
            cases hg : (ws.under (childPrefix c ws)).get (y :: z) with
            | none => rfl
            | some o => exact absurd (Batch.mem_heads.2 ⟨_, Batch.mem_of_get hg, rfl⟩) hy
          rw [Batch.get_under] at this
          simp [Kids.lookup, Batch.upd, this]
      have hout : ∀ k, dropPrefix (childPrefix c ws) k = none →
          ws.upd (fun _ => .absent) k = .absent := fun k hk =>
        by rw [Batch.upd_of_get_none (Batch.get_none_of_drop hq hk)]
      split at h
      · next v hg =>
        simp only [Option.some.injEq] at h; subst h
        refine ⟨fun w hw => ?_, fun k => ?_, ⟨by simp [childPrefix], Or.inl (by simp), hcan⟩, hq0⟩
        · obtain ⟨r, h1, -, h3⟩ := hsplit w hw
          cases r with
          | nil =>
            have := Batch.get_of_mem hT h3
            rw [hg] at this; simp only [Option.some.injEq] at this
            rw [← this]; simp [Op.pre]
          | cons y z => exact hpre' (y :: z, w.2) h3 (by simp)
        · cases hd : dropPrefix (childPrefix c ws) k with
          | none => rw [lookup_node_none hd, hout k hd]
          | some r =>
            obtain rfl := dropPrefix_eq_some.1 hd
            cases r with
            | nil =>
              rw [lookup_node_nil hd]
              rw [Batch.get_under, List.append_nil] at hg
              simp [Batch.upd, hg, Op.post, Read.ofOption]
            | cons y z => rw [lookup_node_cons hd, hkid]
      · simp at h
      · next hg =>
        simp only [Option.some.injEq] at h; subst h
        have h2 := childPrefix_two_heads hc hne hg
        refine ⟨fun w hw => ?_, fun k => ?_, ⟨by simp [childPrefix], Or.inr ?_, hcan⟩, hq0⟩
        · obtain ⟨r, h1, -, h3⟩ := hsplit w hw
          cases r with
          | nil =>
            have := Batch.get_of_mem hT h3
            rw [hg] at this; simp at this
          | cons y z => exact hpre' (y :: z, w.2) h3 (by simp)
        · cases hd : dropPrefix (childPrefix c ws) k with
          | none => rw [lookup_node_none hd, hout k hd]
          | some r =>
            obtain rfl := dropPrefix_eq_some.1 hd
            cases r with
            | nil =>
              rw [lookup_node_nil hd]
              rw [Batch.get_under, List.append_nil] at hg
              simp [Batch.upd, hg, Read.ofOption]
            | cons y z => rw [lookup_node_cons hd, hkid]
        · rw [hlen]; simp [Kids.length]; exact h2
termination_by (ws.tot, 0)
decreasing_by
  all_goals simp_wf
  have h := Batch.tot_under_lt (q := childPrefix c ws) (by simp [childPrefix]) ws
  simp only [hne, ite_false] at h
  exact lex_left (by omega)

theorem insertKids_spec (ho : StrictOrder K) (T : Batch K V) (chs : List K) (ks : Kids K V D)
    (hT : T.Nodup) (hnd : chs.Nodup) (hfresh : ∀ ch ∈ chs, ch ∉ ks.keys) (hks : ks.Canon)
    (hne : ∀ ch ∈ chs, T.at ch ≠ []) :
    (insertKids T chs ks = none → ∃ w ∈ T, (∃ ch ∈ chs, w.1.head? = some ch) ∧ ¬ w.2.pre none) ∧
    (∀ ks', insertKids T chs ks = some ks' →
      (∀ w ∈ T, (∃ ch ∈ chs, w.1.head? = some ch) → w.2.pre none) ∧
      (∀ y z, ks'.lookup y z =
        if y ∈ chs then T.upd (fun _ => .absent) (y :: z) else ks.lookup y z) ∧
      ks'.Canon ∧ (∀ x, x ∈ ks'.keys ↔ x ∈ chs ∨ x ∈ ks.keys) ∧
      ks'.length = chs.length + ks.length) := by
  match chs with
  | [] =>
    rw [insertKids]
    refine ⟨by simp, fun ks' h => ?_⟩
    simp only [Option.some.injEq] at h; subst h
    exact ⟨by simp, by simp, hks, by simp, by simp⟩
  | ch :: chs =>
    simp only [List.nodup_cons] at hnd
    have IH1 := insertKids_spec ho T chs ks hT hnd.2 (fun x hx => hfresh x (List.mem_cons_of_mem _ hx))
      hks (fun x hx => hne x (List.mem_cons_of_mem _ hx))
    have IH2 := insertAll_spec ho ch (T.at ch) (Batch.nodup_at hT)
      (fun w hw => (Batch.mem_at.1 hw).2) (hne ch List.mem_cons_self)
    rw [insertKids]
    constructor
    · intro h
      split at h
      · simp at h
      · next h1 =>
        cases hk : insertKids T chs ks with
        | none =>
          obtain ⟨w, hw, ⟨x, hx, hwx⟩, hp⟩ := IH1.1 hk
          exact ⟨w, hw, ⟨x, List.mem_cons_of_mem _ hx, hwx⟩, hp⟩
        | some ks' =>
          cases ht : insertAll (D := D) ch (T.at ch) with
          | none =>
            obtain ⟨w, hw, hp⟩ := IH2.1 ht
            exact ⟨w, (Batch.mem_at.1 hw).1, ⟨ch, List.mem_cons_self, (Batch.mem_at.1 hw).2⟩, hp⟩
          | some t => exact (h1 ks' t hk ht).elim
    · intro ks'' h
      split at h
      · next ks' t hk ht =>
        simp only [Option.some.injEq] at h; subst h
        obtain ⟨p1, l1, c1, k1, n1⟩ := IH1.2 ks' hk
        obtain ⟨p2, l2, c2, h2⟩ := IH2.2 t ht
        have hnot : ch ∉ ks'.keys := by
          rw [k1]; rintro (h | h)
          · exact hnd.1 h
          · exact hfresh ch List.mem_cons_self h
        refine ⟨fun w hw ⟨x, hx, hwx⟩ => ?_, fun y z => ?_, Kids.canon_ins ho h2 c2 c1 hnot,
          fun x => ?_, ?_⟩
        · rcases List.mem_cons.1 hx with rfl | hx
          · exact p2 w (Batch.mem_at.2 ⟨hw, hwx⟩)
          · exact p1 w hw ⟨x, hx, hwx⟩
        · rw [Kids.lookup_ins hnot]
          by_cases hy : ch = y
          · subst hy
            simp only [ite_true, List.mem_cons_self]
            rw [l2]
            simp only [Batch.upd, Batch.get_at, List.head?_cons, ite_true]
          · rw [l1]
            simp only [hy, ite_false, List.mem_cons, Ne.symm hy, false_or]
        · rw [Kids.mem_keys_ins, k1]
          simp only [List.mem_cons]
          constructor
          · rintro (h | h | h) <;> simp [h]
          · rintro ((h | h) | h) <;> simp [h]
        · rw [Kids.length_ins, n1]; simp; omega
      · simp at h
termination_by (T.tot, chs.length + 1)
decreasing_by
  all_goals simp_wf
  all_goals first
    | exact lex_right (Nat.le_refl _) (by omega)
    | exact lex_right (Batch.tot_at_le _ _) (by omega)
end

/-! ## Reads after a batch -/

/-- A list of children read as a map keyed from their first character. -/
def Kids.read (ks : Kids K V D) : List K → Read V
  | [] => .absent
  | y :: z => ks.lookup y z

theorem Batch.upd_congr {ws : Batch K V} {R R' : List K → Read V} {k : List K}
    (h : R k = R' k) : ws.upd R k = ws.upd R' k := by
  simp only [Batch.upd, h]

theorem Batch.upd_at {c : K} {ws : Batch K V} {R : List K → Read V} {z : List K} :
    (ws.at c).upd R (c :: z) = ws.upd R (c :: z) := by
  simp [Batch.upd, Batch.get_at]

theorem Batch.upd_under {q : List K} {ws : Batch K V} {R R' : List K → Read V} {k : List K}
    (h : R' k = R (q ++ k)) : (ws.under q).upd R' k = ws.upd R (q ++ k) := by
  simp only [Batch.upd, Batch.get_under, h]

/-- A node built from new children `ks'` and value `x` reads what the batch
`W` leaves on `R`, when every write extends `p` and `R` reads nothing outside
`p`. -/
theorem node_upd {p : List K} {x : Option V} {ks' : Kids K V D} {W : Batch K V}
    {R : List K → Read V} (hq : ∀ w ∈ W, p <+: w.1)
    (hR : ∀ k, dropPrefix p k = none → R k = .absent)
    (hks : ∀ y z, ks'.lookup y z = W.upd R (p ++ y :: z))
    (hx : Read.ofOption x = W.upd R p) :
    ∀ k, (Trie.node p x ks').lookup k = W.upd R k := by
  intro k
  cases hd : dropPrefix p k with
  | none =>
    rw [lookup_node_none hd, Batch.upd_of_get_none (Batch.get_none_of_drop hq hd), hR k hd]
  | some r =>
    obtain rfl := dropPrefix_eq_some.1 hd
    cases r with
    | nil => rw [lookup_node_nil hd, hx, List.append_nil]
    | cons y z => rw [lookup_node_cons hd, hks]

theorem Kids.read_cons {c y : K} {t : Trie K V D} {rest : Kids K V D} {z : List K} :
    (Kids.cons c t rest).read (y :: z) = if c = y then t.lookup (y :: z) else rest.read (y :: z) :=
  rfl

theorem Kids.read_not_mem {ks : Kids K V D} {k : List K} (h : ∀ y, k.head? = some y → y ∉ ks.keys) :
    ks.read k = .absent := by
  cases k with
  | nil => rfl
  | cons y z => exact Kids.lookup_not_mem (h y rfl)

theorem Kids.mem_keys_of_lookup {ks : Kids K V D} {y : K} {z : List K}
    (h : ks.lookup y z ≠ .absent) : y ∈ ks.keys :=
  Classical.byContradiction fun hy => h (Kids.lookup_not_mem hy)

theorem two_le_length {ks : Kids K V D} {a b : K} (ha : a ∈ ks.keys) (hb : b ∈ ks.keys)
    (hab : a ≠ b) : 2 ≤ ks.length := by
  match ks, ha, hb with
  | .nil, ha, _ => simp [Kids.keys] at ha
  | .cons x _ .nil, ha, hb =>
    simp [Kids.keys] at ha hb; exact absurd (ha.trans hb.symm) hab
  | .cons _ _ (.cons _ _ _), _, _ => simp [Kids.length]

/-- A canonical node read as a value-less node holding it as its one child,
cut after `q`. -/
theorem lookup_split {q e : K} {qs rest : List K} {v : Option V} {ks : Kids K V D} (k : List K) :
    (Trie.node ((q :: qs) ++ e :: rest) v ks).lookup k =
      (Trie.node (q :: qs) none (.cons e (.node (e :: rest) v ks) .nil)).lookup k := by
  rw [lookup_node_append]
  cases hd : dropPrefix (q :: qs) k with
  | none => rw [lookup_node_none hd]
  | some r =>
    obtain rfl := dropPrefix_eq_some.1 hd
    simp only
    cases r with
    | nil =>
      rw [lookup_node_nil hd, lookup_node_none (dropPrefix_cons_nil _ _)]; rfl
    | cons y z =>
      rw [lookup_node_cons hd]
      simp only [Kids.lookup]
      split
      · next h => subst h; rfl
      · next h => exact lookup_node_none (dropPrefix_cons_ne _ _ h)

/-! ## A batch on a canonical trie -/

/-- What the node-level theorem concludes about a result `r` of the writes
`ws` on `t`. -/
def BatchOk (c : K) (t : Trie K V D) (ws : Batch K V) (r : Option (Trie K V D)) : Prop :=
  (∀ w ∈ ws, w.2.pre (t.lookup w.1).toOption) ∧
  (∀ k, Trie.lookupOpt r k = ws.upd t.lookup k) ∧ (∀ t' ∈ r, t'.Canon ∧ t'.HeadIs c)

/-- The exact-match step, shared by a node and by a node cut after a shorter
prefix: given the transformed children, settling the node's own write leaves
what the batch says. -/
theorem settle_ok (c : K) {p : List K} {v : Option V} {ks' : Kids K V D} {ws : Batch K V}
    {R : List K → Read V} {r : Option (Trie K V D)}
    (hp : p.head? = some c) (hn : ws.Nodup) (hq : ∀ w ∈ ws, p <+: w.1)
    (hR : ∀ k, dropPrefix p k = none → R k = .absent)
    (hRp : R p = .ofOption v)
    (hpre : ∀ w ∈ ws.under p, w.1 ≠ [] → w.2.pre (R (p ++ w.1)).toOption)
    (hks : ∀ y z, ks'.lookup y z = ws.upd R (p ++ y :: z)) (hc : ks'.Canon)
    (h : (match (generalizing := false) (ws.under p).get [], v with
        | some (.update x), some _ => some (some (.node p (some x) ks'))
        | some .delete, some _ => collapse p ks'
        | some (.insert x), none => some (some (.node p (some x) ks'))
        | some _, _ => none
        | none, some _ => some (some (.node p v ks'))
        | none, none => collapse p ks') = some r) :
    (∀ w ∈ ws, w.2.pre (R w.1).toOption) ∧ (∀ k, Trie.lookupOpt r k = ws.upd R k) ∧
      (∀ t' ∈ r, t'.Canon ∧ t'.HeadIs c) := by
  have hne : p ≠ [] := ne_nil_of_head hp
  have hown : (ws.under p).get [] = ws.get p := by rw [Batch.get_under, List.append_nil]
  -- every write is the node's own or beneath it
  have hall : (∀ o, ws.get p = some o → o.pre (R p).toOption) →
      ∀ w ∈ ws, w.2.pre (R w.1).toOption := by
    intro ho w hw
    obtain ⟨rr, hr⟩ := hq w hw
    have hm : (rr, w.2) ∈ ws.under p := Batch.mem_under.2 (by rw [hr]; exact hw)
    cases rr with
    | nil =>
      simp only [List.append_nil] at hr
      have := Batch.get_of_mem hn (show (p, w.2) ∈ ws by rw [hr]; exact hw)
      rw [← hr]; exact ho _ this
    | cons y z => rw [← hr]; exact hpre _ hm (by simp)
  have hhead : ∀ x, (Trie.node p x ks').HeadIs c := fun _ => hp
  have hcol : ∀ {r}, collapse p ks' = some r → Read.ofOption none = ws.upd R p →
      (∀ k, Trie.lookupOpt r k = ws.upd R k) ∧ (∀ t' ∈ r, t'.Canon ∧ t'.HeadIs c) := by
    intro r h1 h2
    obtain ⟨l1, -, c1⟩ := collapse_correct hp hc h1
    exact ⟨fun k => by rw [l1]; exact node_upd hq hR hks h2 k, c1⟩
  rw [hown] at h
  cases hg : ws.get p with
  | none =>
    rw [hg] at h
    have hpo : ∀ o, ws.get p = some o → o.pre (R p).toOption := by simp [hg]
    cases v with
    | none =>
      obtain ⟨l, c1⟩ := hcol h (by rw [Batch.upd_of_get_none hg, hRp])
      exact ⟨hall hpo, l, c1⟩
    | some y =>
      simp only [Option.some.injEq] at h; subst h
      refine ⟨hall hpo, fun k => node_upd hq hR hks ?_ k, ?_⟩
      · rw [Batch.upd_of_get_none hg, hRp]
      · intro t' ht; simp only [Option.mem_def, Option.some.injEq] at ht; subst ht
        exact ⟨⟨hne, Or.inl (by simp), hc⟩, hhead _⟩
  | some o =>
    rw [hg] at h
    cases o with
    | update x =>
      cases v with
      | none => simp at h
      | some y =>
        simp only [Option.some.injEq] at h; subst h
        refine ⟨hall (by intro o ho; rw [hg] at ho; cases ho; simp [hRp, Op.pre, Read.ofOption,
          Read.toOption]), fun k => node_upd hq hR hks ?_ k, ?_⟩
        · rw [Batch.upd_of_get_some hg]; rfl
        · intro t' ht; simp only [Option.mem_def, Option.some.injEq] at ht; subst ht
          exact ⟨⟨hne, Or.inl (by simp), hc⟩, hhead _⟩
    | delete =>
      cases v with
      | none => simp at h
      | some y =>
        obtain ⟨l, c1⟩ := hcol h (by rw [Batch.upd_of_get_some hg]; rfl)
        exact ⟨hall (by intro o ho; rw [hg] at ho; cases ho; simp [hRp, Op.pre, Read.ofOption,
          Read.toOption]), l, c1⟩
    | insert x =>
      cases v with
      | some y => simp at h
      | none =>
        simp only [Option.some.injEq] at h; subst h
        refine ⟨hall (by intro o ho; rw [hg] at ho; cases ho; simp [hRp, Op.pre, Read.ofOption,
          Read.toOption]), fun k => node_upd hq hR hks ?_ k, ?_⟩
        · rw [Batch.upd_of_get_some hg]; rfl
        · intro t' ht; simp only [Option.mem_def, Option.some.injEq] at ht; subst ht
          exact ⟨⟨hne, Or.inl (by simp), hc⟩, hhead _⟩

theorem settle_none {p : List K} {v : Option V} {ks' : Kids K V D} {ws : Batch K V}
    {R : List K → Read V} (hRp : R p = .ofOption v) (hc : ks'.Canon)
    (h : (match (generalizing := false) (ws.under p).get [], v with
        | some (.update x), some _ => some (some (.node p (some x) ks'))
        | some .delete, some _ => collapse p ks'
        | some (.insert x), none => some (some (.node p (some x) ks'))
        | some _, _ => none
        | none, some _ => some (some (.node p v ks'))
        | none, none => collapse p ks') = none) :
    ∃ w ∈ ws, ¬ w.2.pre (R w.1).toOption := by
  have hown : (ws.under p).get [] = ws.get p := by rw [Batch.get_under, List.append_nil]
  rw [hown] at h
  cases hg : ws.get p with
  | none =>
    rw [hg] at h
    cases v with
    | none => exact absurd h (collapse_ne_none hc)
    | some _ => simp at h
  | some o =>
    rw [hg] at h
    refine ⟨(p, o), Batch.mem_of_get hg, ?_⟩
    cases o <;> cases v <;> simp_all [Op.pre, Read.ofOption, Read.toOption, collapse_ne_none hc]

/-- Two keys found under different first characters make two children. -/
theorem two_children {ks : Kids K V D} {a b : K} {za zb : List K} {xa xb : V}
    (ha : ks.lookup a za = .found xa) (hb : ks.lookup b zb = .found xb) (hab : a ≠ b) :
    2 ≤ ks.length :=
  two_le_length (Kids.mem_keys_of_lookup (by rw [ha]; simp))
    (Kids.mem_keys_of_lookup (by rw [hb]; simp)) hab

mutual
theorem Trie.batch_spec (ho : StrictOrder K) (t : Trie K V D) (ws : Batch K V) (c : K)
    (htc : t.Canon) (hth : t.HeadIs c) (hn : ws.Nodup) (hne : ws ≠ [])
    (hc : ∀ w ∈ ws, w.1.head? = some c) :
    (t.batch ws = none → ∃ w ∈ ws, ¬ w.2.pre (t.lookup w.1).toOption) ∧
    (∀ r, t.batch ws = some r → BatchOk c t ws r) := by
  match t, htc, hth with
  | .stub _, h, _ => exact h.elim
  | .node [] _ _, h, _ => exact (h.1 rfl).elim
  | .node (c0 :: p') v ks, htc, hth =>
    simp only [Trie.HeadIs, List.head?_cons, Option.some.injEq] at hth; subst hth
    obtain ⟨-, hv, hks⟩ := htc
    have hW : ws.at c0 = ws := Batch.at_of_all hc
    have hq := childPrefix_prefix hc
    have hs := split_holds (c0 :: p') (childPrefix c0 ws)
    have hR : ∀ k, dropPrefix (c0 :: p') k = none →
        (Trie.node (c0 :: p') v ks).lookup k = .absent := fun k h => lookup_node_none h
    have hRp : (Trie.node (c0 :: p') v ks).lookup (c0 :: p') = .ofOption v :=
      lookup_node_nil (dropPrefix_eq_some.2 (List.append_nil _).symm)
    have hRk : ∀ y z, (Trie.node (c0 :: p') v ks).lookup ((c0 :: p') ++ y :: z) = ks.read (y :: z) :=
      fun y z => lookup_node_cons (dropPrefix_append_self _ _)
    rw [Trie.batch, hW]; simp only [hne, ite_false]
    cases hsp : split (c0 :: p') (childPrefix c0 ws) with
    | equal =>
      rw [hsp] at hs; simp only [Split.Holds] at hs
      rw [hs] at hq
      simp only
      have IH := Kids.transform_spec ho ks (ws.under (c0 :: p')) hks (Batch.nodup_under hn)
      constructor
      · intro h
        cases ht : ks.transform (ws.under (c0 :: p')) with
        | none =>
          obtain ⟨⟨rr, o⟩, hw, hr, hp⟩ := IH.1 ht
          cases rr with
          | nil => exact absurd rfl hr
          | cons y z => exact ⟨_, Batch.mem_under.1 hw, by rwa [hRk]⟩
        | some ks' =>
          rw [ht] at h; dsimp only at h
          exact settle_none hRp (IH.2 ks' ht).2.2 h
      · intro r h
        cases ht : ks.transform (ws.under (c0 :: p')) with
        | none => rw [ht] at h; simp at h
        | some ks' =>
          rw [ht] at h; dsimp only at h
          obtain ⟨p1, l1, c1⟩ := IH.2 ks' ht
          exact settle_ok c0 rfl hn hq hR hRp
            (fun w hw hw1 => by
              obtain ⟨rr, o⟩ := w
              cases rr with
              | nil => exact absurd rfl hw1
              | cons y z => rw [hRk]; exact p1 _ hw hw1)
            (fun y z => by rw [l1]; exact Batch.upd_under (hRk y z).symm) c1 h
    | keyLonger c' r' =>
      rw [hsp] at hs; simp only [Split.Holds] at hs
      simp only
      have hT : (ws.under (c0 :: p')).Nodup := Batch.nodup_under hn
      have hqq : ∀ w ∈ ws, ((c0 :: p') ++ c' :: r') <+: w.1 := fun w hw => by
        rw [← hs]; exact hq w hw
      have hqp : ∀ w ∈ ws, (c0 :: p') <+: w.1 := fun w hw =>
        (List.prefix_append _ _).trans (hqq w hw)
      have hTh : ∀ w ∈ ws.under (c0 :: p'), w.1.head? = some c' := by
        rintro ⟨k, o⟩ hw
        have := hqq _ (Batch.mem_under.1 hw)
        simp only at this
        obtain ⟨u, hu⟩ := (List.prefix_append_right_inj (c0 :: p')).1 this
        simp only; rw [← hu]; rfl
      have hTne : ws.under (c0 :: p') ≠ [] := Batch.under_ne_nil hne hqp
      have hsplitW : ∀ w ∈ ws, ∃ y z, w.1 = (c0 :: p') ++ y :: z ∧
          ((y :: z), w.2) ∈ ws.under (c0 :: p') := by
        rintro ⟨k, o⟩ hw
        obtain ⟨rr, hr⟩ := hqp _ hw
        have hm : (rr, o) ∈ ws.under (c0 :: p') := Batch.mem_under.2 (by rw [hr]; exact hw)
        have := hTh _ hm
        cases rr with
        | nil => simp at this
        | cons y z => exact ⟨y, z, hr.symm, hm⟩
      have hgp : ws.get (c0 :: p') = none := by
        cases hg : ws.get (c0 :: p') with
        | none => rfl
        | some o =>
          obtain ⟨y, z, h1, -⟩ := hsplitW _ (Batch.mem_of_get hg)
          simp at h1
      have hx : Read.ofOption v = ws.upd (Trie.node (c0 :: p') v ks).lookup (c0 :: p') := by
        rw [Batch.upd_of_get_none hgp, hRp]
      have hp0 : (c0 :: p').head? = some c0 := rfl
      by_cases hck : c' ∈ ks.keys
      · simp only [hck, ite_true]
        have IH := Kids.batchOld_spec ho ks (ws.under (c0 :: p')) hks hT
        constructor
        · intro h
          cases hb : ks.batchOld (ws.under (c0 :: p')) with
          | none =>
            obtain ⟨⟨k, o⟩, hw, ⟨y, -, hwy⟩, hp⟩ := IH.1 hb
            cases k with
            | nil => simp at hwy
            | cons y' z => exact ⟨_, Batch.mem_under.1 hw, by rwa [hRk]⟩
          | some ks1 =>
            rw [hb] at h; dsimp only at h
            split at h
            · exact absurd h (collapse_ne_none (IH.2 ks1 hb).2.2.1)
            · simp at h
        · intro r h
          cases hb : ks.batchOld (ws.under (c0 :: p')) with
          | none => rw [hb] at h; simp at h
          | some ks1 =>
            rw [hb] at h; dsimp only at h
            obtain ⟨p1, l1, c1, -, -⟩ := IH.2 ks1 hb
            have hl : ∀ y z, ks1.lookup y z =
                ws.upd (Trie.node (c0 :: p') v ks).lookup ((c0 :: p') ++ y :: z) := by
              intro y z
              rw [l1, ← Batch.upd_under (hRk y z).symm]
              split
              · rfl
              · next hy =>
                have : (ws.under (c0 :: p')).get (y :: z) = none := by
                  cases hg : (ws.under (c0 :: p')).get (y :: z) with
                  | none => rfl
                  | some o =>
                    have := hTh _ (Batch.mem_of_get hg)
                    simp at this; subst this; exact absurd hck hy
                rw [Batch.upd_of_get_none this]; exact (Kids.lookup_not_mem hy).symm
            have hpre : ∀ w ∈ ws, w.2.pre ((Trie.node (c0 :: p') v ks).lookup w.1).toOption := by
              intro w hw
              obtain ⟨y, z, h1, h2⟩ := hsplitW w hw
              rw [h1, hRk]
              exact p1 _ h2 ⟨y, by simpa using (show y = c' by simpa using hTh _ h2) ▸ hck, rfl⟩
            split at h
            · next hcv =>
              obtain ⟨l2, -, c2⟩ := collapse_correct hp0 c1 h
              refine ⟨hpre, fun k => ?_, c2⟩
              rw [l2]; exact node_upd hqp hR hl (by rw [← hcv.2]; exact hx) k
            · next hcv =>
              simp only [Option.some.injEq] at h; subst h
              refine ⟨hpre, fun k => node_upd hqp hR hl hx k, fun t' ht => ?_⟩
              simp only [Option.mem_def, Option.some.injEq] at ht; subst ht
              refine ⟨⟨by simp, ?_, c1⟩, hp0⟩
              cases v with
              | some _ => exact Or.inl (by simp)
              | none =>
                refine Or.inr ?_
                have hck1 : c' ∈ ks1.keys := Classical.byContradiction fun h => hcv ⟨h, rfl⟩
                obtain ⟨a, za, xa, b, zb, xb, hab, ha, hb'⟩ := two_found (p := c0 :: p') (ks := ks) ho ⟨by simp, hv, hks⟩
                have found : ∀ y z x, y ≠ c' →
                    (Trie.node (c0 :: p') none ks).lookup ((c0 :: p') ++ y :: z) = .found x →
                    y ∈ ks1.keys := by
                  intro y z x hy hf
                  apply Kids.mem_keys_of_lookup (z := z)
                  rw [hl, Batch.upd_of_get_none, hf]; · simp
                  rw [← List.append_nil (c0 :: p'), List.append_assoc, ← Batch.get_under]
                  simp only [List.nil_append]
                  cases hg : (ws.under (c0 :: p')).get (y :: z) with
                  | none => rfl
                  | some o => have := hTh _ (Batch.mem_of_get hg); simp at this; exact absurd this hy
                by_cases hac : a = c'
                · subst hac
                  exact two_le_length (found b zb xb (Ne.symm hab) hb') hck1 (Ne.symm hab)
                · exact two_le_length (found a za xa hac ha) hck1 hac
      · simp only [hck, ite_false]
        have IH := insertAll_spec (D := D) ho c' _ hT hTh hTne
        have hread : ∀ w ∈ ws.under (c0 :: p'), ks.read w.1 = .absent := by
          rintro ⟨k, o⟩ hw
          have := hTh _ hw
          cases k with
          | nil => simp at this
          | cons y z => simp at this; subst this; exact Kids.lookup_not_mem hck
        constructor
        · intro h
          cases hi : insertAll (D := D) c' (ws.under (c0 :: p')) with
          | none =>
            obtain ⟨⟨k, o⟩, hw, hp⟩ := IH.1 hi
            have := hTh _ hw
            cases k with
            | nil => simp at this
            | cons y z =>
              refine ⟨_, Batch.mem_under.1 hw, ?_⟩
              rw [hRk, hread _ hw]; exact hp
          | some n => rw [hi] at h; simp at h
        · intro r h
          cases hi : insertAll (D := D) c' (ws.under (c0 :: p')) with
          | none => rw [hi] at h; simp at h
          | some n =>
            rw [hi] at h; dsimp only at h
            simp only [Option.some.injEq] at h; subst h
            obtain ⟨p1, l1, c1, h1⟩ := IH.2 n hi
            refine ⟨fun w hw => ?_, fun k => node_upd hqp hR (fun y z => ?_) hx k, fun t' ht => ?_⟩
            · obtain ⟨y, z, e1, e2⟩ := hsplitW w hw
              rw [e1, hRk, hread _ e2]; exact p1 (y :: z, w.2) e2
            · rw [Kids.lookup_ins hck, ← Batch.upd_under (hRk y z).symm]
              split
              · next hy => subst hy; rw [l1]; exact Batch.upd_congr (Kids.lookup_not_mem hck).symm
              · next hy =>
                have : (ws.under (c0 :: p')).get (y :: z) = none := by
                  cases hg : (ws.under (c0 :: p')).get (y :: z) with
                  | none => rfl
                  | some o =>
                    have := hTh _ (Batch.mem_of_get hg); simp at this; exact absurd this.symm hy
                rw [Batch.upd_of_get_none this]; rfl
            · simp only [Option.mem_def, Option.some.injEq] at ht; subst ht
              refine ⟨⟨by simp, ?_, Kids.canon_ins ho h1 c1 hks hck⟩, hp0⟩
              rcases hv with hv | hv
              · exact Or.inl hv
              · exact Or.inr (by rw [Kids.length_ins]; omega)
    | keyShorter e rest =>
      rw [hsp] at hs; simp only [Split.Holds] at hs
      simp only
      have hk0 : (Kids.cons e (.node (e :: rest) v ks) .nil : Kids K V D).Canon :=
        ⟨rfl, ⟨by simp, hv, hks⟩, trivial, by simp [Kids.keys]⟩
      have hRt : (Trie.node (c0 :: p') v ks).lookup =
          (Trie.node (childPrefix c0 ws) none (.cons e (.node (e :: rest) v ks) .nil)).lookup := by
        funext k; rw [hs]
        exact lookup_split (q := c0) (qs := (ws.under [c0]).common) k
      have hR : ∀ k, dropPrefix (childPrefix c0 ws) k = none →
          (Trie.node (childPrefix c0 ws) none
            (.cons e (.node (e :: rest) v ks) .nil : Kids K V D)).lookup k = .absent :=
        fun k h => lookup_node_none h
      have hRp : (Trie.node (childPrefix c0 ws) none
          (.cons e (.node (e :: rest) v ks) .nil : Kids K V D)).lookup (childPrefix c0 ws) =
          .ofOption none := lookup_node_nil (dropPrefix_eq_some.2 (List.append_nil _).symm)
      have hRk : ∀ y z, (Trie.node (childPrefix c0 ws) none
          (.cons e (.node (e :: rest) v ks) .nil : Kids K V D)).lookup
            (childPrefix c0 ws ++ y :: z) =
          (Kids.cons e (.node (e :: rest) v ks) .nil : Kids K V D).read (y :: z) :=
        fun y z => lookup_node_cons (dropPrefix_append_self _ _)
      have IH := Kids.transform_spec ho (.cons e (.node (e :: rest) v ks) .nil)
        (ws.under (childPrefix c0 ws)) hk0 (Batch.nodup_under hn)
      -- the node's own write, settled as at a value-less node
      have hconv : ∀ (ks' : Kids K V D) (r : Option (Option (Trie K V D))),
          (match (ws.under (childPrefix c0 ws)).get [] with
            | some (.insert x) => some (some (Trie.node (childPrefix c0 ws) (some x) ks'))
            | some _ => none
            | none => collapse (childPrefix c0 ws) ks') = r →
          (match (generalizing := false) (ws.under (childPrefix c0 ws)).get [], (none : Option V) with
            | some (.update x), some _ => some (some (.node (childPrefix c0 ws) (some x) ks'))
            | some .delete, some _ => collapse (childPrefix c0 ws) ks'
            | some (.insert x), none => some (some (.node (childPrefix c0 ws) (some x) ks'))
            | some _, _ => none
            | none, some _ => some (some (.node (childPrefix c0 ws) none ks'))
            | none, none => collapse (childPrefix c0 ws) ks') = r := by
        intro ks' r
        cases (ws.under (childPrefix c0 ws)).get [] with
        | none => exact id
        | some o => cases o <;> exact id
      simp only [BatchOk]
      rw [hRt]
      constructor
      · intro h
        cases ht : Kids.transform (.cons e (.node (e :: rest) v ks) .nil) (ws.under (childPrefix c0 ws)) with
        | none =>
          obtain ⟨⟨rr, o⟩, hw, hr, hp⟩ := IH.1 ht
          cases rr with
          | nil => exact absurd rfl hr
          | cons y z => exact ⟨_, Batch.mem_under.1 hw, by rwa [hRk]⟩
        | some ks' =>
          rw [ht] at h; dsimp only at h
          exact settle_none hRp (IH.2 ks' ht).2.2 (hconv ks' none h)
      · intro r h
        cases ht : Kids.transform (.cons e (.node (e :: rest) v ks) .nil) (ws.under (childPrefix c0 ws)) with
        | none => rw [ht] at h; simp at h
        | some ks' =>
          rw [ht] at h; dsimp only at h
          obtain ⟨p1, l1, c1⟩ := IH.2 ks' ht
          exact settle_ok c0 rfl hn hq hR hRp
            (fun w hw hw1 => by
              obtain ⟨rr, o⟩ := w
              cases rr with
              | nil => exact absurd rfl hw1
              | cons y z => rw [hRk]; exact p1 _ hw hw1)
            (fun y z => by rw [l1]; exact Batch.upd_under (hRk y z).symm) c1 (hconv ks' _ h)
    | diverge cm a ka b pb =>
      rw [hsp] at hs; simp only [Split.Holds] at hs
      obtain ⟨hs1, hs2, hab⟩ := hs
      simp only
      have hcm : cm ≠ [] := by
        rintro rfl
        have h1 : (childPrefix c0 ws).head? = some c0 := rfl
        rw [hs1] at h1; simp at h1
        simp at hs2
        exact hab (by simp_all)
      have hcm0 : cm.head? = some c0 := by
        cases cm with
        | nil => exact absurd rfl hcm
        | cons x cm => simp at hs2; simp [hs2.1]
      have hqa : ∀ w ∈ ws, cm ++ a :: ka <+: w.1 := fun w hw => by rw [← hs1]; exact hq w hw
      have hqc : ∀ w ∈ ws, cm <+: w.1 := fun w hw => (List.prefix_append _ _).trans (hqa w hw)
      have hU : ∀ w ∈ ws.under cm, w.1.head? = some a := by
        rintro ⟨k, o⟩ hw
        have := hqa _ (Batch.mem_under.1 hw)
        simp only at this
        obtain ⟨u, hu⟩ := (List.prefix_append_right_inj cm).1 this
        simp only; rw [← hu]; rfl
      have hUa : (ws.under cm).at a = ws.under cm := Batch.at_of_all hU
      have hUn : (ws.under cm).Nodup := Batch.nodup_under hn
      have hUne : ws.under cm ≠ [] := Batch.under_ne_nil hne hqc
      have habs : ∀ r, (Trie.node (c0 :: p') v ks).lookup (cm ++ a :: r) = .absent :=
        fun r => lookup_node_none (dropPrefix_of_diverge rfl hs2 hab)
      have hall : ∀ w ∈ ws, ∃ r, w.1 = cm ++ a :: r ∧ (a :: r, w.2) ∈ ws.under cm := by
        rintro ⟨k, o⟩ hw
        obtain ⟨u, hu⟩ := hqa _ hw
        simp only at hu; subst hu
        exact ⟨ka ++ u, by simp, Batch.mem_under.2 (by simpa using hw)⟩
      have IH := insertAll_spec (D := D) ho a (ws.under cm) hUn hU hUne
      rw [hUa]
      constructor
      · intro h
        cases hi : insertAll (D := D) a (ws.under cm) with
        | none =>
          obtain ⟨⟨k, o⟩, hw, hp⟩ := IH.1 hi
          have := hU _ hw
          cases k with
          | nil => simp at this
          | cons y z =>
            simp at this; subst this
            exact ⟨_, Batch.mem_under.1 hw, by rw [habs]; exact hp⟩
        | some n => rw [hi] at h; simp at h
      · intro r h
        cases hi : insertAll (D := D) a (ws.under cm) with
        | none => rw [hi] at h; simp at h
        | some n =>
          rw [hi] at h; dsimp only at h
          simp only [Option.some.injEq] at h; subst h
          obtain ⟨p1, l1, c1, h1⟩ := IH.2 n hi
          have hnb : a ∉ (Kids.cons b (Trie.node (b :: pb) v ks) .nil).keys := by
            simp [Kids.keys, hab]
          have hgcm : ∀ y z, y ≠ a → ws.get (cm ++ y :: z) = none := by
            intro y z hy
            rw [Batch.get_eq_none]
            intro w hw he
            obtain ⟨r, e1, -⟩ := hall w hw
            rw [e1] at he; simp at he; exact hy he.1.symm
          refine ⟨fun w hw => ?_, fun k => node_upd hqc (fun k hk => ?_) (fun y z => ?_) ?_ k,
            fun t' ht => ?_⟩
          · obtain ⟨r, e1, e2⟩ := hall w hw
            rw [e1, habs]; exact p1 (a :: r, w.2) e2
          · rw [hs2]; exact lookup_node_none (by simp [dropPrefix_append, hk])
          · rw [Kids.lookup_ins hnb]
            split
            · next hy =>
              subst hy
              rw [l1]; exact Batch.upd_under (R' := fun _ => Read.absent) (habs z).symm
            · next hy =>
              rw [Batch.upd_of_get_none (hgcm y z (Ne.symm hy)), hs2, lookup_node_append,
                dropPrefix_append_self]
              simp only [Kids.lookup]
              split
              · next hb => subst hb; rfl
              · next hb => exact (lookup_node_none (dropPrefix_cons_ne _ _ hb)).symm
          · rw [Batch.upd_of_get_none, hs2, lookup_node_none (dropPrefix_of_keyShorter rfl)]; · rfl
            rw [Batch.get_eq_none]
            intro w hw he
            obtain ⟨r, e1, -⟩ := hall w hw
            rw [e1] at he; simp at he
          · simp only [Option.mem_def, Option.some.injEq] at ht; subst ht
            refine ⟨⟨hcm, Or.inr (by simp [Kids.length_ins, Kids.length]), ?_⟩, hcm0⟩
            exact Kids.canon_ins ho h1 c1 ⟨rfl, ⟨by simp, hv, hks⟩, trivial, by simp [Kids.keys]⟩ hnb
termination_by (ws.tot, t.weight)
decreasing_by
  all_goals simp_wf
  all_goals first
    | have h1 := Batch.tot_under_lt (q := c0 :: p') (by simp) ws
      simp only [hne, ite_false] at h1
      exact lex_left (by omega)
    | have h1 := Batch.tot_under_lt (q := childPrefix c0 ws) (by simp [childPrefix]) ws
      simp only [hne, ite_false] at h1
      exact lex_left (by omega)

theorem Kids.transform_spec (ho : StrictOrder K) (ks : Kids K V D) (T : Batch K V)
    (hks : ks.Canon) (hn : T.Nodup) :
    (ks.transform T = none → ∃ w ∈ T, w.1 ≠ [] ∧ ¬ w.2.pre (ks.read w.1).toOption) ∧
    (∀ ks', ks.transform T = some ks' →
      (∀ w ∈ T, w.1 ≠ [] → w.2.pre (ks.read w.1).toOption) ∧
      (∀ y z, ks'.lookup y z = T.upd ks.read (y :: z)) ∧ ks'.Canon) := by
  have IH := Kids.batchOld_spec ho ks T hks hn
  have hnd : (T.heads.filter (· ∉ ks.keys)).Nodup :=
    List.Nodup.sublist (List.filter_sublist) Batch.nodup_heads
  have hmem : ∀ ch, ch ∈ T.heads.filter (· ∉ ks.keys) ↔ ch ∈ T.heads ∧ ch ∉ ks.keys := by
    intro ch; simp [List.mem_filter]
  have hne : ∀ ch ∈ T.heads.filter (· ∉ ks.keys), T.at ch ≠ [] := by
    intro ch hch he
    obtain ⟨w, hw, hwc⟩ := Batch.mem_heads.1 ((hmem ch).1 hch).1
    exact Batch.at_eq_nil.1 he w hw hwc
  have hread : ∀ ch z, ch ∉ ks.keys → ks.read (ch :: z) = .absent :=
    fun ch z h => Kids.lookup_not_mem h
  rw [Kids.transform]
  constructor
  · intro h
    cases hb : ks.batchOld T with
    | none =>
      obtain ⟨w, hw, ⟨y, -, hwy⟩, hp⟩ := IH.1 hb
      exact ⟨w, hw, fun e => by rw [e] at hwy; simp at hwy, hp⟩
    | some ks1 =>
      rw [hb] at h; dsimp only at h
      obtain ⟨-, -, c1, k1, -⟩ := IH.2 ks1 hb
      have IK := insertKids_spec ho T _ ks1 hn hnd
        (fun ch hch hk => ((hmem ch).1 hch).2 (k1 ch hk)) c1 hne
      obtain ⟨⟨k, o⟩, hw, ⟨ch, hch, hwc⟩, hp⟩ := IK.1 h
      cases k with
      | nil => simp at hwc
      | cons y z =>
        simp only [List.head?_cons, Option.some.injEq] at hwc; subst hwc
        exact ⟨_, hw, by simp, by rwa [hread _ _ ((hmem y).1 hch).2]⟩
  · intro ks' h
    cases hb : ks.batchOld T with
    | none => rw [hb] at h; simp at h
    | some ks1 =>
      rw [hb] at h; dsimp only at h
      obtain ⟨p1, l1, c1, k1, -⟩ := IH.2 ks1 hb
      have IK := insertKids_spec ho T _ ks1 hn hnd
        (fun ch hch hk => ((hmem ch).1 hch).2 (k1 ch hk)) c1 hne
      obtain ⟨p2, l2, c2, -, -⟩ := IK.2 ks' h
      refine ⟨fun ⟨k, o⟩ hw hk => ?_, fun y z => ?_, c2⟩
      · cases k with
        | nil => exact absurd rfl hk
        | cons y z =>
          by_cases hy : y ∈ ks.keys
          · exact p1 _ hw ⟨y, hy, rfl⟩
          · rw [hread _ _ hy]
            exact p2 _ hw ⟨y, (hmem y).2 ⟨Batch.mem_heads.2 ⟨_, hw, rfl⟩, hy⟩, rfl⟩
      · rw [l2]
        split
        · next hy => exact Batch.upd_congr (hread _ _ ((hmem y).1 hy).2).symm
        · next hy =>
          rw [l1]
          split
          · rfl
          · next hk =>
            have : T.get (y :: z) = none := by
              cases hg : T.get (y :: z) with
              | none => rfl
              | some o =>
                exact absurd ((hmem y).2 ⟨Batch.mem_heads.2 ⟨_, Batch.mem_of_get hg, rfl⟩, hk⟩) hy
            rw [Batch.upd_of_get_none this, hread _ _ hk]
termination_by (T.tot, ks.weight + 1)
decreasing_by
  all_goals simp_wf
  exact lex_right (Nat.le_refl _) (by omega)

theorem Kids.batchOld_spec (ho : StrictOrder K) (ks : Kids K V D) (T : Batch K V)
    (hks : ks.Canon) (hn : T.Nodup) :
    (ks.batchOld T = none →
      ∃ w ∈ T, (∃ y ∈ ks.keys, w.1.head? = some y) ∧ ¬ w.2.pre (ks.read w.1).toOption) ∧
    (∀ ks1, ks.batchOld T = some ks1 →
      (∀ w ∈ T, (∃ y ∈ ks.keys, w.1.head? = some y) → w.2.pre (ks.read w.1).toOption) ∧
      (∀ y z, ks1.lookup y z = if y ∈ ks.keys then T.upd ks.read (y :: z) else .absent) ∧
      ks1.Canon ∧ (∀ x ∈ ks1.keys, x ∈ ks.keys) ∧ (∀ x ∈ ks.keys, T.at x = [] → x ∈ ks1.keys)) := by
  match ks, hks with
  | .nil, _ =>
    rw [Kids.batchOld]
    refine ⟨by simp, fun ks1 h => ?_⟩
    simp only [Option.some.injEq] at h; subst h
    exact ⟨by simp [Kids.keys], by simp [Kids.keys, Kids.lookup], trivial, by simp [Kids.keys],
      by simp [Kids.keys]⟩
  | .cons c t rest, ⟨h1, h2, h3, h4⟩ =>
    have hnm : c ∉ rest.keys := fun h => ho.irrefl c (h4 c h)
    have IHr := Kids.batchOld_spec ho rest T h3 hn
    have hrd : ∀ y z, y ≠ c → (Kids.cons c t rest).read (y :: z) = rest.read (y :: z) :=
      fun y z hy => by simp [Kids.read_cons, Ne.symm hy]
    have hcd : ∀ z, (Kids.cons c t rest).read (c :: z) = t.lookup (c :: z) :=
      fun z => by simp [Kids.read_cons]
    have hrc : ∀ z, rest.read (c :: z) = .absent := fun z => Kids.lookup_not_mem hnm
    have hatc : ∀ w ∈ T.at c, ∃ z, w.1 = c :: z := by
      rintro ⟨k, o⟩ hw
      have := (Batch.mem_at.1 hw).2
      cases k with
      | nil => simp at this
      | cons y z => simp at this; subst this; exact ⟨z, rfl⟩
    rw [Kids.batchOld]
    constructor
    · intro h
      cases hr : rest.batchOld T with
      | none =>
        obtain ⟨⟨k, o⟩, hw, ⟨y, hy, hwy⟩, hp⟩ := IHr.1 hr
        cases k with
        | nil => simp at hwy
        | cons y' z =>
          simp only [List.head?_cons, Option.some.injEq] at hwy; subst hwy
          have hyc : y' ≠ c := fun e => hnm (e ▸ hy)
          exact ⟨_, hw, ⟨y', by simp [Kids.keys, hy], rfl⟩, by rwa [hrd _ _ hyc]⟩
      | some rest' =>
        rw [hr] at h; dsimp only at h
        split at h
        · simp at h
        · next hne =>
          cases ht : t.batch (T.at c) with
          | none =>
            obtain ⟨⟨k, o⟩, hw, hp⟩ := (Trie.batch_spec ho t (T.at c) c h2 h1 (Batch.nodup_at hn) hne
              (fun w hw => (Batch.mem_at.1 hw).2)).1 ht
            obtain ⟨z, hz⟩ := hatc _ hw
            simp only at hz; subst hz
            exact ⟨_, (Batch.mem_at.1 hw).1, ⟨c, by simp [Kids.keys], rfl⟩, by rwa [hcd]⟩
          | some r => rw [ht] at h; cases r <;> simp at h
    · intro ks1 h
      cases hr : rest.batchOld T with
      | none => rw [hr] at h; simp at h
      | some rest' =>
        rw [hr] at h; dsimp only at h
        obtain ⟨p1, l1, c1, k1, u1⟩ := IHr.2 rest' hr
        -- writes beneath the other children
        have hpre_rest : ∀ w ∈ T, (∃ y ∈ rest.keys, w.1.head? = some y) →
            w.2.pre ((Kids.cons c t rest).read w.1).toOption := by
          rintro ⟨k, o⟩ hw ⟨y, hy, hwy⟩
          cases k with
          | nil => simp at hwy
          | cons y' z =>
            simp only [List.head?_cons, Option.some.injEq] at hwy; subst hwy
            rw [hrd _ _ (fun e => hnm (e ▸ hy))]; exact p1 _ hw ⟨y', hy, rfl⟩
        have hlk_rest : ∀ y z, y ≠ c → rest'.lookup y z =
            if y ∈ (Kids.cons c t rest).keys then T.upd (Kids.cons c t rest).read (y :: z)
            else .absent := by
          intro y z hy
          rw [l1]
          simp only [Kids.keys, List.mem_cons, hy, false_or]
          split
          · exact Batch.upd_congr (hrd _ _ hy).symm
          · rfl
        have hkeys : ∀ x ∈ (Kids.cons c t rest).keys, x = c ∨ x ∈ rest.keys := by
          simp [Kids.keys]
        split at h
        · next hat =>
          simp only [Option.some.injEq] at h; subst h
          refine ⟨fun w hw ⟨y, hy, hwy⟩ => ?_, fun y z => ?_, ⟨h1, h2, c1, fun x hx => h4 x (k1 x hx)⟩,
            fun x hx => ?_, fun x hx hxa => ?_⟩
          · rcases hkeys y hy with rfl | hy
            · exact absurd hat (fun he => Batch.at_eq_nil.1 he w hw hwy)
            · exact hpre_rest w hw ⟨y, hy, hwy⟩
          · by_cases hy : c = y
            · subst hy
              have : T.get (c :: z) = none := by
                cases hg : T.get (c :: z) with
                | none => rfl
                | some o => exact absurd (Batch.mem_of_get hg) (fun hm => Batch.at_eq_nil.1 hat _ hm rfl)
              simp only [Kids.lookup, ite_true, Kids.keys, List.mem_cons, true_or]
              rw [Batch.upd_of_get_none this, hcd]
            · simp only [Kids.lookup, hy, ite_false]
              exact hlk_rest y z (Ne.symm hy)
          · simp only [Kids.keys, List.mem_cons] at hx ⊢
            rcases hx with rfl | hx
            · exact Or.inl rfl
            · exact Or.inr (k1 x hx)
          · simp only [Kids.keys, List.mem_cons] at hx ⊢
            rcases hx with rfl | hx
            · exact Or.inl rfl
            · exact Or.inr (u1 x hx hxa)
        · next hne =>
          have IHt := Trie.batch_spec ho t (T.at c) c h2 h1 (Batch.nodup_at hn) hne
            (fun w hw => (Batch.mem_at.1 hw).2)
          cases ht : t.batch (T.at c) with
          | none => rw [ht] at h; simp at h
          | some r =>
            rw [ht] at h
            obtain ⟨pt, lt, ct⟩ := IHt.2 r ht
            have hpre_c : ∀ w ∈ T, w.1.head? = some c →
                w.2.pre ((Kids.cons c t rest).read w.1).toOption := by
              rintro ⟨k, o⟩ hw hwc
              obtain ⟨z, hz⟩ := hatc _ (Batch.mem_at.2 ⟨hw, hwc⟩)
              simp only at hz; subst hz
              rw [hcd]; exact pt _ (Batch.mem_at.2 ⟨hw, hwc⟩)
            have hpre_all : ∀ w ∈ T, (∃ y ∈ (Kids.cons c t rest).keys, w.1.head? = some y) →
                w.2.pre ((Kids.cons c t rest).read w.1).toOption := by
              intro w hw ⟨y, hy, hwy⟩
              rcases hkeys y hy with rfl | hy
              · exact hpre_c w hw hwy
              · exact hpre_rest w hw ⟨y, hy, hwy⟩
            have hlc : ∀ z, Trie.lookupOpt r (c :: z) = T.upd (Kids.cons c t rest).read (c :: z) := by
              intro z
              rw [lt, Batch.upd_at]
              exact Batch.upd_congr (hcd z).symm
            cases r with
            | none =>
              simp only [Option.some.injEq] at h; subst h
              refine ⟨hpre_all, fun y z => ?_, c1, fun x hx => by simp [Kids.keys, k1 x hx],
                fun x hx hxa => ?_⟩
              · by_cases hy : y = c
                · subst hy
                  rw [l1, ite_eq_right_of_eq_false _ _ (eq_false hnm), ← hlc]
                  simp [Kids.keys]; rfl
                · exact hlk_rest y z hy
              · rcases hkeys x hx with rfl | hx
                · exact absurd hxa hne
                · exact u1 x hx hxa
            | some t' =>
              simp only [Option.some.injEq] at h; subst h
              obtain ⟨ct1, ct2⟩ := ct t' rfl
              refine ⟨hpre_all, fun y z => ?_, ⟨ct2, ct1, c1, fun x hx => h4 x (k1 x hx)⟩,
                fun x hx => ?_, fun x hx hxa => ?_⟩
              · by_cases hy : c = y
                · subst hy
                  simp only [Kids.lookup, ite_true, Kids.keys, List.mem_cons, true_or]
                  exact hlc z
                · simp only [Kids.lookup, hy, ite_false]
                  exact hlk_rest y z (Ne.symm hy)
              · simp only [Kids.keys, List.mem_cons] at hx ⊢
                rcases hx with rfl | hx
                · exact Or.inl rfl
                · exact Or.inr (k1 x hx)
              · simp only [Kids.keys, List.mem_cons] at hx ⊢
                rcases hx with rfl | hx
                · exact Or.inl rfl
                · exact Or.inr (u1 x hx hxa)
termination_by (T.tot, ks.weight)
decreasing_by
  all_goals simp_wf
  all_goals first
    | exact lex_right (Nat.le_refl _) (by simp only [Kids.weight]; omega)
    | exact lex_right (Batch.tot_at_le _ _) (by simp only [Kids.weight]; omega)
end

end Lattice.Merkle
