import LatticeProofs.MerkleBatch
import LatticeProofs.MerkleLemmas

/-! Lemmas about batches of writes (helpers for the batch proofs). -/

set_option linter.unusedSectionVars false

namespace Lattice.Merkle

variable {K V D : Type} [DecidableEq K]

/-! ## Reading a batch -/

theorem Batch.mem_of_get : ∀ {ws : Batch K V} {k : List K} {o : Op V},
    ws.get k = some o → (k, o) ∈ ws
  | [], _, _, h => by simp [Batch.get] at h
  | (k', o') :: ws, k, o, h => by
    simp only [Batch.get] at h
    split at h
    · next e => subst e; simp only [Option.some.injEq] at h; subst h; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (Batch.mem_of_get h)

theorem Batch.get_of_mem : ∀ {ws : Batch K V} {k : List K} {o : Op V},
    ws.Nodup → (k, o) ∈ ws → ws.get k = some o
  | [], _, _, _, h => by simp at h
  | (k', o') :: ws, k, o, hn, h => by
    simp only [Batch.Nodup, List.map_cons, List.nodup_cons, List.mem_map] at hn
    simp only [Batch.get]
    rcases List.mem_cons.1 h with e | h
    · simp only [Prod.mk.injEq] at e; obtain ⟨rfl, rfl⟩ := e; simp
    · have : k' ≠ k := fun e => hn.1 ⟨(k, o), h, e.symm⟩
      simp only [this, ite_false]
      exact Batch.get_of_mem hn.2 h

theorem Batch.get_eq_none : ∀ {ws : Batch K V} {k : List K}, ws.get k = none ↔ ∀ w ∈ ws, w.1 ≠ k
  | [], _ => by simp [Batch.get]
  | (k', o') :: ws, k => by
    simp only [Batch.get, List.mem_cons, forall_eq_or_imp]
    split
    · next e => simp [e]
    · next e => simp [e, Batch.get_eq_none]

theorem Batch.get_cons {k k' : List K} {o : Op V} {ws : Batch K V} :
    Batch.get ((k', o) :: ws) k = if k' = k then some o else ws.get k := rfl

/-! ## Scoping a batch -/

theorem Batch.mem_at {c : K} : ∀ {ws : Batch K V} {w : List K × Op V},
    w ∈ ws.at c ↔ w ∈ ws ∧ w.1.head? = some c
  | [], _ => by simp [Batch.at]
  | (k, o) :: ws, w => by
    simp only [Batch.at]
    split
    · next h =>
      simp only [List.mem_cons, Batch.mem_at]
      constructor
      · rintro (rfl | ⟨h1, h2⟩)
        · exact ⟨Or.inl rfl, h⟩
        · exact ⟨Or.inr h1, h2⟩
      · rintro ⟨rfl | h1, h2⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨h1, h2⟩
    · next h =>
      simp only [List.mem_cons, Batch.mem_at]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨Or.inr h1, h2⟩
      · rintro ⟨rfl | h1, h2⟩
        · exact absurd h2 h
        · exact ⟨h1, h2⟩

theorem Batch.mem_under {q : List K} : ∀ {ws : Batch K V} {r : List K} {o : Op V},
    (r, o) ∈ ws.under q ↔ (q ++ r, o) ∈ ws
  | [], _, _ => by simp [Batch.under]
  | (k, o') :: ws, r, o => by
    simp only [Batch.under]
    split
    · next r' h =>
      obtain rfl := dropPrefix_eq_some.1 h
      simp only [List.mem_cons, Prod.mk.injEq, List.append_right_inj, Batch.mem_under]
    · next h =>
      simp only [List.mem_cons, Prod.mk.injEq, Batch.mem_under]
      constructor
      · exact Or.inr
      · rintro (⟨rfl, rfl⟩ | h1)
        · simp [dropPrefix_append_self] at h
        · exact h1

theorem Batch.get_at {c : K} : ∀ {ws : Batch K V} {k : List K},
    (ws.at c).get k = if k.head? = some c then ws.get k else none
  | [], _ => by simp [Batch.at, Batch.get]
  | (k', o) :: ws, k => by
    simp only [Batch.at, Batch.get]
    split
    · next h =>
      simp only [Batch.get, Batch.get_at]
      by_cases e : k' = k
      · subst e; simp [h]
      · simp [e]
    · next h =>
      rw [Batch.get_at]
      by_cases e : k' = k
      · subst e; simp [h]
      · simp [e]

theorem Batch.get_under {q : List K} : ∀ {ws : Batch K V} {k : List K},
    (ws.under q).get k = ws.get (q ++ k)
  | [], _ => by simp [Batch.under, Batch.get]
  | (k', o) :: ws, k => by
    simp only [Batch.under, Batch.get]
    split
    · next r h =>
      obtain rfl := dropPrefix_eq_some.1 h
      simp only [Batch.get, List.append_right_inj, Batch.get_under]
    · next h =>
      rw [Batch.get_under]
      have : k' ≠ q ++ k := fun e => by subst e; simp [dropPrefix_append_self] at h
      simp [this]

theorem Batch.nodup_at {c : K} {ws : Batch K V} (h : ws.Nodup) : (ws.at c).Nodup := by
  unfold Batch.Nodup at *
  induction ws with
  | nil => simp [Batch.at]
  | cons w ws ih =>
    simp only [List.map_cons, List.nodup_cons] at h
    simp only [Batch.at]
    split
    · simp only [List.map_cons, List.nodup_cons]
      refine ⟨fun hm => h.1 ?_, ih h.2⟩
      obtain ⟨w', hw', e⟩ := List.mem_map.1 hm
      exact List.mem_map.2 ⟨w', (Batch.mem_at.1 hw').1, e⟩
    · exact ih h.2

theorem Batch.nodup_under {q : List K} {ws : Batch K V} (h : ws.Nodup) : (ws.under q).Nodup := by
  unfold Batch.Nodup at *
  induction ws with
  | nil => simp [Batch.under]
  | cons w ws ih =>
    obtain ⟨k, o⟩ := w
    simp only [List.map_cons, List.nodup_cons] at h
    simp only [Batch.under]
    split
    · next r hr =>
      obtain rfl := dropPrefix_eq_some.1 hr
      simp only [List.map_cons, List.nodup_cons]
      refine ⟨fun hm => h.1 ?_, ih h.2⟩
      obtain ⟨⟨r', o'⟩, hw', e⟩ := List.mem_map.1 hm
      simp only at e; subst e
      exact List.mem_map.2 ⟨_, Batch.mem_under.1 hw', rfl⟩
    · exact ih h.2

theorem Batch.at_eq_nil {c : K} {ws : Batch K V} :
    ws.at c = [] ↔ ∀ w ∈ ws, w.1.head? ≠ some c := by
  constructor
  · intro h w hw hc
    have : w ∈ ws.at c := Batch.mem_at.2 ⟨hw, hc⟩
    rw [h] at this; simp at this
  · intro h
    apply List.eq_nil_iff_forall_not_mem.2
    intro w hw
    exact h w (Batch.mem_at.1 hw).1 (Batch.mem_at.1 hw).2

theorem Batch.at_at {c : K} {ws : Batch K V} : (ws.at c).at c = ws.at c := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [Batch.at]
    split
    · next h => simp [Batch.at, h, ih]
    · exact ih

theorem Batch.at_of_all {c : K} : ∀ {ws : Batch K V}, (∀ w ∈ ws, w.1.head? = some c) → ws.at c = ws
  | [], _ => rfl
  | (k, o) :: ws, h => by
    simp only [Batch.at, h (k, o) List.mem_cons_self, ite_true]
    rw [Batch.at_of_all fun w hw => h w (List.mem_cons_of_mem _ hw)]

theorem Batch.under_under {q r : List K} : ∀ {ws : Batch K V},
    (ws.under q).under r = ws.under (q ++ r)
  | [] => rfl
  | (k, o) :: ws => by
    simp only [Batch.under, dropPrefix_append]
    cases h : dropPrefix q k with
    | none => simp [Batch.under_under]
    | some k2 =>
      simp only [Batch.under, Option.bind_some]
      cases dropPrefix r k2 <;> simp [Batch.under_under]

theorem Batch.under_at {c : K} {r : List K} : ∀ {ws : Batch K V},
    (ws.at c).under (c :: r) = ws.under (c :: r)
  | [] => rfl
  | (k, o) :: ws => by
    simp only [Batch.at]
    split
    · simp only [Batch.under, Batch.under_at]
    · next h =>
      simp only [Batch.under]
      have : dropPrefix (c :: r) k = none := by
        cases k with
        | nil => rfl
        | cons a k => exact dropPrefix_cons_ne _ _ (fun e => h (by simp [e]))
      rw [this, Batch.under_at]

/-! ## Heads -/

theorem Batch.mem_heads {c : K} : ∀ {ws : Batch K V},
    c ∈ ws.heads ↔ ∃ w ∈ ws, w.1.head? = some c
  | [] => by simp [Batch.heads]
  | ([], o) :: ws => by simp [Batch.heads, Batch.mem_heads]
  | (a :: k, o) :: ws => by
    have ih := Batch.mem_heads (c := c) (ws := ws)
    simp only [Batch.heads, List.mem_cons, exists_eq_or_imp, List.head?_cons, Option.some.injEq]
    split
    · next h =>
      rw [ih]; constructor
      · exact Or.inr
      · rintro (rfl | h2)
        · exact ih.1 h
        · exact h2
    · rw [List.mem_cons, ih]; constructor
      · rintro (rfl | h2)
        · exact Or.inl rfl
        · exact Or.inr h2
      · rintro (rfl | h2)
        · exact Or.inl rfl
        · exact Or.inr h2

theorem Batch.nodup_heads : ∀ {ws : Batch K V}, ws.heads.Nodup
  | [] => List.nodup_nil
  | ([], _) :: ws => Batch.nodup_heads (ws := ws)
  | (_ :: _, _) :: ws => by
    have h := Batch.nodup_heads (ws := ws)
    simp only [Batch.heads]
    split
    · exact h
    · next hn => exact List.nodup_cons.2 ⟨hn, h⟩

/-! ## Common prefixes -/

theorem lcp_prefix_left : ∀ a b : List K, lcp a b <+: a
  | [], _ => by simp [lcp]
  | _ :: _, [] => by simp [lcp]
  | x :: a, y :: b => by
    simp only [lcp]
    split
    · exact (List.prefix_cons_inj x).2 (lcp_prefix_left a b)
    · exact List.nil_prefix

theorem lcp_prefix_right : ∀ a b : List K, lcp a b <+: b
  | [], _ => by simp [lcp]
  | _ :: _, [] => by simp [lcp]
  | x :: a, y :: b => by
    simp only [lcp]
    split
    · next h => subst h; exact (List.prefix_cons_inj x).2 (lcp_prefix_right a b)
    · exact List.nil_prefix

theorem lcp_greatest : ∀ {x a b : List K}, x <+: a → x <+: b → x <+: lcp a b
  | [], _, _, _, _ => List.nil_prefix
  | _ :: _, [], _, h, _ => by simp at h
  | _ :: _, _ :: _, [], _, h => by simp at h
  | z :: x, u :: a, w :: b, h1, h2 => by
    rw [List.cons_prefix_cons] at h1 h2
    obtain ⟨rfl, h1⟩ := h1
    obtain ⟨rfl, h2⟩ := h2
    simp only [lcp, ite_true]
    exact (List.prefix_cons_inj z).2 (lcp_greatest h1 h2)

theorem Batch.common_prefix : ∀ {ws : Batch K V} {w : List K × Op V}, w ∈ ws → ws.common <+: w.1
  | [], _, h => by simp at h
  | [(k, o)], w, h => by simp at h; subst h; exact List.prefix_refl _
  | (k, o) :: (k2, o2) :: ws, w, h => by
    simp only [Batch.common]
    rcases List.mem_cons.1 h with rfl | h
    · exact lcp_prefix_left _ _
    · exact (lcp_prefix_right _ _).trans (Batch.common_prefix h)

theorem Batch.common_greatest {x : List K} : ∀ {ws : Batch K V}, ws ≠ [] →
    (∀ w ∈ ws, x <+: w.1) → x <+: ws.common
  | [], h, _ => absurd rfl h
  | [(k, o)], _, h => h _ List.mem_cons_self
  | (k, o) :: (k2, o2) :: ws, _, h => by
    simp only [Batch.common]
    exact lcp_greatest (h _ List.mem_cons_self)
      (Batch.common_greatest (by simp) fun w hw => h w (List.mem_cons_of_mem _ hw))

theorem Batch.under_ne_nil {q : List K} {ws : Batch K V} (h : ws ≠ [])
    (hq : ∀ w ∈ ws, q <+: w.1) : ws.under q ≠ [] := by
  obtain ⟨⟨k, o⟩, hw⟩ := List.exists_mem_of_ne_nil _ h
  obtain ⟨r, rfl⟩ := hq _ hw
  intro he
  have : (r, o) ∈ ws.under q := Batch.mem_under.2 hw
  rw [he] at this; simp at this

/-- Every write under `c` extends `childPrefix c`. -/
theorem childPrefix_prefix {c : K} {ws : Batch K V} (hc : ∀ w ∈ ws, w.1.head? = some c) :
    ∀ w ∈ ws, childPrefix c ws <+: w.1 := by
  rintro ⟨k, o⟩ hw
  have := hc _ hw
  cases k with
  | nil => simp at this
  | cons a t =>
    simp only [List.head?_cons, Option.some.injEq] at this; subst this
    have hm : (t, o) ∈ ws.under [a] := Batch.mem_under.2 hw
    exact (List.prefix_cons_inj a).2 (Batch.common_prefix hm)

theorem childPrefix_greatest {c : K} {ws : Batch K V} {x : List K}
    (hc : ∀ w ∈ ws, w.1.head? = some c) (hne : ws ≠ []) (hx : ∀ w ∈ ws, x <+: w.1) :
    x <+: childPrefix c ws := by
  cases x with
  | nil => exact List.nil_prefix
  | cons a x =>
    obtain ⟨⟨k, o⟩, hw⟩ := List.exists_mem_of_ne_nil _ hne
    have h1 := hc _ hw
    obtain ⟨r, rfl⟩ := hx _ hw
    simp only [List.cons_append, List.head?_cons, Option.some.injEq] at h1; subst h1
    unfold childPrefix
    refine List.prefix_cons_inj _ |>.2 (Batch.common_greatest ?_ ?_)
    · exact Batch.under_ne_nil hne fun w hw => by
        have := hc w hw
        cases hk : w.1 with
        | nil => rw [hk] at this; simp at this
        | cons b t => rw [hk] at this; simp at this; subst this; exact ⟨t, rfl⟩
    · rintro ⟨t, o'⟩ ht
      have := hx _ (Batch.mem_under.1 ht)
      simpa using this

/-- With no write exactly at `childPrefix c`, the writes part in at least two
directions right after it. -/
theorem childPrefix_two_heads {c : K} {ws : Batch K V} (hc : ∀ w ∈ ws, w.1.head? = some c)
    (hne : ws ≠ []) (hown : (ws.under (childPrefix c ws)).get [] = none) :
    2 ≤ (ws.under (childPrefix c ws)).heads.length := by
  have hq := childPrefix_prefix hc
  have hT : ws.under (childPrefix c ws) ≠ [] := Batch.under_ne_nil hne hq
  -- every write strictly extends `q`
  have hlong : ∀ w ∈ ws.under (childPrefix c ws), w.1 ≠ [] := by
    intro w hw he
    rw [Batch.get_eq_none] at hown
    exact hown w hw he
  obtain ⟨⟨r0, o0⟩, h0⟩ := List.exists_mem_of_ne_nil _ hT
  obtain ⟨d, r0', rfl⟩ : ∃ d r0', r0 = d :: r0' := by
    cases r0 with
    | nil => exact absurd rfl (hlong _ h0)
    | cons d r => exact ⟨d, r, rfl⟩
  have hd : d ∈ (ws.under (childPrefix c ws)).heads := Batch.mem_heads.2 ⟨_, h0, rfl⟩
  apply Classical.byContradiction
  intro hlt
  have hall : ∀ w ∈ ws.under (childPrefix c ws), w.1.head? = some d := by
    intro w hw
    obtain ⟨k, o⟩ := w
    cases k with
    | nil => exact absurd rfl (hlong _ hw)
    | cons e k =>
      have he : e ∈ (ws.under (childPrefix c ws)).heads := Batch.mem_heads.2 ⟨_, hw, rfl⟩
      have hl : (ws.under (childPrefix c ws)).heads.length ≤ 1 := by omega
      have : ∀ x ∈ (ws.under (childPrefix c ws)).heads, ∀ y ∈ (ws.under (childPrefix c ws)).heads, x = y := by
        intro x hx y hy
        match h : (ws.under (childPrefix c ws)).heads, hl with
        | [], _ => rw [h] at hx; simp at hx
        | [z], _ => rw [h] at hx hy; simp at hx hy; rw [hx, hy]
      simp [this e he d hd]
  have hp : childPrefix c ws ++ [d] <+: childPrefix c ws := childPrefix_greatest hc hne fun ⟨k, o⟩ hw => by
    obtain ⟨r, rfl⟩ := hq _ hw
    have hm : (r, o) ∈ ws.under (childPrefix c ws) := Batch.mem_under.2 hw
    have := hall _ hm
    cases r with
    | nil => simp at this
    | cons e r => simp at this; subst this; exact ⟨r, by simp⟩
  have := hp.length_le
  simp at this; omega

/-! ## What a batch does to a map -/

/-- The read a batch leaves: the write's value at a written key, `R`
elsewhere. -/
def Batch.upd (ws : Batch K V) (R : List K → Read V) (k : List K) : Read V :=
  match ws.get k with
  | some o => .ofOption o.post
  | none => R k

theorem Batch.upd_of_get_none {ws : Batch K V} {R : List K → Read V} {k : List K}
    (h : ws.get k = none) : ws.upd R k = R k := by
  simp [Batch.upd, h]

theorem Batch.upd_of_get_some {ws : Batch K V} {R : List K → Read V} {k : List K} {o : Op V}
    (h : ws.get k = some o) : ws.upd R k = .ofOption o.post := by
  simp [Batch.upd, h]

theorem Op.pre_none {o : Op V} : o.pre none ↔ ∃ v, o = .insert v := by
  cases o <;> simp [Op.pre]

end Lattice.Merkle
