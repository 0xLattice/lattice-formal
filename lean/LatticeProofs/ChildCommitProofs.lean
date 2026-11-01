import LatticeProofs.ChildCommit

/-!
# Transaction child commitments and derived child grinds: proofs

The statements below are the specification of `ChildCommit.lean`'s functions;
the proofs only establish them.
-/

namespace Lattice.ChildCommit

/-! ## `child/X = C@P` -/

theorem splitSep_eq {v c : Text} {p : Text} (h : splitSep v = (c, some p)) :
    v = c ++ '@' :: p := by
  induction v generalizing c with
  | nil => simp [splitSep] at h
  | cons ch cs ih =>
    unfold splitSep at h
    by_cases hc : ch = '@'
    · simp only [hc, ↓reduceIte, Prod.mk.injEq, Option.some.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [hc]
    · simp only [hc, ↓reduceIte] at h
      revert h
      cases hs : splitSep cs with
      | mk a r =>
        intro h
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [ih hs]

/-- A parsed value is `C ++ "@" ++ P`: the parse is injective. -/
theorem commitValue_eq {v c p : Text} (h : commitValue v = some (c, p)) : v = c ++ '@' :: p := by
  unfold commitValue at h
  split at h
  next a q hs =>
    split at h
    next =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact splitSep_eq hs
    next => simp at h
  next => simp at h

/-- The rule, decided by `commitsValid` from the carrier's own fields: with any
commitment the index is well-formed, and every commitment `child/X = v` has
`v = C@P` with `P` the carrier's `prevState` and `children[X] = C`. The
carrier names a child by CID only, so no child block is read. -/
theorem commitsValid_iff (b : Carrier) :
    commitsValid b = true ↔
      (commitments b.actions ≠ [] → b.childrenWellFormed = true) ∧
      ∀ x v, (x, v) ∈ commitments b.actions →
        ∃ c, commitValue v = some (c, b.prevState) ∧ b.children.lookup x = some c := by
  unfold commitsValid
  cases hcs : commitments b.actions with
  | nil => simp
  | cons e es =>
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true,
      List.all_eq_true, ne_eq, reduceCtorEq, not_false_eq_true, forall_const]
    apply and_congr Iff.rfl
    constructor
    · intro h x v hm
      have := h (x, v) hm
      revert this
      cases hv : commitValue v with
      | none => simp
      | some cp =>
        obtain ⟨c, p⟩ := cp
        simp only [Bool.and_eq_true, beq_iff_eq]
        rintro ⟨rfl, hl⟩
        exact ⟨c, rfl, hl⟩
    · intro h xv hm
      obtain ⟨c, hv, hl⟩ := h xv.1 xv.2 hm
      simp [hv, hl]

/-- Whether a carrier satisfies the rules is computed from its header,
transaction and children fields alone. -/
def valid_decidable (b : Carrier) : Decidable (Valid b) := inferInstance

/-- **The C@P rule.** A valid carrier that commits `child/X = C@P` holds `C` at
`children[X]` and enters `P`. -/
theorem commit_sound {b : Carrier} (hv : Valid b) {x v c p : Text}
    (hm : (x, v) ∈ commitments b.actions) (hp : commitValue v = some (c, p)) :
    b.children.lookup x = some c ∧ p = b.prevState := by
  obtain ⟨c', hv', hl⟩ := ((commitsValid_iff b).1 hv.2).2 x v hm
  rw [hp] at hv'
  simp only [Option.some.injEq, Prod.mk.injEq] at hv'
  obtain ⟨rfl, rfl⟩ := hv'
  exact ⟨hl, rfl⟩

/-- A stale `P` makes the carrier invalid, whatever else it holds. -/
theorem stale_invalid {b : Carrier} {x v c p : Text}
    (hm : (x, v) ∈ commitments b.actions) (hp : commitValue v = some (c, p))
    (hs : p ≠ b.prevState) : ¬ Valid b :=
  fun hv => hs (commit_sound hv hm hp).2

/-- A commitment to a `C` that is not at `children[X]` makes the carrier invalid. -/
theorem absent_invalid {b : Carrier} {x v c p : Text}
    (hm : (x, v) ∈ commitments b.actions) (hp : commitValue v = some (c, p))
    (hs : b.children.lookup x ≠ some c) : ¬ Valid b :=
  fun hv => hs (commit_sound hv hm hp).1

/-- Two commitments to one directory that both satisfy the rule are equal:
both are `children[X]@prevState`. -/
theorem commit_values_agree {b : Carrier} (hv : commitsValid b = true) {x v₁ v₂ : Text}
    (h₁ : (x, v₁) ∈ commitments b.actions) (h₂ : (x, v₂) ∈ commitments b.actions) :
    v₁ = v₂ := by
  obtain ⟨c₁, hv₁, hl₁⟩ := ((commitsValid_iff b).1 hv).2 x v₁ h₁
  obtain ⟨c₂, hv₂, hl₂⟩ := ((commitsValid_iff b).1 hv).2 x v₂ h₂
  rw [hl₁] at hl₂
  cases hl₂
  rw [commitValue_eq hv₁, commitValue_eq hv₂]

theorem key_of_commitment {a : Action} {x v : Text} (h : commitment a = some (x, v)) :
    a.key = childPrefix ++ x ∧ a.newValue = some v := by
  unfold commitment at h
  cases hn : a.newValue with
  | none => simp [hn] at h
  | some w =>
    simp only [hn] at h
    by_cases hp : childPrefix.isPrefixOf a.key = true
    · simp only [hp, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨?_, rfl⟩
      have := List.prefix_iff_eq_take.1 (List.isPrefixOf_iff_prefix.1 hp)
      conv => lhs; rw [← List.take_append_drop childPrefix.length a.key]
      rw [← this]
    · simp [hp] at h

theorem mem_commitments {as : List Action} {x v : Text} :
    (x, v) ∈ commitments as ↔ ∃ a ∈ as, commitment a = some (x, v) := by
  simp [commitments, List.mem_filterMap]

theorem eq_of_nodup_map {f : α → β} : ∀ {l : List α}, (l.map f).Nodup →
    ∀ {a b}, a ∈ l → b ∈ l → f a = f b → a = b
  | [], _, _, _, ha, _, _ => absurd ha (List.not_mem_nil)
  | c :: l, hn, a, b, ha, hb, he => by
    rw [List.map_cons, List.nodup_cons] at hn
    have hc : ∀ x ∈ l, f x ≠ f c := fun x hx hfx => hn.1 (List.mem_map.2 ⟨x, hx, hfx⟩)
    rcases List.mem_cons.1 ha with ea | la <;> rcases List.mem_cons.1 hb with eb | lb
    · rw [ea, eb]
    · subst ea; exact absurd he.symm (hc b lb)
    · subst eb; exact absurd he (hc a la)
    · exact eq_of_nodup_map hn.2 la lb he

/-- **One action per directory.** In a valid carrier the actions committing
into one directory are one action: two writes to `child/X` share a key, and
two actions on one key are a state conflict. -/
theorem commit_unique {b : Carrier} (hv : Valid b) {a₁ a₂ : Action} {x v₁ v₂ : Text}
    (h₁ : a₁ ∈ b.actions) (h₂ : a₂ ∈ b.actions)
    (c₁ : commitment a₁ = some (x, v₁)) (c₂ : commitment a₂ = some (x, v₂)) : a₁ = a₂ :=
  eq_of_nodup_map hv.1 h₁ h₂ ((key_of_commitment c₁).1.trans (key_of_commitment c₂).1.symm)

/-! ## Proofs as header paths -/

theorem linksFrom_append (B : Header) (p q : List (Text × Header)) :
    linksFrom B (p ++ q) ↔ linksFrom B p ∧ linksFrom (terminalFrom B p) q := by
  induction p generalizing B with
  | nil => simp [linksFrom, terminalFrom]
  | cons e p ih =>
    obtain ⟨d, N⟩ := e
    simp only [List.cons_append, linksFrom, terminalFrom, ih, and_assoc]

theorem terminalFrom_append (B : Header) (p q : List (Text × Header)) :
    terminalFrom B (p ++ q) = terminalFrom (terminalFrom B p) q := by
  induction p generalizing B with
  | nil => rfl
  | cons e p ih => obtain ⟨d, N⟩ := e; exact ih N

/-- Composition is associative. -/
theorem compose_assoc (p q r : Proof) :
    (p.compose q).compose r = p.compose (q.compose r) := by
  simp [Proof.compose, List.append_assoc]

/-- A composed path is valid exactly when both parts are, given the seam: the
hop is rooted at the upstream's terminal. -/
theorem compose_valid {p q : Proof} (hs : q.root = p.terminal) :
    (p.compose q).Valid ↔ p.Valid ∧ q.Valid := by
  simp only [Proof.Valid, Proof.compose, linksFrom_append, hs, Proof.terminal]

theorem compose_terminal {p q : Proof} (hs : q.root = p.terminal) :
    (p.compose q).terminal = q.terminal := by
  simp only [Proof.terminal, Proof.compose, terminalFrom_append, hs]

/-- **Verification of a composed path is the conjunction of its parts**: the
upstream path is valid, and the hop verifies under the upstream root's grind. -/
theorem verifies_compose (pow : Header → Nat) {p q : Proof} {C : Header}
    (hs : q.root = p.terminal) (hq : q.hops ≠ []) :
    Verifies pow (p.compose q) C ↔ p.Valid ∧ VerifiesAt (pow p.root) q C := by
  unfold Verifies VerifiesAt
  rw [compose_valid hs, compose_terminal hs]
  simp only [Proof.compose]
  constructor
  · rintro ⟨_, ⟨hp, hq'⟩, ht, hm⟩; exact ⟨hp, hq, hq', ht, hm⟩
  · rintro ⟨hp, _, hq', ht, hm⟩
    exact ⟨by simp [hq], ⟨hp, hq'⟩, ht, hm⟩

/-- **Derived-proof soundness.** A path from a grind root to carrier `B`,
extended by `B`'s hop to the block `C` it commits at `X`, verifies for `C`
exactly when the grind meets `C`'s target. -/
theorem derived_sound (pow : Header → Nat) {p : Proof} {B C : Header} {X : Text}
    (hp : p.Valid) (hB : p.terminal = B) (hl : Link B X C) :
    Verifies pow (p.compose (hop B X C)) C ↔ Work.Meets C.target (pow p.root) := by
  rw [verifies_compose pow hB.symm (by simp [hop])]
  constructor
  · exact fun h => h.2.2.2.2
  · intro hm
    exact ⟨hp, by simp [hop], ⟨hl, trivial⟩, rfl, hm⟩

theorem terminalFrom_mem (B : Header) :
    ∀ hs : List (Text × Header), hs ≠ [] → terminalFrom B hs ∈ hs.map Prod.snd
  | [], h => absurd rfl h
  | [(_, N)], _ => by simp [terminalFrom]
  | (_, N) :: e :: rest, _ => by
    have := terminalFrom_mem N (e :: rest) (by simp)
    simp only [terminalFrom] at this ⊢
    exact List.mem_cons_of_mem _ this

/-- **No proof verifies for a block off its path.** -/
theorem verifies_on_path (pow : Header → Nat) {p : Proof} {C : Header}
    (h : Verifies pow p C) : C ∈ p.blocks := by
  obtain ⟨hn, _, ht, _⟩ := h
  rw [← ht]
  exact terminalFrom_mem p.root p.hops hn

theorem not_verifies_off_path (pow : Header → Nat) {p : Proof} {C : Header}
    (h : C ∉ p.blocks) : ¬ Verifies pow p C :=
  fun hv => h (verifies_on_path pow hv)

/-! ## Credit by location -/

/-- Inserting the same observation twice is inserting it once. -/
theorem insert_idem (m : Credits) (g b : Text) (w : Nat) :
    (m.insert g b w).insert g b w = m.insert g b w := by
  funext g' b'
  simp only [Credits.insert]
  by_cases h : g' = g ∧ b' = b <;> simp [h, Nat.max_assoc]

/-- The order of observations does not matter. -/
theorem insert_comm (m : Credits) (g₁ b₁ w₁ g₂ b₂ w₂) :
    (m.insert g₁ b₁ w₁).insert g₂ b₂ w₂ = (m.insert g₂ b₂ w₂).insert g₁ b₁ w₁ := by
  funext g' b'
  simp only [Credits.insert]
  by_cases h₁ : g' = g₁ ∧ b' = b₁ <;> by_cases h₂ : g' = g₂ ∧ b' = b₂
  · obtain ⟨rfl, rfl⟩ := h₁; obtain ⟨rfl, rfl⟩ := h₂
    simp [Nat.max_assoc, Nat.max_comm w₁ w₂]
  · obtain ⟨rfl, rfl⟩ := h₁
    simp only [and_self, ↓reduceIte, h₂]
  · obtain ⟨rfl, rfl⟩ := h₂
    simp only [and_self, ↓reduceIte, h₁]
  · simp [h₁, h₂]

/-- The credit at a location is bounded by `x` exactly when the prior credit
and every observation of that location are. -/
theorem applyAll_le_iff (m : Credits) (es : List Credit) (g b : Text) (x : Nat) :
    applyAll m es g b ≤ x ↔
      m g b ≤ x ∧ ∀ e ∈ es, e.root = g → e.block = b → e.work ≤ x := by
  induction es generalizing m with
  | nil => simp [applyAll]
  | cons e es ih =>
    simp only [applyAll, List.foldl_cons] at ih ⊢
    rw [ih]
    simp only [Credits.insert, List.mem_cons, forall_eq_or_imp]
    by_cases h : g = e.root ∧ b = e.block
    · obtain ⟨rfl, rfl⟩ := h
      simp only [and_self, ↓reduceIte, Nat.max_le, forall_const]
      exact ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩⟩
    · simp only [h, ↓reduceIte]
      have : ¬ (e.root = g ∧ e.block = b) := fun h' => h ⟨h'.1.symm, h'.2.symm⟩
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun hg hb => absurd ⟨hg, hb⟩ this, h2⟩
      · rintro ⟨h1, _, h2⟩
        exact ⟨h1, h2⟩

/-- The credit at a location is the prior credit or one observation's
quantity: never a sum of observations. -/
theorem applyAll_attained (m : Credits) (es : List Credit) (g b : Text) :
    applyAll m es g b = m g b ∨
      ∃ e ∈ es, e.root = g ∧ e.block = b ∧ applyAll m es g b = e.work := by
  induction es generalizing m with
  | nil => simp [applyAll]
  | cons e es ih =>
    simp only [applyAll, List.foldl_cons] at ih ⊢
    rcases ih (m.insert e.root e.block e.work) with h | ⟨e', he', h1, h2, h3⟩
    · rw [h]
      simp only [Credits.insert]
      by_cases hl : g = e.root ∧ b = e.block
      · obtain ⟨rfl, rfl⟩ := hl
        simp only [and_self, ↓reduceIte]
        rcases Nat.le_total (m e.root e.block) e.work with hw | hw
        · exact Or.inr ⟨e, List.mem_cons_self, rfl, rfl, Nat.max_eq_right hw⟩
        · exact Or.inl (Nat.max_eq_left hw)
      · simp [hl]
    · exact Or.inr ⟨e', List.mem_cons_of_mem _ he', h1, h2, h3⟩

/-- **No double credit.** The credits depend only on which observations were
made, not on how many times, by how many proofs, carriers or derivations, or
in what order. -/
theorem no_double_credit (m : Credits) {es es' : List Credit} (h : ∀ e, e ∈ es ↔ e ∈ es') :
    applyAll m es = applyAll m es' := by
  funext g b
  apply Nat.le_antisymm
  · have := (applyAll_le_iff m es' g b _).1 (Nat.le_refl _)
    exact (applyAll_le_iff m es g b _).2 ⟨this.1, fun e he => this.2 e ((h e).1 he)⟩
  · have := (applyAll_le_iff m es g b _).1 (Nat.le_refl _)
    exact (applyAll_le_iff m es' g b _).2 ⟨this.1, fun e he => this.2 e ((h e).2 he)⟩

/-- One observation named `n + 1` times credits what it credits once. -/
theorem replicate_credits_once (m : Credits) (e : Credit) (n : Nat) :
    applyAll m (List.replicate (n + 1) e) = applyAll m [e] :=
  no_double_credit m fun e' => by simp [List.mem_replicate]

/-! ## Run binding -/

/-- **A run credits only an anchored block.** -/
theorem run_credit_bound {K : Carrier} {X : Text} {C : Child} {run grind v : Nat}
    (h : runCredit K X C run grind = some v) :
    K.children.lookup X = some C.cid ∧ C.parentState = K.prevState := by
  unfold runCredit at h
  by_cases hc : K.children.lookup X = some C.cid ∧ C.parentState = K.prevState
  · exact hc
  · simp [hc] at h

/-- A valid carrier's `child/X = C@P`, for a `C` built on `P`, always meets
the binding: the run credits `C`. -/
theorem commit_meets_binding {K : Carrier} (hv : Valid K) {X v P : Text} {C : Child}
    (hm : (X, v) ∈ commitments K.actions) (hp : commitValue v = some (C.cid, P))
    (hC : C.parentState = P) (run grind : Nat) :
    runCredit K X C run grind = some (run - grind) := by
  obtain ⟨hl, hP⟩ := commit_sound hv hm hp
  unfold runCredit
  simp [hl, hC, hP]

/-- A `C` built on a stale `P` (not `K.prevState`) never takes `K`'s run,
whether or not `K` is valid. -/
theorem stale_no_credit {K : Carrier} {X P : Text} {C : Child}
    (hC : C.parentState = P) (hs : P ≠ K.prevState) (run grind : Nat) :
    runCredit K X C run grind = none := by
  unfold runCredit
  simp [hC, hs]

end Lattice.ChildCommit
