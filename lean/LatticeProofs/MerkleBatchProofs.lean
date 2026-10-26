import LatticeProofs.MerkleBatchCanon
import LatticeProofs.MerkleBatchCongr
import LatticeProofs.MerkleBatchLive
import LatticeProofs.MerkleProofs

/-! # Batched writes (cashew `MerkleDictionary.transform(transforms:)`)

A block's writes to one sub-state are applied by cashew in one recursive pass
over the trie (`MerkleBatch.lean`), not one after another. These theorems
tie that pass to the sequential model of `MerkleProofs.lean`:

* `batch_eq_sequential`: on a canonical trie the batch gives what the writes
  give one after another, in any order, and fails exactly when they fail;
* `batch_canonical`, `reachable_canonical`: it keeps the canonical form of
  §3.4.1, so every state built from the empty state by batches is canonical;
* `batch_sound`: run on a partial trie that commits to the same root, it
  gives the root the full trie gives;
* `proof_scope`: the partial trie cashew's `proof(paths:)` builds for the
  batch exists exactly when the batch succeeds, commits to the same root,
  and suffices to run the batch. -/

set_option linter.unusedSectionVars false

namespace Lattice.Merkle

variable {K V D : Type} [DecidableEq K] [LT K] [DecidableRel (α := K) (· < ·)]
variable {H : Enc K V D → D}

/-! ## The map a batch makes -/

/-- The map after a batch with one write per key. -/
def Batch.updMap (ws : Batch K V) (m : List K → Option V) (k : List K) : Option V :=
  match ws.get k with
  | some o => o.post
  | none => m k

theorem Batch.updMap_cons {k : List K} {o : Op V} {ws : Batch K V} {m : List K → Option V}
    (hn : Batch.Nodup ((k, o) :: ws)) :
    ws.updMap (fun k' => if k' = k then o.post else m k') = Batch.updMap ((k, o) :: ws) m := by
  funext k'
  have hk : ws.get k = none := Batch.get_eq_none.2 fun w hw he =>
    (List.nodup_cons.1 hn).1 (by rw [← he]; exact List.mem_map_of_mem (f := fun w => w.1) hw)
  simp only [Batch.updMap, Batch.get_cons]
  by_cases h : k = k'
  · subst h; simp [hk]
  · simp only [h, ite_false]
    cases ws.get k' <;> simp [Ne.symm h]

theorem Batch.Nodup.tail {w : List K × Op V} {ws : Batch K V} (hn : Batch.Nodup (w :: ws)) :
    ws.Nodup := (List.nodup_cons.1 hn).2

theorem Batch.Nodup.ne {k : List K} {o : Op V} {ws : Batch K V} (hn : Batch.Nodup ((k, o) :: ws))
    {w : List K × Op V} (hw : w ∈ ws) : w.1 ≠ k := fun he =>
  (List.nodup_cons.1 hn).1 (by rw [← he]; exact List.mem_map_of_mem (f := fun w => w.1) hw)

/-- One write per key: the writes, one after another, succeed on the map
when each one's precondition holds on the map before the batch. -/
theorem applyAllMap_of_pre :
    ∀ {ws : Batch K V} {m : List K → Option V}, ws.Nodup → (∀ w ∈ ws, w.2.pre (m w.1)) →
      applyAllMap ws m = some (ws.updMap m)
  | [], m, _, _ => by simp only [applyAllMap]; rfl
  | (k, o) :: ws, m, hn, hp => by
    simp only [applyAllMap, Op.applyMap_of_pre (hp _ (List.mem_cons_self ..)), Option.bind_eq_bind,
      Option.bind_some]
    rw [applyAllMap_of_pre hn.tail fun w hw => by
      simp only [hn.ne hw, ite_false]; exact hp w (List.mem_cons_of_mem _ hw)]
    rw [Batch.updMap_cons hn]

theorem pre_of_applyAllMap :
    ∀ {ws : Batch K V} {m : List K → Option V}, ws.Nodup → applyAllMap ws m ≠ none →
      ∀ w ∈ ws, w.2.pre (m w.1)
  | [], _, _, _ => by simp
  | (k, o) :: ws, m, hn, h => by
    simp only [applyAllMap, Option.bind_eq_bind] at h
    have h1 : o.applyMap k m ≠ none := fun e => by simp [e] at h
    rw [Op.applyMap_of_pre (Op.pre_of_applyMap h1), Option.bind_some] at h
    have ih := pre_of_applyAllMap hn.tail h
    intro w hw
    rcases List.mem_cons.1 hw with rfl | hw
    · exact Op.pre_of_applyMap h1
    · have := ih w hw; simp only [hn.ne hw, ite_false] at this; exact this

/-! ## One after another -/

theorem Root.apply_count {o : Op V} {k : List K} {s s' : Root K V D}
    (h : s.apply o k = some s') : s'.count = s.count + o.delta := by
  cases k with
  | nil => simp [Root.apply] at h
  | cons c r =>
    simp only [Root.apply] at h
    split at h
    · split at h
      · simp only [Option.some.injEq] at h; subst h; rfl
      · simp at h
    · simp at h
    · simp only [Option.some.injEq] at h; subst h; rfl

theorem Root.applyAll_count :
    ∀ {ws : Batch K V} {s s' : Root K V D}, s.applyAll ws = some s' → s'.count = s.count + ws.delta
  | [], s, s', h => by simp only [Root.applyAll, Option.some.injEq] at h; subst h; simp [Batch.delta]
  | (k, o) :: ws, s, s', h => by
    simp only [Root.applyAll, Option.bind_eq_bind] at h
    cases h1 : s.apply o k with
    | none => simp [h1] at h
    | some s1 =>
      rw [h1, Option.bind_some] at h
      rw [Root.applyAll_count h, Root.apply_count h1, Batch.delta]; omega

theorem Root.applyAll_keys :
    ∀ {ws : Batch K V} {s s' : Root K V D}, s.applyAll ws = some s' → ∀ w ∈ ws, w.1 ≠ []
  | [], _, _, _ => by simp
  | (k, o) :: ws, s, s', h => by
    simp only [Root.applyAll, Option.bind_eq_bind] at h
    cases h1 : s.apply o k with
    | none => simp [h1] at h
    | some s1 =>
      rw [h1, Option.bind_some] at h
      intro w hw
      rcases List.mem_cons.1 hw with rfl | hw
      · rintro (e : k = []); subst e; simp [Root.apply] at h1
      · exact Root.applyAll_keys h w hw

/-- Completeness of the sequential run: one write per key, each at a
nonempty key with its precondition holding before the batch. -/
theorem applyAll_complete (ho : StrictOrder K) :
    ∀ {ws : Batch K V} {s : Root K V D}, s.Canon → ws.Nodup →
      (∀ w ∈ ws, w.1 ≠ [] ∧ w.2.pre (s.toMap w.1)) → ∃ s', s.applyAll ws = some s'
  | [], s, _, _, _ => ⟨s, rfl⟩
  | (k, o) :: ws, s, hs, hn, hp => by
    have h0 := hp _ (List.mem_cons_self ..)
    obtain ⟨s1, e1⟩ := apply_complete ho o hs h0.1 (by
      rw [Op.applyMap_of_pre h0.2]; simp)
    obtain ⟨f1, f2⟩ := apply_correct ho o hs e1
    rw [Op.applyMap_of_pre h0.2, Option.some.injEq] at f1
    obtain ⟨s', e2⟩ := applyAll_complete ho f2 hn.tail fun w hw => by
      refine ⟨(hp w (List.mem_cons_of_mem _ hw)).1, ?_⟩
      rw [← f1]; simp only [hn.ne hw, ite_false]; exact (hp w (List.mem_cons_of_mem _ hw)).2
    exact ⟨s', by simp [Root.applyAll, e1, e2]⟩

theorem applyAll_fails (ho : StrictOrder K) {ws : Batch K V} {s : Root K V D} (hs : s.Canon)
    (hn : ws.Nodup) (h : ∃ w ∈ ws, w.1 = [] ∨ ¬ w.2.pre (s.toMap w.1)) : s.applyAll ws = none := by
  cases e : s.applyAll ws with
  | none => rfl
  | some s' =>
    obtain ⟨w, hw, hb⟩ := h
    rcases hb with hb | hb
    · exact absurd hb (Root.applyAll_keys e w hw)
    · obtain ⟨f1, -⟩ := applyAll_correct ho ws hs e
      exact absurd (pre_of_applyAllMap hn (by simp [f1]) w hw) hb

/-! ## The batch on a canonical trie -/

theorem Root.batch_spec (ho : StrictOrder K) {ws : Batch K V} {s : Root K V D} (hs : s.Canon)
    (hn : ws.Nodup) :
    (s.batch ws = none → ∃ w ∈ ws, w.1 = [] ∨ ¬ w.2.pre (s.toMap w.1)) ∧
    (∀ b, s.batch ws = some b →
      (∀ w ∈ ws, w.1 ≠ [] ∧ w.2.pre (s.toMap w.1)) ∧
      (∀ y z, b.kids.lookup y z = ws.upd s.kids.read (y :: z)) ∧ b.kids.Canon ∧
      b.count = s.count + ws.delta) := by
  have IH := Kids.transform_spec ho s.kids ws hs.1 hn
  have hrd : ∀ k, k ≠ [] → s.toMap k = (s.kids.read k).toOption := by
    intro k hk; cases k with
    | nil => exact absurd rfl hk
    | cons => rfl
  unfold Root.batch
  constructor
  · intro h
    by_cases hg : ws.get [] = none
    · simp only [hg, ite_true] at h
      cases ht : s.kids.transform ws with
      | none =>
        obtain ⟨w, hw, hk, hp⟩ := IH.1 ht
        exact ⟨w, hw, Or.inr (by rwa [hrd _ hk])⟩
      | some ks => rw [ht] at h; simp at h
    · cases hg' : ws.get [] with
      | none => exact absurd hg' hg
      | some o => exact ⟨_, Batch.mem_of_get hg', Or.inl rfl⟩
  · intro b h
    by_cases hg : ws.get [] = none
    · simp only [hg, ite_true] at h
      cases ht : s.kids.transform ws with
      | none => rw [ht] at h; simp at h
      | some ks =>
        rw [ht] at h; simp only [Option.some.injEq] at h; subst h
        obtain ⟨p1, l1, c1⟩ := IH.2 ks ht
        have hk : ∀ w ∈ ws, w.1 ≠ [] := fun w hw he =>
          (Batch.get_eq_none.1 hg) w hw he
        exact ⟨fun w hw => ⟨hk w hw, by rw [hrd _ (hk w hw)]; exact p1 w hw (hk w hw)⟩, l1, c1, rfl⟩
    · simp [hg] at h

theorem Batch.get_perm {ws ws' : Batch K V} (hn : ws.Nodup) (hp : ws.Perm ws') (k : List K) :
    ws.get k = ws'.get k := by
  have hn' : ws'.Nodup := (hp.map _).nodup_iff.1 hn
  cases h : ws.get k with
  | some o => exact (Batch.get_of_mem hn' (hp.subset (Batch.mem_of_get h))).symm
  | none =>
    cases h' : ws'.get k with
    | none => rfl
    | some o =>
      rw [Batch.get_of_mem hn (hp.symm.subset (Batch.mem_of_get h'))] at h; cases h

/-- **The batch is the sequential run.** On a canonical trie, cashew's
one-pass batch of a block's writes (one per key) gives exactly what applying
them one after another gives, in any order: the same trie when they succeed,
and failure when they fail. -/
theorem batch_eq_sequential (ho : StrictOrder K) {ws ws' : Batch K V} {s : Root K V D}
    (hs : s.Canon) (hn : ws.Nodup) (hp : ws.Perm ws') : s.batch ws = s.applyAll ws' := by
  have hn' : ws'.Nodup := (hp.map _).nodup_iff.1 hn
  have S := Root.batch_spec ho hs hn
  cases hb : s.batch ws with
  | none =>
    obtain ⟨w, hw, hbad⟩ := S.1 hb
    exact (applyAll_fails ho hs hn' ⟨w, hp.subset hw, hbad⟩).symm
  | some b =>
    obtain ⟨p1, l1, c1, n1⟩ := S.2 b hb
    obtain ⟨s3, e3⟩ := applyAll_complete ho hs hn p1
    obtain ⟨s4, e4⟩ := applyAll_complete ho hs hn' fun w hw => p1 w (hp.symm.subset hw)
    obtain ⟨f3, g3⟩ := applyAll_correct ho ws hs e3
    obtain ⟨f4, g4⟩ := applyAll_correct ho ws' hs e4
    rw [applyAllMap_of_pre hn fun w hw => (p1 w hw).2, Option.some.injEq] at f3
    rw [applyAllMap_of_pre hn' fun w hw => (p1 w (hp.symm.subset hw)).2,
      Option.some.injEq] at f4
    have hm : s3.toMap = s4.toMap := by
      rw [← f3, ← f4]; funext k; simp only [Batch.updMap, Batch.get_perm hn hp k]
    have h34 := canonical_unique ho g3 g4 hm
    have hk : b.kids = s3.kids := Kids.canon_unique ho c1 g3.1 fun y z => by
      rw [l1]
      show _ = s3.lookup (y :: z)
      rw [Root.lookup_eq_ofOption g3.full, ← f3]
      simp only [Batch.upd, Batch.updMap]
      cases ws.get (y :: z) with
      | some o => rfl
      | none => exact Root.lookup_eq_ofOption hs.full (y :: z)
    have hc : b.count = s3.count := by rw [n1, Root.applyAll_count e3]
    rw [e4, ← h34]
    cases b; cases s3; simp only at hk hc; subst hk hc; rfl

/-- The batch on the map: what its writes say, and the trie stays canonical,
`count` included. -/
theorem batch_correct (ho : StrictOrder K) {ws : Batch K V} {s b : Root K V D} (hs : s.Canon)
    (hn : ws.Nodup) (h : s.batch ws = some b) :
    applyAllMap ws s.toMap = some b.toMap ∧ b.Canon := by
  rw [batch_eq_sequential ho hs hn (List.Perm.refl ws)] at h
  exact applyAll_correct ho ws hs h

/-- The batch fails exactly when a write is at the empty key or its
precondition fails on the map before the batch. -/
theorem batch_fails_iff (ho : StrictOrder K) {ws : Batch K V} {s : Root K V D} (hs : s.Canon)
    (hn : ws.Nodup) : s.batch ws = none ↔ ∃ w ∈ ws, w.1 = [] ∨ ¬ w.2.pre (s.toMap w.1) := by
  refine ⟨(Root.batch_spec ho hs hn).1, fun h => ?_⟩
  rw [batch_eq_sequential ho hs hn (List.Perm.refl ws)]
  exact applyAll_fails ho hs hn h

/-- **Canonical form is preserved** (§3.4.1). -/
theorem batch_canonical (ho : StrictOrder K) {ws : Batch K V} {s b : Root K V D} (hs : s.Canon)
    (hn : ws.Nodup) (h : s.batch ws = some b) : b.Canon :=
  (batch_correct ho hs hn h).2

/-- The states batches reach from the empty state. -/
inductive Reachable : Root K V D → Prop
  | empty : Reachable Root.empty
  | batch {s s' : Root K V D} {ws : Batch K V} :
      Reachable s → ws.Nodup → s.batch ws = some s' → Reachable s'

/-- Every state built from the empty state by batches is canonical: its root
is the root of its map (`canonical_unique`). -/
theorem reachable_canonical (ho : StrictOrder K) {s : Root K V D} (h : Reachable s) : s.Canon := by
  induction h with
  | empty => exact ⟨trivial, rfl⟩
  | batch _ hn hb ih => exact batch_canonical ho ih hn hb

/-! ## On a partial trie -/

/-- **The batch is sound on a partial trie** (`apply_sound` for a batch): a
batch that succeeds on a partial trie whose root is that of a full trie
succeeds on the full trie and gives the same root. Only the two input tries
must be free of collisions: the pass never hashes to decide. -/
theorem batch_sound {ws : Batch K V} {p s p' : Root K V D}
    (hH : NoCollision H (p.HasEnc H) (s.HasEnc H)) (hd : p.digest H = s.digest H) (hs : s.Full)
    (h : p.batch ws = some p') : ∃ s', s.batch ws = some s' ∧ p'.digest H = s'.digest H := by
  obtain ⟨s', e1, e2⟩ := Root.batch_le (Root.le_of_digest hH hs hd) h
  exact ⟨s', e1, e2.digest⟩

/-- `batch_sound` in extraction form: a partial trie on which the batch gives
another root exhibits a collision between the two input tries. -/
theorem batch_sound_or_collision {ws : Batch K V} {p s p' : Root K V D}
    (hd : p.digest H = s.digest H) (hs : s.Full) (h : p.batch ws = some p') :
    (∃ s', s.batch ws = some s' ∧ p'.digest H = s'.digest H) ∨
    ∃ e₁ e₂, p.HasEnc H e₁ ∧ s.HasEnc H e₂ ∧ e₁ ≠ e₂ ∧ H e₁ = H e₂ :=
  or_collision fun hH => batch_sound hH hd hs h

/-- A block's batch, verified on a partial trie whose root is that of the
canonical trie `s`, ends at the root of the canonical trie of the map the
writes make (`block_commits` for cashew's batch). -/
theorem batch_commits (ho : StrictOrder K) {ws : Batch K V} {s p p' : Root K V D}
    (hs : s.Canon) (hn : ws.Nodup) (hd : p.digest H = s.digest H)
    (hH : NoCollision H (p.HasEnc H) (s.HasEnc H)) (h : p.batch ws = some p') :
    ∃ s', s.batch ws = some s' ∧ s'.Canon ∧ applyAllMap ws s.toMap = some s'.toMap ∧
      p'.digest H = s'.digest H := by
  obtain ⟨s', e1, e2⟩ := batch_sound hH hd hs.full h
  obtain ⟨f1, f2⟩ := batch_correct ho hs hn e1
  exact ⟨s', e1, f2, f1, e2⟩

/-! ## The proof (cashew `proof(paths:)`) -/

/-- The proof is built whenever the batch succeeds: `proof()` refuses only
writes whose precondition fails. -/
theorem prove_complete (ho : StrictOrder K) {ws : Batch K V} {s : Root K V D} (hs : s.Canon)
    (hn : ws.Nodup) (h : s.batch ws ≠ none) : Root.prove H ws s ≠ none := fun hp =>
  h ((batch_fails_iff ho hs hn).2 (Root.prove_none ho hs.1 hp))

/-- The proof suffices: the batch that succeeds on the full trie succeeds on
the proof, so the stubs it leaves are never read (in particular a collapse
always finds its one remaining child resolved). -/
theorem prove_live (ho : StrictOrder K) {ws : Batch K V} {s p s' : Root K V D} (hs : s.Canon)
    (hn : ws.Nodup) (hp : Root.prove H ws s = some p) (h : s.batch ws = some s') :
    p.batch ws ≠ none :=
  Root.prove_live ho hs.1 hn hp h

/-- **The proof's scope.** On a canonical trie, the partial trie cashew's
`proof(paths:)` resolves for a batch exists whenever the batch succeeds,
commits to the same root, and the batch succeeds on it exactly when it
succeeds on the full trie, giving the same root. -/
theorem proof_scope (ho : StrictOrder K) {ws : Batch K V} {s : Root K V D} (hs : s.Canon)
    (hn : ws.Nodup) :
    (s.batch ws ≠ none → ∃ p, Root.prove H ws s = some p) ∧
    ∀ p, Root.prove H ws s = some p →
      p.digest H = s.digest H ∧ (p.batch ws ≠ none ↔ s.batch ws ≠ none) ∧
      ∀ p', p.batch ws = some p' → ∃ s', s.batch ws = some s' ∧ p'.digest H = s'.digest H := by
  refine ⟨fun h => ?_, fun p hp => ?_⟩
  · cases e : Root.prove H ws s with
    | none => exact absurd e (prove_complete ho hs hn h)
    | some p => exact ⟨p, rfl⟩
  · have hle := Root.prove_le hp
    have sound : ∀ p', p.batch ws = some p' → ∃ s', s.batch ws = some s' ∧ p'.digest H = s'.digest H :=
      fun p' h => by
        obtain ⟨s', e1, e2⟩ := Root.batch_le hle h
        exact ⟨s', e1, e2.digest⟩
    refine ⟨hle.digest, ⟨fun h => ?_, fun h => ?_⟩, sound⟩
    · cases e : p.batch ws with
      | none => exact absurd e h
      | some p' => obtain ⟨s', e1, -⟩ := sound p' e; simp [e1]
    · cases e : s.batch ws with
      | none => exact absurd e h
      | some s' => exact prove_live ho hs hn hp e

end Lattice.Merkle
