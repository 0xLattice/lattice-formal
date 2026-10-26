import LatticeProofs.MerkleRoot
import LatticeProofs.Lemmas

/-!
# Merkle state commitments (spec §3.4, §6.1, §12.1)

What a block's state root commits to, for one sub-state held as cashew's
compressed radix trie. `H` is the digest of a node's encoding; every theorem
that compares digests assumes it is injective (collision resistance). `ho`
says the character order children are sorted by is a strict total order.

The statements below are the specification; the proofs only establish them.
-/

set_option linter.unusedSectionVars false

namespace Lattice.Merkle

variable {K V D : Type} [DecidableEq K] [LT K] [DecidableRel (α := K) (· < ·)]
  {H : Enc K V D → D}

/-! ## Reads (§6.1) -/

/-- A read of a partial trie that commits to the root of a fully resolved
trie: when it is not stopped by a stub, it is that trie's read. -/
theorem lookup_sound (hH : Function.Injective H) {p s : Root K V D}
    (hd : p.digest H = s.digest H) (hs : s.Full) {k : List K} :
    (∀ v, p.lookup k = .found v → s.toMap k = some v) ∧
    (p.lookup k = .absent → s.toMap k = none) := by
  constructor
  · intro v h
    have := Root.lookup_congr hH hs hd (k := k) (by simp [h])
    simp [Root.toMap, ← this, h, Read.toOption]
  · intro h
    have := Root.lookup_congr hH hs hd (k := k) (by simp [h])
    simp [Root.toMap, ← this, h, Read.toOption]

/-- Fail closed: a write at a key whose path reaches a stub fails. -/
theorem unknown_write_fails (o : Op V) {p : Root K V D} {k : List K}
    (h : p.lookup k = .unknown) : p.apply o k = none := by
  cases hp : p.apply o k with
  | none => rfl
  | some _ => exact absurd h (Root.apply_resolved o hp)

/-- The implementation reads with `try? get`, which turns a stub into
"absent", and picks the write from that read. A write that then succeeds
read no stub, so the read it relied on was the committed value. -/
theorem read_then_write_sound (hH : Function.Injective H) (o : Op V) {p s p' : Root K V D}
    {k : List K} (hd : p.digest H = s.digest H) (hs : s.Full) (h : p.apply o k = some p') :
    (p.lookup k).toOption = s.toMap k := by
  rw [Root.lookup_congr hH hs hd (Root.apply_resolved o h)]; rfl

/-! ## Writes (§6.1) -/

/-- A write that succeeds on a partial trie gives the root that the same
write gives on the fully resolved trie it commits to. -/
theorem apply_sound (hH : Function.Injective H) (o : Op V) {p s p' : Root K V D}
    {k : List K} (hd : p.digest H = s.digest H) (hs : s.Full) (h : p.apply o k = some p') :
    ∃ s', s.apply o k = some s' ∧ p'.digest H = s'.digest H ∧ s'.Full :=
  Root.apply_congr hH o hs hd h

theorem Op.applyMap_of_pre {o : Op V} {k : List K} {m : List K → Option V} (h : o.pre (m k)) :
    o.applyMap k m = some fun k' => if k' = k then o.post else m k' := by
  cases o <;> cases hm : m k <;> simp_all [Op.pre, Op.applyMap]

theorem Op.pre_of_applyMap {o : Op V} {k : List K} {m : List K → Option V}
    (h : o.applyMap k m ≠ none) : o.pre (m k) := by
  cases o <;> cases hm : m k <;> simp_all [Op.pre, Op.applyMap]

theorem Root.lookup_eq_ofOption {s : Root K V D} (hs : s.Full) (k : List K) :
    s.lookup k = .ofOption (s.toMap k) := by
  have := Root.lookup_full hs k
  simp only [Root.toMap]
  cases h : s.lookup k <;> simp_all [Read.ofOption, Read.toOption]

theorem Root.Canon.full {s : Root K V D} (hs : s.Canon) : s.Full := Kids.Canon.full hs.1

/-- On a canonical trie, a write does to the map exactly what it says
(precondition included), and the trie stays canonical, `count` included. -/
theorem apply_correct (ho : StrictOrder K) (o : Op V) {s s' : Root K V D} {k : List K}
    (hs : s.Canon) (h : s.apply o k = some s') :
    o.applyMap k s.toMap = some s'.toMap ∧ s'.Canon := by
  obtain ⟨hpre, hl, hc⟩ := Root.apply_correct ho o hs h
  refine ⟨?_, hc⟩
  rw [Op.applyMap_of_pre hpre]
  congr 1
  funext k'
  simp only [Root.toMap, hl k']
  split <;> simp

/-- Completeness: on a canonical trie, a write at a nonempty key whose
precondition holds on the map succeeds. -/
theorem apply_complete (ho : StrictOrder K) (o : Op V) {s : Root K V D} {k : List K}
    (hs : s.Canon) (hk : k ≠ []) (hm : o.applyMap k s.toMap ≠ none) :
    ∃ s', s.apply o k = some s' := by
  have := Root.apply_complete ho o hs hk (Op.pre_of_applyMap hm)
  cases h : s.apply o k with
  | none => exact absurd h this
  | some s' => exact ⟨s', rfl⟩

/-! ## The root is a function of the map -/

/-- Two canonical tries that hold the same map are the same trie. -/
theorem canonical_unique (ho : StrictOrder K) {s₁ s₂ : Root K V D} (h₁ : s₁.Canon)
    (h₂ : s₂.Canon) (hm : s₁.toMap = s₂.toMap) : s₁ = s₂ :=
  Root.canon_unique ho h₁ h₂ fun k => by
    rw [Root.lookup_eq_ofOption h₁.full, Root.lookup_eq_ofOption h₂.full, hm]

/-- Hence their roots are equal: the root depends on the map, not on the
history of writes that built it. -/
theorem digest_of_map (ho : StrictOrder K) {s₁ s₂ : Root K V D} (h₁ : s₁.Canon)
    (h₂ : s₂.Canon) (hm : s₁.toMap = s₂.toMap) : s₁.digest H = s₂.digest H := by
  rw [canonical_unique ho h₁ h₂ hm]

/-! ## Liveness: the path suffices -/

/-- The partial trie that resolves only a write's path (and the nodes of the
children along it) commits to the same root. -/
theorem witness_digest (k : List K) (s : Root K V D) : (s.witness H k).digest H = s.digest H :=
  Root.digest_witness k s

/-- A write that succeeds on the fully resolved trie succeeds on that partial
trie, with the same root. -/
theorem witness_live (hH : Function.Injective H) (o : Op V) {s s' : Root K V D} {k : List K}
    (hs : s.Full) (h : s.apply o k = some s') :
    ∃ p', (s.witness H k).apply o k = some p' ∧ p'.digest H = s'.digest H := by
  cases hw : (s.witness H k).apply o k with
  | none => exact absurd hw (Root.apply_witness o hs h)
  | some p' =>
    obtain ⟨s'', h1, h2, -⟩ := Root.apply_congr hH o hs (witness_digest k s) hw
    rw [h] at h1; cases h1
    exact ⟨p', rfl, h2⟩

/-! ## Batches -/

/-- Writes one after another on a partial trie give the root they give on
the fully resolved trie. -/
theorem applyAll_sound (hH : Function.Injective H) :
    ∀ (ws : List (List K × Op V)) {p s p' : Root K V D}, p.digest H = s.digest H → s.Full →
      p.applyAll ws = some p' → ∃ s', s.applyAll ws = some s' ∧ p'.digest H = s'.digest H ∧ s'.Full
  | [], p, s, p', hd, hs, h => by
    simp only [Root.applyAll, Option.some.injEq] at h; subst h; exact ⟨s, rfl, hd, hs⟩
  | (k, o) :: ws, p, s, p', hd, hs, h => by
    simp only [Root.applyAll] at h
    cases hp : p.apply o k with
    | none => rw [hp] at h; cases h
    | some p1 =>
      rw [hp] at h
      obtain ⟨s1, e1, e2, e3⟩ := apply_sound hH o hd hs hp
      obtain ⟨s', f1, f2, f3⟩ := applyAll_sound hH ws e2 e3 h
      exact ⟨s', by simp [Root.applyAll, e1, f1], f2, f3⟩

/-- Writes one after another on a canonical trie do to the map what they say,
and keep it canonical. -/
theorem applyAll_correct (ho : StrictOrder K) :
    ∀ (ws : List (List K × Op V)) {s s' : Root K V D}, s.Canon → s.applyAll ws = some s' →
      applyAllMap ws s.toMap = some s'.toMap ∧ s'.Canon
  | [], s, s', hs, h => by
    simp only [Root.applyAll, Option.some.injEq] at h; subst h; exact ⟨rfl, hs⟩
  | (k, o) :: ws, s, s', hs, h => by
    simp only [Root.applyAll] at h
    cases hp : s.apply o k with
    | none => rw [hp] at h; cases h
    | some s1 =>
      rw [hp] at h
      obtain ⟨e1, e2⟩ := apply_correct ho o hs hp
      obtain ⟨f1, f2⟩ := applyAll_correct ho ws e2 h
      exact ⟨by simp [applyAllMap, e1, f1], f2⟩

/-- A batch transform (cashew applies a block's writes to a sub-state in one
pass) gives the sequential result whenever its output is canonical and holds
the map the writes make: there is only one such trie. -/
theorem batch_eq_fold (ho : StrictOrder K) {ws : List (List K × Op V)} {s s' b : Root K V D}
    (hs : s.Canon) (h : s.applyAll ws = some s') (hb : b.Canon)
    (hm : applyAllMap ws s.toMap = some b.toMap) : b = s' := by
  obtain ⟨e1, e2⟩ := applyAll_correct ho ws hs h
  rw [e1] at hm
  exact canonical_unique ho hb e2 (Option.some.inj hm).symm

/-! ## State continuity (§12.1) -/

/-- Root `r` commits to map `m`: a canonical trie holds exactly `m` and has
root `r`. -/
def Commits (H : Enc K V D → D) (r : D) (m : List K → Option V) : Prop :=
  ∃ s : Root K V D, s.Canon ∧ s.toMap = m ∧ s.digest H = r

/-- The map fixes the root it is committed by. -/
theorem commits_unique (ho : StrictOrder K) {r r' : D} {m : List K → Option V}
    (h : Commits H r m) (h' : Commits H r' m) : r = r' := by
  obtain ⟨s, hs, hm, rfl⟩ := h
  obtain ⟨s', hs', hm', rfl⟩ := h'
  exact digest_of_map ho hs hs' (hm.trans hm'.symm)

/-- The empty root commits to the empty map. -/
theorem commits_empty : Commits H ((Root.empty : Root K V D).digest H) fun _ => none := by
  refine ⟨Root.empty, ⟨trivial, rfl⟩, ?_, rfl⟩
  funext k
  cases k <;> rfl

/-- One block's sub-state transition, verified against a partial trie that
commits to the previous root, commits to the map its writes make. -/
theorem block_commits (hH : Function.Injective H) (ho : StrictOrder K) {r : D}
    {m : List K → Option V} {ws : List (List K × Op V)} {p p' : Root K V D}
    (hc : Commits H r m) (hd : p.digest H = r) (h : p.applyAll ws = some p') :
    ∃ m', applyAllMap ws m = some m' ∧ Commits H (p'.digest H) m' := by
  obtain ⟨s, hs, rfl, rfl⟩ := hc
  obtain ⟨s', e1, e2, -⟩ := applyAll_sound hH ws hd hs.full h
  obtain ⟨f1, f2⟩ := applyAll_correct ho ws hs e1
  exact ⟨s'.toMap, f1, s', f2, rfl, e2.symm⟩

/-- A chain of sub-state transitions, each verified by a partial trie that
commits to the root the previous one left (`B[i].postState ==
B[i+1].prevState`). -/
inductive Verified (H : Enc K V D → D) : D → List (List (List K × Op V)) → D → Prop
  | nil (r : D) : Verified H r [] r
  | cons {r : D} {ws : List (List K × Op V)} {bs : List (List (List K × Op V))} {r' : D}
      (p p' : Root K V D) : p.digest H = r → p.applyAll ws = some p' →
      Verified H (p'.digest H) bs r' → Verified H r (ws :: bs) r'

/-- The blocks' writes on the abstract map, block after block. -/
def applyBlocksMap : List (List (List K × Op V)) → (List K → Option V) → Option (List K → Option V)
  | [], m => some m
  | ws :: bs, m => do applyBlocksMap bs (← applyAllMap ws m)

/-- §12.1: from a root committing to a map, a verified chain ends at the root
of the canonical trie of the map its writes make. -/
theorem chain_commits (hH : Function.Injective H) (ho : StrictOrder K) :
    ∀ {r r' : D} {bs : List (List (List K × Op V))} {m : List K → Option V},
      Commits H r m → Verified H r bs r' →
      ∃ m', applyBlocksMap bs m = some m' ∧ Commits H r' m'
  | _, _, _, m, hc, .nil _ => ⟨m, rfl, hc⟩
  | _, _, _, _, hc, .cons p p' hd ha hv => by
    obtain ⟨m1, e1, e2⟩ := block_commits hH ho hc hd ha
    obtain ⟨m', f1, f2⟩ := chain_commits hH ho e2 hv
    exact ⟨m', by simp [applyBlocksMap, e1, f1], f2⟩

/-! ## The receipt sub-state of the value model (§6.5) -/

/-- A model map read through the implementation's storage-key encoding
(`ReceiptKey.storageKey` for receipts): `M` holds what `m` holds, at encoded
keys, and nothing else. -/
def Represents {κ : Type} [DecidableEq κ] (enc : κ → List K) (M : List K → Option V)
    (m : Lattice.Map κ V) : Prop :=
  (∀ x, M (enc x) = m.get? x) ∧ ∀ k, (∀ x, enc x ≠ k) → M k = none

/-- The trie writes a block's receipt actions make: an insertion each. -/
def receiptWrites (enc : ReceiptKey → List K) : List Action → List (List K × Op Address)
  | [] => []
  | .receipt w n dm amtD d :: as => (enc ⟨d, dm, amtD, n⟩, .insert w) :: receiptWrites enc as
  | _ :: as => receiptWrites enc as

theorem represents_set {κ : Type} [DecidableEq κ] {enc : κ → List K}
    (henc : Function.Injective enc) {M : List K → Option V} {m : Lattice.Map κ V}
    (h : Represents enc M m) (x : κ) (v : V) :
    Represents enc (fun k' => if k' = enc x then some v else M k') (m.set x v) := by
  refine ⟨fun y => ?_, fun k hk => ?_⟩
  · rw [Map.get?_set]
    by_cases hy : y = x
    · subst hy; simp
    · have : enc y ≠ enc x := fun e => hy (henc e)
      simp [this, hy, h.1 y]
  · have : k ≠ enc x := fun e => hk x e.symm
    simp [this, h.2 k hk]

theorem receipts_writes {enc : ReceiptKey → List K} (henc : Function.Injective enc) :
    ∀ (as : List Action) {M : List K → Option Address} {m m' : Lattice.Map ReceiptKey Address},
      Represents enc M m → applyReceipts m as = some m' →
      ∃ M', applyAllMap (receiptWrites enc as) M = some M' ∧ Represents enc M' m'
  | [], M, m, m', hr, h => by
    simp only [applyReceipts, Option.some.injEq] at h; subst h; exact ⟨M, rfl, hr⟩
  | .receipt w n dm amtD d :: as, M, m, m', hr, h => by
    simp only [applyReceipts] at h
    split at h
    · next hc =>
      have hM : M (enc ⟨d, dm, amtD, n⟩) = none := by rw [hr.1]; exact hc.1
      obtain ⟨M', e1, e2⟩ := receipts_writes henc as (represents_set henc hr _ w) h
      refine ⟨M', ?_, e2⟩
      simp only [receiptWrites, applyAllMap, Op.applyMap, hM]
      exact e1
    · cases h
  | .account _ _ :: as, M, m, m', hr, h => receipts_writes henc as hr h
  | .deposit _ _ _ _ :: as, M, m, m', hr, h => receipts_writes henc as hr h
  | .withdrawal _ _ _ _ _ :: as, M, m, m', hr, h => receipts_writes henc as hr h

/-- §6.5, §12.1 for the receipt sub-state: if `prevState`'s receipt root
commits to the model's receipts, a block whose receipt writes verify against
a partial trie of that root leaves a root that commits to exactly the
receipts `applyReceipts` produces. -/
theorem receipts_commit {H : Enc K Address D → D} (hH : Function.Injective H)
    (ho : StrictOrder K) {enc : ReceiptKey → List K} (henc : Function.Injective enc) {r : D}
    {M : List K → Option Address} {m m' : Lattice.Map ReceiptKey Address} {as : List Action}
    {p p' : Root K Address D} (hc : Commits H r M) (hr : Represents enc M m) (hd : p.digest H = r)
    (hp : p.applyAll (receiptWrites enc as) = some p') (hm : applyReceipts m as = some m') :
    ∃ M', Commits H (p'.digest H) M' ∧ Represents enc M' m' := by
  obtain ⟨M1, e1, e2⟩ := block_commits hH ho hc hd hp
  obtain ⟨M2, f1, f2⟩ := receipts_writes henc as hr hm
  rw [e1] at f1; cases f1
  exact ⟨M1, e2, f2⟩

end Lattice.Merkle
