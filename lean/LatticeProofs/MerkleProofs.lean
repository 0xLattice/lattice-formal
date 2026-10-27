import LatticeProofs.MerkleRoot
import LatticeProofs.Lemmas

/-!
# Merkle state commitments (spec §3.4, §6.1, §12.1)

What a block's state root commits to, for one sub-state held as cashew's
compressed radix trie. `H` is the digest of a node's encoding. A real hash
has collisions, so no theorem assumes `H` is injective. Each theorem that
compares digests instead assumes `NoCollision H A B`: no collision between
the encodings of the tries it names (for a run of writes, every trie the run
reaches). That holds unless those very tries contain a SHA-256 collision, so
breaking a theorem yields one (`or_collision` states it that way). `ho` says
the character order children are sorted by is a strict total order.

The statements below are the specification; the proofs only establish them.
-/

set_option linter.unusedSectionVars false

namespace Lattice.Merkle

variable {K V D : Type} [DecidableEq K] [LT K] [DecidableRel (α := K) (· < ·)]
  {H : Enc K V D → D}

/-- Collision extraction: a statement proved under `NoCollision H A B` holds,
or there is a collision between an encoding in `A` and one in `B`. -/
theorem or_collision {A B : Enc K V D → Prop} {P : Prop} (h : NoCollision H A B → P) :
    P ∨ ∃ e₁ e₂, A e₁ ∧ B e₂ ∧ e₁ ≠ e₂ ∧ H e₁ = H e₂ := by
  by_cases hc : ∃ e₁ e₂, A e₁ ∧ B e₂ ∧ e₁ ≠ e₂ ∧ H e₁ = H e₂
  · exact Or.inr hc
  · exact Or.inl (h fun e₁ e₂ h1 h2 he =>
      Classical.byContradiction fun hne => hc ⟨e₁, e₂, h1, h2, hne, he⟩)

/-! ## Reads (§6.1) -/

/-- A read of a partial trie that commits to the root of a fully resolved
trie: when it is not stopped by a stub, it is that trie's read. -/
theorem lookup_sound {p s : Root K V D} (hH : NoCollision H (p.HasEnc H) (s.HasEnc H))
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

/-- `lookup_sound` in extraction form: a read through a partial trie that
disagrees with the committed trie exhibits a collision between their nodes. -/
theorem lookup_sound_or_collision {p s : Root K V D} (hd : p.digest H = s.digest H)
    (hs : s.Full) (k : List K) :
    ((∀ v, p.lookup k = .found v → s.toMap k = some v) ∧
      (p.lookup k = .absent → s.toMap k = none)) ∨
    ∃ e₁ e₂, p.HasEnc H e₁ ∧ s.HasEnc H e₂ ∧ e₁ ≠ e₂ ∧ H e₁ = H e₂ :=
  or_collision fun hH => lookup_sound hH hd hs

/-- Fail closed: a write at a key whose path reaches a stub fails. -/
theorem unknown_write_fails (o : Op V) {p : Root K V D} {k : List K}
    (h : p.lookup k = .unknown) : p.apply o k = none := by
  cases hp : p.apply o k with
  | none => rfl
  | some _ => exact absurd h (Root.apply_resolved o hp)

/-- The implementation reads with `try? get`, which turns a stub into
"absent", and picks the write from that read. A write that then succeeds
read no stub, so the read it relied on was the committed value. -/
theorem read_then_write_sound (o : Op V) {p s p' : Root K V D} {k : List K}
    (hH : NoCollision H (p.HasEnc H) (s.HasEnc H)) (hd : p.digest H = s.digest H) (hs : s.Full) (h : p.apply o k = some p') :
    (p.lookup k).toOption = s.toMap k := by
  rw [Root.lookup_congr hH hs hd (Root.apply_resolved o h)]; rfl

/-! ## Writes (§6.1) -/

/-- A write that succeeds on a partial trie gives the root that the same
write gives on the fully resolved trie it commits to. -/
theorem apply_sound (o : Op V) {p s p' : Root K V D} {k : List K}
    (hH : NoCollision H (p.HasEnc H) (s.HasEnc H)) (hd : p.digest H = s.digest H)
    (hs : s.Full) (h : p.apply o k = some p') :
    ∃ s', s.apply o k = some s' ∧ p'.digest H = s'.digest H ∧ s'.Full :=
  Root.apply_congr o hH hs hd h

/-- `apply_sound` in extraction form. -/
theorem apply_sound_or_collision (o : Op V) {p s p' : Root K V D} {k : List K}
    (hd : p.digest H = s.digest H) (hs : s.Full) (h : p.apply o k = some p') :
    (∃ s', s.apply o k = some s' ∧ p'.digest H = s'.digest H ∧ s'.Full) ∨
    ∃ e₁ e₂, p.HasEnc H e₁ ∧ s.HasEnc H e₂ ∧ e₁ ≠ e₂ ∧ H e₁ = H e₂ :=
  or_collision fun hH => apply_sound o hH hd hs h

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
theorem witness_live (o : Op V) {s s' : Root K V D} {k : List K}
    (hH : NoCollision H ((s.witness H k).HasEnc H) (s.HasEnc H)) (hs : s.Full) (h : s.apply o k = some s') :
    ∃ p', (s.witness H k).apply o k = some p' ∧ p'.digest H = s'.digest H := by
  cases hw : (s.witness H k).apply o k with
  | none => exact absurd hw (Root.apply_witness o hs h)
  | some p' =>
    obtain ⟨s'', h1, h2, -⟩ := Root.apply_congr o hH hs (witness_digest k s) hw
    rw [h] at h1; cases h1
    exact ⟨p', rfl, h2⟩

/-! ## Batches -/

/-- Writes one after another on a partial trie give the root they give on
the fully resolved trie. -/
theorem applyAll_sound :
    ∀ (ws : List (List K × Op V)) {p s p' : Root K V D},
      NoCollision H (Root.RunHasEnc H ws p) (Root.RunHasEnc H ws s) →
      p.digest H = s.digest H → s.Full →
      p.applyAll ws = some p' → ∃ s', s.applyAll ws = some s' ∧ p'.digest H = s'.digest H ∧ s'.Full
  | [], p, s, p', _, hd, hs, h => by
    simp only [Root.applyAll, Option.some.injEq] at h; subst h; exact ⟨s, rfl, hd, hs⟩
  | (k, o) :: ws, p, s, p', hH, hd, hs, h => by
    simp only [Root.applyAll] at h
    cases hp : p.apply o k with
    | none => rw [hp] at h; cases h
    | some p1 =>
      rw [hp] at h
      obtain ⟨s1, e1, e2, e3⟩ :=
        apply_sound o (hH.mono (fun _ h => Or.inl h) (fun _ h => Or.inl h)) hd hs hp
      have hH1 : NoCollision H (Root.RunHasEnc H ws p1) (Root.RunHasEnc H ws s1) :=
        hH.mono (fun _ h => Or.inr ⟨p1, hp, h⟩) (fun _ h => Or.inr ⟨s1, e1, h⟩)
      obtain ⟨s', f1, f2, f3⟩ := applyAll_sound ws hH1 e2 e3 h
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

/-- One block's sub-state transition, verified against a partial trie whose
root is that of the canonical trie `s`, ends at the root of the canonical
trie of the map the writes make. -/
theorem block_commits (ho : StrictOrder K) {ws : List (List K × Op V)} {s p p' : Root K V D}
    (hs : s.Canon) (hd : p.digest H = s.digest H)
    (hH : NoCollision H (Root.RunHasEnc H ws p) (Root.RunHasEnc H ws s))
    (h : p.applyAll ws = some p') :
    ∃ s', s.applyAll ws = some s' ∧ s'.Canon ∧ applyAllMap ws s.toMap = some s'.toMap ∧
      p'.digest H = s'.digest H := by
  obtain ⟨s', e1, e2, -⟩ := applyAll_sound ws hH hd hs.full h
  obtain ⟨f1, f2⟩ := applyAll_correct ho ws hs e1
  exact ⟨s', e1, f2, f1, e2⟩

/-- `block_commits` in extraction form: a block whose verified root is not
the root of the map its writes make exhibits a collision among the tries the
validator and the honest node reach. -/
theorem block_commits_or_collision (ho : StrictOrder K) {ws : List (List K × Op V)}
    {s p p' : Root K V D} (hs : s.Canon) (hd : p.digest H = s.digest H)
    (h : p.applyAll ws = some p') :
    (∃ s', s.applyAll ws = some s' ∧ s'.Canon ∧ applyAllMap ws s.toMap = some s'.toMap ∧
      p'.digest H = s'.digest H) ∨
    ∃ e₁ e₂, Root.RunHasEnc H ws p e₁ ∧ Root.RunHasEnc H ws s e₂ ∧ e₁ ≠ e₂ ∧ H e₁ = H e₂ :=
  or_collision fun hH => block_commits ho hs hd hH h

/-- A chain of sub-state transitions: each block's writes, verified on the
partial trie the validator resolved, which must commit to the root the
previous block left (`B[i].postState == B[i+1].prevState`). -/
def Verified (H : Enc K V D → D) : D → List (Root K V D × List (List K × Op V)) → D → Prop
  | r, [], r' => r = r'
  | r, (p, ws) :: bs, r' =>
    p.digest H = r ∧ ∃ p', p.applyAll ws = some p' ∧ Verified H (p'.digest H) bs r'

/-- No collision, block by block, between the tries a validator's run reaches
and those the honest run from `s` reaches. -/
def ChainNoCollision (H : Enc K V D → D) :
    Root K V D → List (Root K V D × List (List K × Op V)) → Prop
  | _, [] => True
  | s, (p, ws) :: bs =>
    NoCollision H (Root.RunHasEnc H ws p) (Root.RunHasEnc H ws s) ∧
      ∀ s', s.applyAll ws = some s' → ChainNoCollision H s' bs

/-- The blocks' writes on the abstract map, block after block. -/
def applyBlocksMap : List (List (List K × Op V)) → (List K → Option V) → Option (List K → Option V)
  | [], m => some m
  | ws :: bs, m => do applyBlocksMap bs (← applyAllMap ws m)

/-- §12.1: from the root of a canonical trie, a verified chain ends at the
root of the canonical trie of the map its writes make. -/
theorem chain_commits (ho : StrictOrder K) :
    ∀ (bs : List (Root K V D × List (List K × Op V))) {s : Root K V D} {r' : D},
      s.Canon → ChainNoCollision H s bs → Verified H (s.digest H) bs r' →
      ∃ m', applyBlocksMap (bs.map (·.2)) s.toMap = some m' ∧ Commits H r' m'
  | [], s, r', hs, _, hv => ⟨s.toMap, rfl, s, hs, rfl, hv⟩
  | (p, ws) :: bs, s, r', hs, hH, hv => by
    obtain ⟨hd, p', hp, hv⟩ := hv
    obtain ⟨s', e1, e2, e3, e4⟩ := block_commits ho hs hd (hH.1) hp
    rw [e4] at hv
    obtain ⟨m', f1, f2⟩ := chain_commits ho bs e2 (hH.2 s' e1) hv
    exact ⟨m', by simp [applyBlocksMap, e3, f1], f2⟩

/-- §12.1 from genesis: a verified chain from the empty root ends at the
root of the canonical trie of the map its writes make, and so at the one
root any canonical trie of that map has. -/
theorem chain_from_empty (ho : StrictOrder K) {bs : List (Root K V D × List (List K × Op V))}
    {r' : D} (hH : ChainNoCollision H Root.empty bs) (hv : Verified H (Root.empty.digest H) bs r') :
    ∃ m', applyBlocksMap (bs.map (·.2)) (fun _ => none) = some m' ∧ Commits H r' m' ∧
      ∀ t : Root K V D, t.Canon → t.toMap = m' → t.digest H = r' := by
  obtain ⟨m', e1, e2⟩ := chain_commits ho bs (s := Root.empty) ⟨trivial, rfl⟩ hH hv
  have : (Root.empty : Root K V D).toMap = fun _ => none := by funext k; cases k <;> rfl
  rw [this] at e1
  exact ⟨m', e1, e2, fun t ht hm => commits_unique ho ⟨t, ht, hm, rfl⟩ e2⟩

/-! ## The receipt sub-state of the value model (§6.5) -/

/-- `enc` is injective on the keys `P` admits. The implementation's receipt
encoding is a hash, so it is injective on no infinite set; `P` is the finite
set of keys in play (`KeysProofs.receipts_commit_path`). -/
def InjOn {κ : Type} (enc : κ → List K) (P : κ → Prop) : Prop :=
  ∀ x y, P x → P y → enc x = enc y → x = y

/-- A model map read through the implementation's storage-key encoding
(`ReceiptKey.storageKey` for receipts), on the keys `P` admits: `M` holds
what `m` holds at their encodings, and nothing at any other key. -/
def Represents {κ : Type} [DecidableEq κ] (enc : κ → List K) (P : κ → Prop)
    (M : List K → Option V) (m : Lattice.Map κ V) : Prop :=
  (∀ x, P x → M (enc x) = m.get? x) ∧ ∀ k, (∀ x, P x → enc x ≠ k) → M k = none

/-- The trie writes a block's receipt actions make: an insertion each. -/
def receiptWrites (enc : ReceiptKey → List K) : List Action → List (List K × Op Address)
  | [] => []
  | .receipt w n dm amtD d :: as => (enc ⟨d, dm, amtD, n⟩, .insert w) :: receiptWrites enc as
  | _ :: as => receiptWrites enc as

/-- Every key a receipt action of `as` inserts is admitted by `P`. -/
def ReceiptKeysIn (P : ReceiptKey → Prop) (as : List Action) : Prop :=
  ∀ w n dm amtD d, Action.receipt w n dm amtD d ∈ as → P ⟨d, dm, amtD, n⟩

theorem represents_set {κ : Type} [DecidableEq κ] {enc : κ → List K} {P : κ → Prop}
    (henc : InjOn enc P) {M : List K → Option V} {m : Lattice.Map κ V}
    (h : Represents enc P M m) (x : κ) (hx : P x) (v : V) :
    Represents enc P (fun k' => if k' = enc x then some v else M k') (m.set x v) := by
  refine ⟨fun y hy => ?_, fun k hk => ?_⟩
  · rw [Map.get?_set]
    by_cases e : y = x
    · subst e; simp
    · have : enc y ≠ enc x := fun e' => e (henc y x hy hx e')
      simp [this, e, h.1 y hy]
  · have : k ≠ enc x := fun e => hk x hx e.symm
    simp [this, h.2 k hk]

theorem receipts_writes {enc : ReceiptKey → List K} {P : ReceiptKey → Prop}
    (henc : InjOn enc P) :
    ∀ (as : List Action) {M : List K → Option Address} {m m' : Lattice.Map ReceiptKey Address},
      ReceiptKeysIn P as → Represents enc P M m → applyReceipts m as = some m' →
      ∃ M', applyAllMap (receiptWrites enc as) M = some M' ∧ Represents enc P M' m'
  | [], M, m, m', _, hr, h => by
    simp only [applyReceipts, Option.some.injEq] at h; subst h; exact ⟨M, rfl, hr⟩
  | .receipt w n dm amtD d :: as, M, m, m', hP, hr, h => by
    simp only [applyReceipts] at h
    have hx : P ⟨d, dm, amtD, n⟩ := hP w n dm amtD d (List.mem_cons_self ..)
    have hP' : ReceiptKeysIn P as := fun w n dm amtD d h => hP w n dm amtD d (List.mem_cons_of_mem _ h)
    split at h
    · next hc =>
      have hM : M (enc ⟨d, dm, amtD, n⟩) = none := by rw [hr.1 _ hx]; exact hc.1
      obtain ⟨M', e1, e2⟩ := receipts_writes henc as hP' (represents_set henc hr _ hx w) h
      refine ⟨M', ?_, e2⟩
      simp only [receiptWrites, applyAllMap, Op.applyMap, hM]
      exact e1
    · cases h
  | .account _ _ :: as, M, m, m', hP, hr, h =>
    receipts_writes henc as (fun w n dm amtD d h => hP w n dm amtD d (List.mem_cons_of_mem _ h)) hr h
  | .deposit _ _ _ _ :: as, M, m, m', hP, hr, h =>
    receipts_writes henc as (fun w n dm amtD d h => hP w n dm amtD d (List.mem_cons_of_mem _ h)) hr h
  | .withdrawal _ _ _ _ _ :: as, M, m, m', hP, hr, h =>
    receipts_writes henc as (fun w n dm amtD d h => hP w n dm amtD d (List.mem_cons_of_mem _ h)) hr h

/-- §6.5, §12.1 for the receipt sub-state: if `prevState`'s receipt root is
that of a canonical trie holding the model's receipts (at the encodings of the
keys `P` admits), a block whose receipt writes verify against a partial trie of
that root leaves a root that commits to exactly the receipts `applyReceipts`
produces. The encoding need only be injective on `P`, which holds every key
the block inserts. -/
theorem receipts_commit {H : Enc K Address D → D} (ho : StrictOrder K)
    {enc : ReceiptKey → List K} {P : ReceiptKey → Prop} (henc : InjOn enc P)
    {m m' : Lattice.Map ReceiptKey Address} {as : List Action} {s p p' : Root K Address D}
    (hP : ReceiptKeysIn P as)
    (hs : s.Canon) (hr : Represents enc P s.toMap m) (hd : p.digest H = s.digest H)
    (hH : NoCollision H (Root.RunHasEnc H (receiptWrites enc as) p)
      (Root.RunHasEnc H (receiptWrites enc as) s))
    (hp : p.applyAll (receiptWrites enc as) = some p') (hm : applyReceipts m as = some m') :
    ∃ M', Commits H (p'.digest H) M' ∧ Represents enc P M' m' := by
  obtain ⟨s', -, e2, e3, e4⟩ := block_commits ho hs hd hH hp
  obtain ⟨M2, f1, f2⟩ := receipts_writes henc as hP hr hm
  rw [e3] at f1; cases f1
  exact ⟨s'.toMap, ⟨s', e2, rfl, e4.symm⟩, f2⟩

end Lattice.Merkle
