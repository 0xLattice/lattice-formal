import Std.Data.String.ToNat
import Std.Data.String.ToInt
import LatticeProofs.Keys

/-!
# Encodings that must not collide: proofs (spec §2, §3.5, §3.7, §5.4, §11.1)

The statements below are the specification of `Keys.lean`'s encodings; the
proofs only establish them.
-/

namespace Lattice.Keys

/-! ## Fixed-width digits -/

theorem valR_digitsR (b : Nat) : ∀ w n, valR b (digitsR b w n) = n % b ^ w
  | 0, n => by simp [digitsR, valR, Nat.mod_one]
  | w + 1, n => by
    simp only [digitsR, valR, valR_digitsR b w (n / b), Nat.pow_succ, Nat.mul_comm (b ^ w) b]
    exact Nat.mod_mul.symm

theorem digitsR_valR {b : Nat} (hb : 0 < b) : ∀ r : List Nat, (∀ x ∈ r, x < b) →
    digitsR b r.length (valR b r) = r
  | [], _ => rfl
  | x :: r, h => by
    have hx := h x (List.mem_cons_self ..)
    simp only [List.length_cons, digitsR, valR]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx, Nat.add_mul_div_left _ _ hb,
      Nat.div_eq_of_lt hx, Nat.zero_add,
      digitsR_valR hb r fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem digitsR_length (b : Nat) : ∀ w n, (digitsR b w n).length = w
  | 0, _ => rfl
  | w + 1, n => by simp [digitsR, digitsR_length b w]

theorem digitsR_lt {b : Nat} (hb : 0 < b) : ∀ w n, ∀ x ∈ digitsR b w n, x < b
  | 0, _, _, h => nomatch h
  | w + 1, n, x, h => by
    simp only [digitsR, List.mem_cons] at h
    rcases h with rfl | h
    · exact Nat.mod_lt _ hb
    · exact digitsR_lt hb w _ x h

/-! ## Lowercase hex (§5.4 `hex(target)`, the receipt path) -/

theorem hexDigit_inj : ∀ a < 16, ∀ b < 16, hexDigit a = hexDigit b → a = b := by decide

theorem map_inj_on {a : Nat → Char} {k : Nat} (ha : ∀ x < k, ∀ y < k, a x = a y → x = y) :
    ∀ {l l' : List Nat}, (∀ x ∈ l, x < k) → (∀ x ∈ l', x < k) → l.map a = l'.map a → l = l'
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => nomatch h
  | _ :: _, [], _, _, h => nomatch h
  | x :: l, y :: l', hl, hl', h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [ha x (hl x (List.mem_cons_self ..)) y (hl' y (List.mem_cons_self ..)) h.1,
      map_inj_on ha (fun z hz => hl z (List.mem_cons_of_mem _ hz))
        (fun z hz => hl' z (List.mem_cons_of_mem _ hz)) h.2]

theorem fixedText_inj {a : Nat → Char} {b w : Nat} (hb : 0 < b)
    (ha : ∀ x < b, ∀ y < b, a x = a y → x = y) {m n : Nat} (hm : m < b ^ w) (hn : n < b ^ w)
    (h : fixedText a b w m = fixedText a b w n) : m = n := by
  unfold fixedText at h
  have := map_inj_on ha (fun x hx => digitsR_lt hb w m x (List.mem_reverse.1 hx))
    (fun x hx => digitsR_lt hb w n x (List.mem_reverse.1 hx)) h
  have := congrArg (valR b) (List.reverse_inj.1 this)
  rwa [valR_digitsR, valR_digitsR, Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hn] at this

theorem hex64_inj {m n : Nat} (hm : m < 2 ^ 256) (hn : n < 2 ^ 256) (h : hex64 m = hex64 n) :
    m = n :=
  fixedText_inj (b := 16) (w := 64) (by decide) hexDigit_inj
    (by rwa [show (16 : Nat) ^ 64 = 2 ^ 256 by decide]) (by rwa [show (16 : Nat) ^ 64 = 2 ^ 256 by decide]) h

theorem mem_fixedText {a : Nat → Char} {b w n : Nat} {c : Char} (hb : 0 < b)
    (h : c ∈ fixedText a b w n) : ∃ x < b, c = a x := by
  unfold fixedText at h
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h
  exact ⟨x, digitsR_lt hb w n x (List.mem_reverse.1 hx), rfl⟩

/-! ## Decimal (§5.4 `decimal`, §3.7 `amountDemanded`, `nonce`) -/

theorem decimal_inj {m n : Nat} (h : decimal m = decimal n) : m = n :=
  Nat.repr_injective (String.toList_injective h)

theorem decimalInt_inj {i j : Int} (h : decimalInt i = decimalInt j) : i = j :=
  Int.repr_injective (String.toList_injective h)

theorem decimal_digit {n : Nat} {c : Char} (h : c ∈ decimal n) : c.isDigit :=
  Nat.isDigit_of_mem_toDigits (b := 10) (by decide) (by decide) (by simpa [decimal] using h)

theorem decimalInt_char {i : Int} {c : Char} (h : c ∈ decimalInt i) : c.isDigit ∨ c = '-' := by
  unfold decimalInt at h
  rw [Int.repr_eq_ite] at h
  split at h
  · exact Or.inl (decimal_digit h)
  · simp only [String.toList_append, List.mem_append] at h
    rcases h with h | h
    · right; simpa using h
    · exact Or.inl (decimal_digit h)

/-! ## The canonical CID text (§2, §3.1, §11.1) -/

theorem b32Val_digit : ∀ d < 32, b32Val (b32Digit d) = some d := by decide

theorem b32Digit_inj : ∀ a < 32, ∀ b < 32, b32Digit a = b32Digit b → a = b := by decide

theorem b32Val_some {c : Char} {d : Nat} (h : b32Val c = some d) : d < 32 ∧ b32Digit d = c := by
  unfold b32Val at h
  split at h
  · cases h
    refine ⟨by omega, ?_⟩
    simp only [b32Digit, show c.toNat - 97 < 26 by omega, ↓reduceIte,
      show 97 + (c.toNat - 97) = c.toNat by omega, Char.ofNat_toNat]
  · split at h
    · cases h
      refine ⟨by omega, ?_⟩
      simp only [b32Digit, show ¬ c.toNat - 24 < 26 by omega, ↓reduceIte,
        show 24 + (c.toNat - 24) = c.toNat by omega, Char.ofNat_toNat]
    · cases h

theorem decodeDigits_map : ∀ ds : List Nat, (∀ d ∈ ds, d < 32) →
    decodeDigits (ds.map b32Digit) = some ds
  | [], _ => rfl
  | d :: ds, h => by
    simp only [List.map_cons, decodeDigits, b32Val_digit d (h d (List.mem_cons_self ..)),
      decodeDigits_map ds fun x hx => h x (List.mem_cons_of_mem _ hx)]

theorem decodeDigits_some : ∀ {cs : Text} {ds : List Nat}, decodeDigits cs = some ds →
    (∀ d ∈ ds, d < 32) ∧ ds.map b32Digit = cs
  | [], ds, h => by cases h; exact ⟨(fun _ h => nomatch h), rfl⟩
  | c :: cs, ds, h => by
    simp only [decodeDigits] at h
    split at h
    · cases h
      rename_i d ds' hc hcs
      obtain ⟨h1, h2⟩ := decodeDigits_some hcs
      obtain ⟨h3, h4⟩ := b32Val_some hc
      refine ⟨fun x hx => ?_, by simp [h2, h4]⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · exact h3
      · exact h1 x hx
    · cases h

theorem cidBits_lt {d : Nat} (hd : d < 2 ^ 256) : cidBits d < 32 ^ 58 := by
  unfold cidBits cidPrefix; omega

/-- §2: decoding the canonical text gives back the digest. -/
theorem cid_decode_encode {d : Nat} (hd : d < 2 ^ 256) : cidDecode (cidText d) = some d := by
  have hl : ((digitsR 32 58 (cidBits d)).reverse.map b32Digit).length = 58 := by
    rw [List.length_map, List.length_reverse, digitsR_length]
  simp only [cidText, fixedText, cidDecode, hl, and_self, ↓reduceIte]
  rw [decodeDigits_map _ fun x hx => digitsR_lt (by decide) 58 _ x (List.mem_reverse.1 hx)]
  simp only [List.reverse_reverse, valR_digitsR, Nat.mod_eq_of_lt (cidBits_lt hd)]
  have h1 : cidBits d % 4 = 0 := by unfold cidBits; omega
  have h4 : cidBits d / 4 = cidPrefix * 2 ^ 256 + d := by unfold cidBits; omega
  have h5 : (cidPrefix * 2 ^ 256 + d) / 2 ^ 256 = cidPrefix := by unfold cidPrefix; omega
  have h6 : (cidPrefix * 2 ^ 256 + d) % 2 ^ 256 = d := by unfold cidPrefix; omega
  rw [h4, h5, h6]
  simp only [h1, and_self, ↓reduceIte]

/-- §2: the text a digest decodes from is its canonical text, so a CID has one
accepted spelling. -/
theorem cid_encode_decode {s : Text} {d : Nat} (h : cidDecode s = some d) :
    d < 2 ^ 256 ∧ cidText d = s := by
  cases s with
  | nil => cases h
  | cons c cs =>
    by_cases hc : c = 'b' ∧ cs.length = 58
    · obtain ⟨rfl, hl⟩ := hc
      simp only [cidDecode, hl, and_self, ↓reduceIte] at h
      cases hds : decodeDigits cs with
      | none => simp [hds] at h
      | some ds =>
        simp only [hds] at h
        by_cases hv : valR 32 ds.reverse % 4 = 0 ∧ valR 32 ds.reverse / 4 / 2 ^ 256 = cidPrefix
        · simp only [hv, and_self, ↓reduceIte, Option.some.injEq] at h
          subst h
          refine ⟨Nat.mod_lt _ (by decide), ?_⟩
          obtain ⟨hlt, hmap⟩ := decodeDigits_some hds
          have hlen : ds.reverse.length = 58 := by
            rw [List.length_reverse, ← hl, ← hmap, List.length_map]
          generalize hV : valR 32 ds.reverse = V at hv ⊢
          have hbits : cidBits (V / 4 % 2 ^ 256) = V := by
            unfold cidBits
            have := Nat.div_add_mod (V / 4) (2 ^ 256)
            rw [hv.2] at this
            have := Nat.div_add_mod V 4
            rw [hv.1] at this
            rw [Nat.mul_comm cidPrefix]; omega
          rw [cidText, fixedText, hbits, ← hV, ← hlen,
            digitsR_valR (by decide) _ fun x hx => hlt x (List.mem_reverse.1 hx),
            List.reverse_reverse, hmap]
        · simp [hv] at h
    · simp [cidDecode, hc] at h

/-- §2, §9.1: one text spelling per CID. -/
theorem cid_one_spelling {s s' : Text} {d : Nat} (h : cidDecode s = some d)
    (h' : cidDecode s' = some d) : s = s' :=
  (cid_encode_decode h).2.symm.trans (cid_encode_decode h').2

/-! ## The state-key grammar (§3.5) -/

theorem b32Digit_ascii : ∀ x < 32, 0x21 ≤ (b32Digit x).toNat ∧ (b32Digit x).toNat ≤ 0x7e ∧
    b32Digit x ≠ '/' ∧ b32Digit x ≠ '\x00' := by decide

/-- §11.1: a canonical address (`cidText`) meets the account grammar, and
contains no `0x00`. -/
theorem cidText_valid (d : Nat) : ValidAccount (cidText d) ∧ '\x00' ∉ cidText d := by
  have hc : ∀ c ∈ cidText d, 0x21 ≤ c.toNat ∧ c.toNat ≤ 0x7e ∧ c ≠ '/' ∧ c ≠ '\x00' := by
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · decide
    · obtain ⟨x, hx, rfl⟩ := mem_fixedText (by decide) hc
      exact b32Digit_ascii x hx
  exact ⟨⟨⟨List.cons_ne_nil _ _, fun c h => ⟨(hc c h).1, (hc c h).2.1⟩⟩,
    fun h => (hc '/' h).2.2.1 rfl⟩, fun h => (hc _ h).2.2.2 rfl⟩

/-! ## Splitting at a separator -/

theorem split_inj {s : Char} : ∀ {f g X Y : Text}, s ∉ f → s ∉ g →
    f ++ s :: X = g ++ s :: Y → f = g ∧ X = Y
  | [], [], _, _, _, _, h => ⟨rfl, (List.cons.inj h).2⟩
  | [], c :: g, _, _, _, hg, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.1 ▸ List.mem_cons_self ..) hg
  | c :: f, [], _, _, hf, _, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.1 ▸ List.mem_cons_self ..) hf
  | c :: f, d :: g, X, Y, hf, hg, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    have := split_inj (fun h => hf (List.mem_cons_of_mem _ h))
      (fun h => hg (List.mem_cons_of_mem _ h)) h.2
    exact ⟨by rw [h.1, this.1], this.2⟩

/-- Split at the LAST separator: `X ++ s :: f` with `s ∉ f`. -/
theorem split_inj_right {s : Char} {f g X Y : Text} (hf : s ∉ f) (hg : s ∉ g)
    (h : X ++ s :: f = Y ++ s :: g) : X = Y ∧ f = g := by
  have h' := congrArg List.reverse h
  simp only [List.reverse_append, List.reverse_cons, List.append_assoc, List.singleton_append] at h'
  have := split_inj (s := s) (by simpa using hf) (by simpa using hg) h'
  exact ⟨List.reverse_inj.1 this.2, List.reverse_inj.1 this.1⟩

theorem joinSep_inj {s : Char} : ∀ {fs gs : List Text}, (∀ f ∈ fs, s ∉ f) → (∀ g ∈ gs, s ∉ g) →
    joinSep s fs = joinSep s gs → fs = gs
  | [], [], _, _, _ => rfl
  | [], g :: gs, _, _, h => by simp [joinSep] at h
  | f :: fs, [], _, _, h => by simp [joinSep] at h
  | f :: fs, g :: gs, hf, hg, h => by
    obtain ⟨e1, e2⟩ := split_inj (hf f (List.mem_cons_self ..)) (hg g (List.mem_cons_self ..)) h
    rw [e1, joinSep_inj (fun x hx => hf x (List.mem_cons_of_mem _ hx))
      (fun x hx => hg x (List.mem_cons_of_mem _ hx)) e2]

/-! ## The proof-of-work preimage (§5.4) -/

theorem stdLink_sep {s : Text} (h : StdLink s) : sep ∉ s := by
  obtain ⟨d, -, rfl⟩ := h; exact (cidText_valid d).2

theorem hex64_sep (n : Nat) : sep ∉ hex64 n := fun h => by
  obtain ⟨x, hx, e⟩ := mem_fixedText (by decide) h
  revert e; revert x; decide

theorem decimal_sep (n : Nat) : sep ∉ decimal n := fun h => by
  have := decimal_digit h; revert this; decide

theorem decimalInt_sep (i : Int) : sep ∉ decimalInt i := fun h => by
  rcases decimalInt_char h with h | h <;> revert h <;> decide

theorem fields_sep {B : Header} (hB : B.Valid) : ∀ f ∈ [decimal B.version, B.previousBlock.getD [],
    B.transactions, hex64 B.target, hex64 B.nextTarget, B.spec, B.parentState, B.prevState,
    B.postState, B.children, decimal B.height, decimalInt B.timestamp,
    recipientField B.rewardRecipient], sep ∉ f := by
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact decimal_sep _
  · cases hp : B.previousBlock with
    | none => exact fun h => nomatch h
    | some p => exact stdLink_sep (hB.previousBlock p hp)
  · exact stdLink_sep hB.transactions
  · exact hex64_sep _
  · exact hex64_sep _
  · exact stdLink_sep hB.spec
  · exact stdLink_sep hB.parentState
  · exact stdLink_sep hB.prevState
  · exact stdLink_sep hB.postState
  · exact stdLink_sep hB.children
  · exact decimal_sep _
  · exact decimalInt_sep _
  · cases hr : B.rewardRecipient with
    | none => exact fun h => nomatch h
    | some r =>
      intro h
      rcases List.mem_cons.1 h with h | h
      · exact absurd h (by decide)
      · exact hB.recipient r hr h

theorem previousBlock_inj {p q : Option Text} (hp : ∀ x, p = some x → StdLink x)
    (hq : ∀ x, q = some x → StdLink x) (h : p.getD [] = q.getD []) : p = q := by
  have ne : ∀ x, StdLink x → x ≠ [] := by
    rintro x ⟨d, -, rfl⟩; exact List.cons_ne_nil _ _
  cases p <;> cases q
  · rfl
  · next x => exact absurd h.symm (ne x (hq x rfl))
  · next x => exact absurd h (ne x (hp x rfl))
  · next x y => exact congrArg some h

theorem recipientField_inj {r r' : Option Text} (h : recipientField r = recipientField r') :
    r = r' := by
  cases r <;> cases r' <;> simp_all [recipientField]

/-- §5.4: two structurally valid headers with the same `powPrefix` are the
same header: distinct field tuples never share a preimage, so one grind
secures one header. Absent and present-empty recipients differ by the `0x01`
tag. -/
theorem powPrefix_inj {B B' : Header} (hB : B.Valid) (hB' : B'.Valid)
    (h : powPrefix B = powPrefix B') : B = B' := by
  have := joinSep_inj (fields_sep hB) (fields_sep hB') h
  simp only [List.cons.injEq, and_true] at this
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13⟩ := this
  cases B; cases B'
  simp only [Header.mk.injEq]
  exact ⟨decimal_inj e1, previousBlock_inj hB.previousBlock hB'.previousBlock e2, e3,
    hex64_inj hB.target hB'.target e4, hex64_inj hB.nextTarget hB'.nextTarget e5, e6, e7, e8, e9,
    e10, decimal_inj e11, decimalInt_inj e12, recipientField_inj e13⟩

/-! ## `DepositKey` and `ReceiptKey` (§3.7) -/

theorem decimal_slash (n : Nat) : '/' ∉ decimal n := fun h => by
  have := decimal_digit h; revert this; decide

theorem amountNonce_inj {X Y : Text} {a n a' n' : Nat}
    (h : X ++ '/' :: (decimal a ++ '/' :: decimal n) = Y ++ '/' :: (decimal a' ++ '/' :: decimal n')) :
    X = Y ∧ a = a' ∧ n = n' := by
  have h' : (X ++ '/' :: decimal a) ++ '/' :: decimal n = (Y ++ '/' :: decimal a') ++ '/' :: decimal n' := by
    simpa using h
  obtain ⟨e1, e2⟩ := split_inj_right (decimal_slash n) (decimal_slash n') h'
  obtain ⟨e3, e4⟩ := split_inj_right (decimal_slash a) (decimal_slash a') e1
  exact ⟨e3, decimal_inj e4, decimal_inj e2⟩

/-- §3.7: the `DepositKey` text is injective for every demander: the two
trailing fields are decimal and hold no `/`. -/
theorem depositText_inj {k k' : DepositKey} (h : depositText k = depositText k') : k = k' := by
  obtain ⟨e1, e2, e3⟩ := amountNonce_inj h
  cases k; cases k'
  simp only [DepositKey.mk.injEq]
  exact ⟨String.toList_injective e1, e2, e3⟩

/-- §3.5, §3.7: the `ReceiptKey` text is injective on keys whose directory
meets the directory grammar (no `/`), whatever the demander. -/
theorem receiptText_inj {k k' : ReceiptKey} (hk : ValidDirectory k.directory.toList)
    (hk' : ValidDirectory k'.directory.toList) (h : receiptText k = receiptText k') : k = k' := by
  obtain ⟨e1, e2⟩ := split_inj hk.2 hk'.2 h
  obtain ⟨e3, e4, e5⟩ := amountNonce_inj e2
  cases k; cases k'
  simp only [ReceiptKey.mk.injEq]
  exact ⟨String.toList_injective e1, String.toList_injective e3, e4, e5⟩

/-- The account grammar alone also suffices: with a `/`-free demander the
directory may hold `/`. -/
theorem receiptText_inj_of_demander {k k' : ReceiptKey} (hk : ValidAccount k.demander.toList)
    (hk' : ValidAccount k'.demander.toList) (h : receiptText k = receiptText k') : k = k' := by
  obtain ⟨e1, e2, e3⟩ := amountNonce_inj (X := k.directory.toList ++ '/' :: k.demander.toList)
    (Y := k'.directory.toList ++ '/' :: k'.demander.toList) (by simpa [receiptText] using h)
  obtain ⟨e4, e5⟩ := split_inj_right hk.2 hk'.2 e1
  cases k; cases k'
  simp only [ReceiptKey.mk.injEq]
  exact ⟨String.toList_injective e4, String.toList_injective e5, e2, e3⟩

/-- Without either ban two keys collide: one `/` moves between directory and
demander. -/
theorem receiptText_collision :
    receiptText ⟨"a/b", "c", 1, 2⟩ = receiptText ⟨"a", "b/c", 1, 2⟩ ∧
      (⟨"a/b", "c", 1, 2⟩ : ReceiptKey) ≠ ⟨"a", "b/c", 1, 2⟩ := by
  decide

/-! ## The receipt-state path (§3.5) -/

/-- §3.5: on grammar-valid keys the receipt path is injective, unless `H`
(256-bit) collides on two receipt preimages. -/
theorem receiptPath_inj {H : Text → Nat} (hw : ∀ x, H x < 2 ^ 256)
    (hH : NoCollision H ReceiptInput ReceiptInput) {k k' : ReceiptKey}
    (hk : ValidDirectory k.directory.toList) (hk' : ValidDirectory k'.directory.toList)
    (h : receiptPath H k = receiptPath H k') : k = k' := by
  have := hH _ _ ⟨k, hk, rfl⟩ ⟨k', hk', rfl⟩ (hex64_inj (hw _) (hw _) h)
  simp only [receiptPreimage, List.append_cancel_left_eq] at this
  exact receiptText_inj hk hk' this

/-- §3.5, domain separation: no receipt preimage is visible-ASCII text, so
none is any state key or key text (each of which the grammar keeps
visible ASCII); the `0x00` in the domain is what does it. -/
theorem receiptPreimage_ne {k : ReceiptKey} {s : Text} (hs : VisibleAscii s) :
    receiptPreimage k ≠ s := by
  intro h
  have : '\x00' ∈ receiptPreimage k := by simp [receiptPreimage, receiptDomain]
  rw [h] at this
  have := hs.2 _ this
  revert this; decide

/-- Hence a receipt path is never the hash of a visible-ASCII text, unless `H`
collides between the two. -/
theorem receiptPath_separated {H : Text → Nat} (hw : ∀ x, H x < 2 ^ 256)
    (hH : NoCollision H ReceiptInput VisibleAscii) {k : ReceiptKey}
    (hk : ValidDirectory k.directory.toList) {s : Text} (hs : VisibleAscii s) :
    receiptPath H k ≠ hex64 (H s) := fun h =>
  receiptPreimage_ne hs (hH _ _ ⟨k, hk, rfl⟩ hs (hex64_inj (hw _) (hw _) h))

/-! ## Non-vacuity -/

/-- The canonical text of digest `0` is the familiar `bafyrei…` spelling,
and it decodes. -/
theorem cid_example : (cidText 0).take 7 = "bafyrei".toList ∧ cidDecode (cidText 0) = some 0 := by
  decide

/-- A second spelling of the same CID (a nonzero padding bit in the last
digit) is refused. -/
theorem cid_padding_refused :
    cidDecode ((cidText 0).dropLast ++ [b32Digit ((cidText 0).getLast!.toNat - 97 + 1)]) = none := by
  decide

/-- Two valid headers differing only in an absent versus a present-empty
recipient have different preimages. -/
theorem recipient_tag_example (B : Header) :
    powPrefix { B with rewardRecipient := none } ≠ powPrefix { B with rewardRecipient := some [] } := by
  intro h
  have := congrArg List.reverse h
  simp [powPrefix, joinSep, recipientField] at this


end Lattice.Keys
