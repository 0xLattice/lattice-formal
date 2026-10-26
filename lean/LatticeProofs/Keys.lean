import LatticeProofs.Model

/-!
# Encodings that must not collide (spec §2, §3.5, §3.7, §5.4, §11.1)

The byte strings Lattice hashes or keys tries by, exactly as Lattice builds
them (all of them ASCII, so a character is a byte):

* the proof-of-work preimage prefix `powPrefix` (§5.4,
  `Block.makeProofOfWorkPreimagePrefix`);
* the `DepositKey` and `ReceiptKey` texts (§3.7, `description`);
* the receipt-state path `hex(SHA256("lattice/receipt-state/v1\0" ||
  ReceiptKey))` (§3.5, `ReceiptKey.storageKey`);
* the canonical text of a standard CID (§2, §3.1, `CIDDigest`), which is also
  the canonical address (§11.1, `CryptoUtils.isValidAddress`).

Each is injective on the values the grammar admits: two distinct values never
share an encoding. `SHA256` is an abstract `H`; as in `MerkleProofs`, no
theorem assumes it injective, only `NoCollision H A B` on the inputs at hand.
-/

namespace Lattice.Keys


abbrev Text := List Char

/-! ## Fixed-width digits -/

/-- The `w` lowest base-`b` digits of `n`, least significant first. -/
def digitsR (b : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | w + 1, n => n % b :: digitsR b w (n / b)

/-- The value of digits, least significant first. -/
def valR (b : Nat) : List Nat → Nat
  | [] => 0
  | x :: r => x + b * valR b r

/-- Fixed-width big-endian text in alphabet `a`. -/
def fixedText (a : Nat → Char) (b w n : Nat) : Text := ((digitsR b w n).reverse).map a

/-! ## Lowercase hex (§5.4 `hex(target)`, the receipt path) -/

/-- `%x` lowercase hex digit. -/
def hexDigit (d : Nat) : Char := if d < 10 then Char.ofNat (48 + d) else Char.ofNat (87 + d)

/-- `UInt256.toHexString` (`%0.16lx` four times) and `Data.hexString` of a
32-byte digest: 64 lowercase hex digits, big-endian. -/
def hex64 (n : Nat) : Text := fixedText hexDigit 16 64 n

/-! ## Decimal (§5.4 `decimal`, §3.7 `amountDemanded`, `nonce`) -/

/-- Swift's `String(n)` / `description` of an unsigned integer. -/
def decimal (n : Nat) : Text := (Nat.repr n).toList

/-- Swift's `String(n)` of an `Int64`: a leading `-` when negative. -/
def decimalInt (i : Int) : Text := (Int.repr i).toList

/-! ## The canonical CID text (§2, §3.1, §11.1) -/

/-- Multibase base32 (RFC 4648 lowercase). -/
def b32Digit (d : Nat) : Char := if d < 26 then Char.ofNat (97 + d) else Char.ofNat (24 + d)

/-- The decoder's reading of one character (`CIDDigest.init`): `a`–`z`,
`2`–`7`, nothing else. -/
def b32Val (c : Char) : Option Nat :=
  if 97 ≤ c.toNat ∧ c.toNat ≤ 122 then some (c.toNat - 97)
  else if 50 ≤ c.toNat ∧ c.toNat ≤ 55 then some (c.toNat - 24)
  else none

def decodeDigits : Text → Option (List Nat)
  | [] => some []
  | c :: cs => match b32Val c, decodeDigits cs with
    | some d, some ds => some (d :: ds)
    | _, _ => none

/-- The bytes `01 71 12 20` every standard CID begins with (CIDv1, dag-cbor,
sha2-256, 32 bytes). -/
def cidPrefix : Nat := 0x01711220

/-- The 290-bit number the 58 base32 digits spell: the 36 CID bytes, then two
zero padding bits. -/
def cidBits (d : Nat) : Nat := 4 * (cidPrefix * 2 ^ 256 + d)

/-- `CIDDigest.string` / `CIDIdentity.standardCID`: `b`, then 58 lowercase
base32 digits of the CID bytes, unpadded. The digest `d` is a 256-bit number. -/
def cidText (d : Nat) : Text := 'b' :: fixedText b32Digit 32 58 (cidBits d)

/-- `CIDDigest.init?`: the digest of a standard CID spelled canonically, and
`none` for every other text (another spelling, another CID kind, nonzero
padding bits). -/
def cidDecode : Text → Option Nat
  | [] => none
  | c :: cs =>
    if c = 'b' ∧ cs.length = 58 then
      match decodeDigits cs with
      | some ds =>
        if valR 32 ds.reverse % 4 = 0 ∧ valR 32 ds.reverse / 4 / 2 ^ 256 = cidPrefix then
          some (valR 32 ds.reverse / 4 % 2 ^ 256)
        else none
      | none => none
    else none

/-! ## The state-key grammar (§3.5) -/

/-- `isDeterministicKeyAtom`: non-empty visible ASCII. -/
def VisibleAscii (s : Text) : Prop := s ≠ [] ∧ ∀ c ∈ s, 0x21 ≤ c.toNat ∧ c.toNat ≤ 0x7e

/-- `isValidDirectoryAtom`: visible ASCII, no `/`. -/
def ValidDirectory (s : Text) : Prop := VisibleAscii s ∧ '/' ∉ s

/-- `isValidAccountAtom`: visible ASCII, no `/`. -/
def ValidAccount (s : Text) : Prop := VisibleAscii s ∧ '/' ∉ s

/-! ## Splitting at a separator -/

/-- Fields joined by a separator they cannot contain. -/
def joinSep (s : Char) : List Text → Text
  | [] => []
  | f :: fs => f ++ s :: joinSep s fs

/-! ## The proof-of-work preimage (§5.4) -/

/-- The header fields `powPrefix` reads. CID links and the recipient are their
text; numbers are numbers. -/
structure Header where
  version : Nat
  previousBlock : Option Text
  transactions : Text
  target : Nat
  nextTarget : Nat
  spec : Text
  parentState : Text
  prevState : Text
  postState : Text
  children : Text
  height : Nat
  timestamp : Int
  rewardRecipient : Option Text
  deriving DecidableEq

def sep : Char := '\x00'

/-- §5.4 `recipientField`: empty when absent, `0x01 || utf8` when present. -/
def recipientField : Option Text → Text
  | none => []
  | some r => '\x01' :: r

/-- §5.4 `powPrefix` (`Block.makeProofOfWorkPreimagePrefix`): every field
followed by `0x00`. -/
def powPrefix (B : Header) : Text :=
  joinSep sep [decimal B.version, B.previousBlock.getD [], B.transactions,
    hex64 B.target, hex64 B.nextTarget, B.spec, B.parentState, B.prevState, B.postState,
    B.children, decimal B.height, decimalInt B.timestamp, recipientField B.rewardRecipient]

/-- A standard CID link in canonical text (§3.1). -/
def StdLink (s : Text) : Prop := ∃ d, d < 2 ^ 256 ∧ cidText d = s

/-- What decoding a header guarantees (§3.1, §5.4): every link a standard CID,
both targets `U256`. The recipient is only required to hold no `0x00`, which
every canonical address satisfies (`cidText_valid`) and the empty text does
too. -/
structure Header.Valid (B : Header) : Prop where
  previousBlock : ∀ p, B.previousBlock = some p → StdLink p
  transactions : StdLink B.transactions
  spec : StdLink B.spec
  parentState : StdLink B.parentState
  prevState : StdLink B.prevState
  postState : StdLink B.postState
  children : StdLink B.children
  target : B.target < 2 ^ 256
  nextTarget : B.nextTarget < 2 ^ 256
  recipient : ∀ r, B.rewardRecipient = some r → sep ∉ r

/-! ## `DepositKey` and `ReceiptKey` (§3.7) -/

/-- `DepositKey.description`: `demander/amountDemanded/nonce`. -/
def depositText (k : DepositKey) : Text :=
  k.demander.toList ++ '/' :: (decimal k.amountDemanded ++ '/' :: decimal k.nonce)

/-- `ReceiptKey.description`: `directory/demander/amountDemanded/nonce`. -/
def receiptText (k : ReceiptKey) : Text :=
  k.directory.toList ++ '/' :: (k.demander.toList ++ '/' ::
    (decimal k.amountDemanded ++ '/' :: decimal k.nonce))

/-! ## The receipt-state path (§3.5) -/

/-- No collision between an input in `A` and one in `B` (as `Merkle.NoCollision`). -/
def NoCollision (H : Text → Nat) (A B : Text → Prop) : Prop :=
  ∀ x y, A x → B y → H x = H y → x = y

/-- `"lattice/receipt-state/v1\0"`. -/
def receiptDomain : Text := "lattice/receipt-state/v1".toList ++ ['\x00']

def receiptPreimage (k : ReceiptKey) : Text := receiptDomain ++ receiptText k

/-- `ReceiptKey.storageKey`: `hex(SHA256(domain || ReceiptKey))`. -/
def receiptPath (H : Text → Nat) (k : ReceiptKey) : Text := hex64 (H (receiptPreimage k))

/-- The receipt preimages of keys the grammar admits. -/
def ReceiptInput (x : Text) : Prop := ∃ k : ReceiptKey, ValidDirectory k.directory.toList ∧ x = receiptPreimage k

/-- The receipt keys in play for one block (`S`: the keys of `prevState`'s
receipt map and of the block's receipt actions) that meet the directory
grammar. -/
def InPlay (S : List ReceiptKey) (k : ReceiptKey) : Prop :=
  ValidDirectory k.directory.toList ∧ k ∈ S

/-- Their receipt preimages: a finite set. -/
def InPlayInput (S : List ReceiptKey) (x : Text) : Prop :=
  ∃ k, InPlay S k ∧ x = receiptPreimage k

end Lattice.Keys
