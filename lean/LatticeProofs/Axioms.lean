import LatticeProofs.Conservation
import LatticeProofs.MerkleProofs
import LatticeProofs.Swap
import LatticeProofs.WorkProofs
import LatticeProofs.KeysProofs

open Lattice in
section
#print axioms applyBlock_wf
#print axioms fee_nonneg
#print axioms spendable_with_recipient
#print axioms spendable_without_recipient
#print axioms locked_change
#print axioms value_with_recipient
#print axioms value_without_recipient
#print axioms value_chain
#print axioms withdrawal_authorized
#print axioms withdrawal_spends
#print axioms spent_is_final
#print axioms spent_persists
#print axioms deposit_fresh
#print axioms receipt_fresh
#print axioms receipt_provenance
#print axioms balances_fit
#print axioms coinbase_fits
#print axioms receipt_value_provenance
#print axioms deposit_value_provenance
#print axioms receipt_chain_provenance
#print axioms deposit_chain_provenance
#print axioms swap_atomic
#print axioms withdrawal_once
#print axioms receipt_once
#print axioms payment_releases_once
end

open Lattice.Merkle in
section
#print axioms or_collision
#print axioms lookup_sound
#print axioms lookup_sound_or_collision
#print axioms unknown_write_fails
#print axioms read_then_write_sound
#print axioms apply_sound
#print axioms apply_sound_or_collision
#print axioms apply_correct
#print axioms apply_complete
#print axioms canonical_unique
#print axioms digest_of_map
#print axioms witness_digest
#print axioms witness_live
#print axioms applyAll_sound
#print axioms applyAll_correct
#print axioms batch_eq_fold
#print axioms commits_unique
#print axioms commits_empty
#print axioms block_commits
#print axioms block_commits_or_collision
#print axioms chain_commits
#print axioms chain_from_empty
#print axioms receipts_commit
end

open Lattice.Work in
section
#print axioms workForTarget_eq
#print axioms workForTarget_zero
#print axioms workForTarget_max
#print axioms workForTarget_eq_bitcoin
#print axioms workForHash_eq
#print axioms workForHash_zero
#print axioms exclusive_between
#print axioms exclusive_at_one
#print axioms credit_per_hash_le
#print axioms credit_per_hash_ge
#print axioms exclusive_credit_exceeds
#print axioms credit_le_creditMax
#print axioms ladder_credit_le
#print axioms terminal_credit_le
#print axioms ladder_exceeds_one
#print axioms rules_differ
#print axioms harder_target_rounding
#print axioms u256_edges
end

open Lattice.Keys in
section
#print axioms hex64_inj
#print axioms decimal_inj
#print axioms decimalInt_inj
#print axioms cid_decode_encode
#print axioms cid_encode_decode
#print axioms cid_one_spelling
#print axioms cidText_valid
#print axioms joinSep_inj
#print axioms powPrefix_inj
#print axioms depositText_inj
#print axioms receiptText_inj
#print axioms receiptText_inj_of_demander
#print axioms receiptText_collision
#print axioms receiptPath_inj
#print axioms receiptPreimage_ne
#print axioms receiptPath_separated
#print axioms cid_example
#print axioms cid_padding_refused
#print axioms recipient_tag_example
end
