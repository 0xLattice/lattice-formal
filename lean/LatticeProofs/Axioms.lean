import LatticeProofs.Conservation
import LatticeProofs.MerkleProofs

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
