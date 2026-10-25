--------------------------------- MODULE MC ---------------------------------
(***************************************************************************)
(* Concrete models for ForkChoice.  One tree exercises every rule at once: *)
(*                                                                         *)
(*        r1 (valid)              r2 (INVALID, heaviest root)              *)
(*       /          \                                                      *)
(*   a (INVALID)   b (valid, grind ratchets 1 -> 2)                        *)
(*      |                                                                  *)
(*   c (valid)                                                             *)
(*                                                                         *)
(* - r2 outweighs r1, so it is canonical until excluded, and it can be     *)
(*   excluded only after r1 executes (the root rule of §9.9).              *)
(* - subtree(a) = subtree(b) = 2 once b's grind ratchets: an exact tie     *)
(*   that a wins on CID, but a is excluded, so b is selected.              *)
(* - c is valid but under an excluded block: never selectable, still       *)
(*   weighs for r1.                                                        *)
(***************************************************************************)
EXTENDS ForkChoice

MCBlocks == {"r1", "a", "b", "c", "r2"}

MCParent == [x \in MCBlocks |->
                CASE x = "a" -> "r1"
                  [] x = "b" -> "r1"
                  [] x = "c" -> "a"
                  [] OTHER   -> "none"]

MCCidRank == [x \in MCBlocks |->
                CASE x = "r1" -> 1 [] x = "a" -> 2 [] x = "b" -> 3
                  [] x = "c"  -> 4 [] x = "r2" -> 5]

MCValid == [x \in MCBlocks |-> x \notin {"a", "r2"}]

\* TIE model: a is valid, so subtree(a) = subtree(b) = 2 is decided by CID
\* alone: a (rank 2) beats b (rank 3), and the tip is c.
MCValidTie == [x \in MCBlocks |-> x # "r2"]

MCGrinds == {"g_r1", "g_a", "g_b", "g_c", "g_r2"}

MCObs ==
    { [g |-> "g_r1", b |-> "r1", q |-> 1],
      [g |-> "g_a",  b |-> "a",  q |-> 1],
      [g |-> "g_b",  b |-> "b",  q |-> 1],
      [g |-> "g_b",  b |-> "b",  q |-> 2],
      [g |-> "g_c",  b |-> "c",  q |-> 1],
      [g |-> "g_r2", b |-> "r2", q |-> 6] }

\* PROBE: g_b additionally observed at a second location.  Valid proofs
\* cannot produce this (a root's sparse path has one terminal per chain);
\* this model shows convergence DEPENDS on that assumption.
MCObsConflict == MCObs \cup { [g |-> "g_b", b |-> "c", q |-> 2] }

MCAvailAll == MCBlocks

\* b's body never arrives: canonical tip b, validated tip stuck at r1.
MCAvailGap == MCBlocks \ {"b"}

=============================================================================
