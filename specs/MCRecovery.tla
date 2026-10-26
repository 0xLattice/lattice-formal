---------------------------- MODULE MCRecovery -----------------------------
(***************************************************************************)
(* One chain, three blocks:                                                *)
(*                                                                         *)
(*        r (genesis, executed at bootstrap)                               *)
(*       / \                                                               *)
(*      a   b                                                              *)
(*                                                                         *)
(* Candidate batches, and what each does to the canonical tip:             *)
(*   Gen   block r, grind g_r = 1, validated            tip r              *)
(*   A     block a, grind g_a = 1                       tip a (1 vs 0)     *)
(*   AConf block a with different metadata: the store refuses it           *)
(*   B     block b, grind g_b = 2                       tip b (2 vs 1)     *)
(*   W1    grind g_x located at a, quantity 1           a = b = 2: tie,    *)
(*                                                      a (smaller CID)    *)
(*   W2    the same grind at a, strengthened to 2       tip a (3 vs 2)     *)
(*   Xa    exclusion of a                               tip b              *)
(*   Vb    validation of b                              validated tip b    *)
(*                                                                         *)
(* Re-resolving W1 after durability would find the stronger W2 (Rebuild).  *)
(***************************************************************************)
EXTENDS Recovery

MCBlocks == {"r", "a", "b"}

MCParent == [x \in MCBlocks |-> IF x = "r" THEN "none" ELSE "r"]

MCCidRank == [x \in MCBlocks |-> CASE x = "r" -> 1 [] x = "a" -> 2 [] OTHER -> 3]

MCGrinds == {"g_r", "g_a", "g_b", "g_x"}

Blk(b, m, g, q, v) == [k |-> "block", b |-> b, m |-> m, g |-> g, q |-> q, v |-> v]
Wrk(b, g, q)       == [k |-> "work",  b |-> b, m |-> "none", g |-> g, q |-> q, v |-> FALSE]
Fact(k, b)         == [k |-> k,       b |-> b, m |-> "none", g |-> "none", q |-> 0, v |-> FALSE]

MCGen   == Blk("r", "m1", "g_r", 1, TRUE)
MCA     == Blk("a", "m1", "g_a", 1, FALSE)
MCAConf == Blk("a", "m2", "g_a", 1, FALSE)
MCB     == Blk("b", "m1", "g_b", 2, FALSE)
MCW1    == Wrk("a", "g_x", 1)
MCW2    == Wrk("a", "g_x", 2)
MCXa    == Fact("excl", "a")
MCVb    == Fact("valid", "b")

MCBatches == {MCGen, MCA, MCAConf, MCB, MCW1, MCW2, MCXa, MCVb}

MCRebuild == [x \in MCBatches |-> IF x = MCW1 THEN MCW2 ELSE x]

\* PROBE (MCRecovery_RevisionProbe.cfg): grind g_x is strengthened at a
\* (W1, W2), then a's deferred validation is staged as a block batch that
\* re-states the strongest grind it holds (ChainTree.connectJob), here g_x
\* at 2.  Live, that batch is a duplicate; replay sorts block batches
\* before work batches, so it lands g_x at 2 in one step and W1, W2 replay
\* as duplicates: one mutation fewer than live import counted.
MCAV == Blk("a", "m1", "g_x", 2, TRUE)
MCBatchesRestate == {MCGen, MCA, MCW1, MCW2, MCAV}
MCRebuildRestate == [x \in MCBatchesRestate |-> x]

=============================================================================
