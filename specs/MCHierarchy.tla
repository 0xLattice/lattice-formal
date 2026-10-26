---------------------------- MODULE MCHierarchy ----------------------------
(***************************************************************************)
(* Parent chain                    Child chain                              *)
(*                                                                         *)
(*        p0 (commits c0)                  c0  (anchor: empty)             *)
(*       /    \                           /   \                            *)
(*     p1      p2 (heavy, 4)            c2     c1 (anchor p1, via p3)      *)
(*     |                          (empty, 4)    |                          *)
(*     p3 (commits c1)                          c3 (anchor p2: SIDEWAYS)   *)
(*     |                                                                   *)
(*     p4                                                                  *)
(*                                                                         *)
(* Runs into the child directory: run(p0) = {p0, p1, p2}, run(p3) =        *)
(* {p3, p4}.  attributed(c0, p0) = 1 + 4 = 5, attributed(c1, p3) = 1.      *)
(* Merged grinds: g_p0 reaches c0, g_p3 reaches c1.                        *)
(*                                                                         *)
(* - p2 outweighs the p1 branch (4 vs 3), so the parent's canonical tip is *)
(*   p2 while c1 anchors on the NONcanonical p1 branch: it must still      *)
(*   validate (§9.5 "a noncanonical parent branch may prove the fact").    *)
(* - c1 vs c2: own work 1 + 3 (c3 still weighs) = 4 vs 4, and c2 has the   *)
(*   smaller CID.  Only c1's attributed run (1) makes c1 win.              *)
(* - c3 anchors at p2, sideways from c1's p1: excluded, still weighs.      *)
(*                                                                         *)
(* Child weights (the same in EVERY model):                                *)
(*   c3 = 3, c1 = 1 + 3 + 1 = 5, c2 = 4, c0 = 1 + 5 + 4 + 5 = 15.          *)
(***************************************************************************)
EXTENDS Hierarchy

MCPBlocks == {"p0", "p1", "p2", "p3", "p4"}
MCCBlocks == {"c0", "c1", "c2", "c3"}

MCParent == [x \in MCPBlocks \cup MCCBlocks |->
                CASE x = "p1" -> "p0" [] x = "p2" -> "p0"
                  [] x = "p3" -> "p1" [] x = "p4" -> "p3"
                  [] x = "c1" -> "c0" [] x = "c2" -> "c0"
                  [] x = "c3" -> "c1"
                  [] OTHER    -> "none"]

MCCidRank == [x \in MCPBlocks \cup MCCBlocks |->
                CASE x = "p0" -> 1 [] x = "p1" -> 2 [] x = "p2" -> 3
                  [] x = "p3" -> 4 [] x = "p4" -> 5
                  [] x = "c0" -> 6 [] x = "c2" -> 7 [] x = "c1" -> 8
                  [] x = "c3" -> 9]

MCGrinds == {"g_p0", "g_p1", "g_p2", "g_p3", "g_p4", "g_c2", "g_c3"}

MCObs ==
    { [ch |-> "P", g |-> "g_p0", b |-> "p0", q |-> 1],
      [ch |-> "P", g |-> "g_p1", b |-> "p1", q |-> 1],
      [ch |-> "P", g |-> "g_p2", b |-> "p2", q |-> 4],
      [ch |-> "P", g |-> "g_p3", b |-> "p3", q |-> 1],
      [ch |-> "P", g |-> "g_p4", b |-> "p4", q |-> 1],
      [ch |-> "C", g |-> "g_p0", b |-> "c0", q |-> 1],
      [ch |-> "C", g |-> "g_p3", b |-> "c1", q |-> 1],
      [ch |-> "C", g |-> "g_c2", b |-> "c2", q |-> 4],
      [ch |-> "C", g |-> "g_c3", b |-> "c3", q |-> 3] }

MCCommits == { <<"p0", "c0">>, <<"p3", "c1">> }

MCAnchor == [x \in MCCBlocks |->
                CASE x = "c1" -> "p1" [] x = "c3" -> "p2" [] OTHER -> "none"]

MCExpectedChildWork == [x \in MCCBlocks |->
                CASE x = "c0" -> 15 [] x = "c1" -> 5 [] x = "c2" -> 4
                  [] x = "c3" -> 3]

AllBlocks == MCPBlocks \cup MCCBlocks

\* Every block valid by its own transition, every body available.
MCValidAll == [x \in AllBlocks |-> TRUE]
MCAvailAll == AllBlocks
MCTipsMain ==
    [P |-> [canonical |-> "p2", validated |-> "p2"],
     C |-> [canonical |-> "c1", validated |-> "c1"]]

\* PARENT VERDICT: p2 is invalid.  The parent's canonical tip moves to p4;
\* the child must not notice (§12.5.7).
MCValidP2Bad == [x \in AllBlocks |-> x # "p2"]
MCTipsP2Bad ==
    [P |-> [canonical |-> "p4", validated |-> "p4"],
     C |-> [canonical |-> "c1", validated |-> "c1"]]

\* PARENT AVAILABILITY: p1's body never arrives, so c1's anchor is never
\* executed: c1 is HELD (not invalid) and the child acts on c2.  c3 is
\* never executed either, so never excluded, and the weighed descent
\* reaches it.  Child weights do not move.
MCAvailP1Gap == AllBlocks \ {"p1"}
MCTipsP1Gap ==
    [P |-> [canonical |-> "p2", validated |-> "p2"],
     C |-> [canonical |-> "c3", validated |-> "c2"]]

=============================================================================
