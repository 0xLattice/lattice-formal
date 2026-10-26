---------------------------- MODULE MCHierarchy3 ---------------------------
(***************************************************************************)
(* Three levels: Nexus -> A -> B as P -> C -> G (§9.10 "level by level").  *)
(*                                                                         *)
(*   P                C                 G                                  *)
(*   pg (genesis)     c0 (genesis;      g0 (genesis; anchor c0, via c1)    *)
(*    |                anchor pg,        |                                 *)
(*   p0 (commits c0)   via p0)          g1 (anchor c0)                     *)
(*    |                |                                                   *)
(*   p1 (commits c1)  c1 (anchor p0, via p1; commits g0)                   *)
(*    |                |                                                   *)
(*   p2 (2)           c2                                                   *)
(*                                                                         *)
(* g_p1 is merged across all three levels: at p1, at c1 and at g0, each    *)
(* credited 1.  Every other grind is 1 except g_p2 = 2.                    *)
(*                                                                         *)
(*   attributed(c0, p0) = runWork(p0) - grindWork(p0) = 1 - 1 = 0          *)
(*   attributed(c1, p1) = (1 + 2) - 1 = 2            (p2)                  *)
(*   attributed(g0, c1) = runWork(c1) - grindWork(c1)                      *)
(*                      = (1 + 2 + 1) - 1 = 3        (p2 via c1, and c2)   *)
(*                                                                         *)
(* The 2 that P attributed at c1 is credited work in c1's run, so it       *)
(* reaches G; g_p1 is counted once at each level, never twice.             *)
(*                                                                         *)
(* Weights: c2 = 1, c1 = 1 + 1 + 2 = 4, c0 = 1 + 4 + 0 = 5;                *)
(*          g1 = 1, g0 = 1 + 1 + 3 = 5.                                    *)
(***************************************************************************)
EXTENDS Hierarchy

M3PBlocks == {"pg", "p0", "p1", "p2"}
M3CBlocks == {"c0", "c1", "c2"}
M3GBlocks == {"g0", "g1"}
M3All == M3PBlocks \cup M3CBlocks \cup M3GBlocks

M3Parent == [x \in M3All |->
                CASE x = "p0" -> "pg" [] x = "p1" -> "p0" [] x = "p2" -> "p1"
                  [] x = "c1" -> "c0" [] x = "c2" -> "c1"
                  [] x = "g1" -> "g0"
                  [] OTHER    -> "none"]

M3CidRank == [x \in M3All |->
                CASE x = "pg" -> 0 [] x = "p0" -> 1 [] x = "p1" -> 2 [] x = "p2" -> 3
                  [] x = "c0" -> 4 [] x = "c1" -> 5 [] x = "c2" -> 6
                  [] x = "g0" -> 7 [] OTHER -> 8]

M3Grinds == {"g_pg", "g_p0", "g_p1", "g_p2", "g_c0", "g_c2", "g_g1"}

M3Obs ==
    { [ch |-> "P", g |-> "g_pg", b |-> "pg", q |-> 1],
      [ch |-> "P", g |-> "g_p0", b |-> "p0", q |-> 1],
      [ch |-> "P", g |-> "g_p1", b |-> "p1", q |-> 1],
      [ch |-> "P", g |-> "g_p2", b |-> "p2", q |-> 2],
      [ch |-> "C", g |-> "g_c0", b |-> "c0", q |-> 1],
      [ch |-> "C", g |-> "g_p1", b |-> "c1", q |-> 1],
      [ch |-> "C", g |-> "g_c2", b |-> "c2", q |-> 1],
      [ch |-> "G", g |-> "g_p1", b |-> "g0", q |-> 1],
      [ch |-> "G", g |-> "g_g1", b |-> "g1", q |-> 1] }

M3Commits == { <<"p0", "c0">>, <<"p1", "c1">>, <<"c1", "g0">> }

M3Anchor == [x \in M3CBlocks \cup M3GBlocks |->
                CASE x = "c0" -> "pg" [] x = "c1" -> "p0" [] x = "c2" -> "p0"
                  [] OTHER    -> "c0"]

M3ExpectedWork == [x \in M3CBlocks \cup M3GBlocks |->
                CASE x = "c0" -> 5 [] x = "c1" -> 4 [] x = "c2" -> 1
                  [] x = "g0" -> 5 [] x = "g1" -> 1]

M3ValidAll == [x \in M3All |-> TRUE]
M3Tips ==
    [P |-> [canonical |-> "p2", validated |-> "p2"],
     C |-> [canonical |-> "c2", validated |-> "c2"],
     G |-> [canonical |-> "g1", validated |-> "g1"]]

=============================================================================
