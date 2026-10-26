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
(*   p2 (2)           c2 (anchor p2, via p3; in c1's run)                  *)
(*    |                                                                    *)
(*   p3 (commits c2)                                                       *)
(*    |                                                                    *)
(*   p4 (3)                                                                *)
(*                                                                         *)
(* g_p1 is merged across all three levels: credited 1 at p1, 2 at c1 and   *)
(* 3 at g0, so taking the wrong level's quantity shows.  Every other grind *)
(* is 1 except g_p2 = 2 and g_p4 = 3.                                      *)
(*                                                                         *)
(*   attributed(c0, p0) = runWork(p0) - grindWork(p0) = 1 - 1 = 0          *)
(*   attributed(c1, p1) = (1 + 2) - 1 = 2            (p2)                  *)
(*   attributed(c2, p3) = (1 + 3) - 1 = 3            (p4)                  *)
(*   attributed(g0, c1) = runWork(c1) - grindWork(c1)                      *)
(*                      = (2 + 2) + (1 + 3) - 2 = 6  (p2, c2, p4)          *)
(*                                                                         *)
(* Runs P attributed at c1 (the carrier) and at c2 (a non-carrier member   *)
(* of c1's run) are credited work in c1's run, so both reach G; g_p1 is    *)
(* counted once at each level, never twice.                                *)
(*                                                                         *)
(* Weights: c2 = 1 + 3 = 4, c1 = 2 + 2 + 4 = 8, c0 = 1 + 8 + 0 = 9;        *)
(*          g1 = 1, g0 = 3 + 1 + 6 = 10.                                   *)
(***************************************************************************)
EXTENDS HierarchyProps

M3PBlocks == {"pg", "p0", "p1", "p2", "p3", "p4"}
M3CBlocks == {"c0", "c1", "c2"}
M3GBlocks == {"g0", "g1"}
M3All == M3PBlocks \cup M3CBlocks \cup M3GBlocks

M3Parent == [x \in M3All |->
                CASE x = "p0" -> "pg" [] x = "p1" -> "p0" [] x = "p2" -> "p1"
                  [] x = "p3" -> "p2" [] x = "p4" -> "p3"
                  [] x = "c1" -> "c0" [] x = "c2" -> "c1"
                  [] x = "g1" -> "g0"
                  [] OTHER    -> "none"]

M3CidRank == [x \in M3All |->
                CASE x = "pg" -> 0 [] x = "p0" -> 1 [] x = "p1" -> 2 [] x = "p2" -> 3
                  [] x = "p3" -> 4 [] x = "p4" -> 5
                  [] x = "c0" -> 6 [] x = "c1" -> 7 [] x = "c2" -> 8
                  [] x = "g0" -> 9 [] OTHER -> 10]

M3Grinds == {"g_pg", "g_p0", "g_p1", "g_p2", "g_p3", "g_p4", "g_c0", "g_c2", "g_g1"}

M3Obs ==
    { [ch |-> "P", g |-> "g_pg", b |-> "pg", q |-> 1],
      [ch |-> "P", g |-> "g_p0", b |-> "p0", q |-> 1],
      [ch |-> "P", g |-> "g_p1", b |-> "p1", q |-> 1],
      [ch |-> "P", g |-> "g_p2", b |-> "p2", q |-> 2],
      [ch |-> "P", g |-> "g_p3", b |-> "p3", q |-> 1],
      [ch |-> "P", g |-> "g_p4", b |-> "p4", q |-> 3],
      [ch |-> "C", g |-> "g_c0", b |-> "c0", q |-> 1],
      [ch |-> "C", g |-> "g_p1", b |-> "c1", q |-> 2],
      [ch |-> "C", g |-> "g_c2", b |-> "c2", q |-> 1],
      [ch |-> "G", g |-> "g_p1", b |-> "g0", q |-> 3],
      [ch |-> "G", g |-> "g_g1", b |-> "g1", q |-> 1] }

M3Commits == { <<"p0", "c0">>, <<"p1", "c1">>, <<"p3", "c2">>, <<"c1", "g0">> }

M3Anchor == [x \in M3CBlocks \cup M3GBlocks |->
                CASE x = "c0" -> "pg" [] x = "c1" -> "p0" [] x = "c2" -> "p2"
                  [] OTHER    -> "c0"]

M3ExpectedWork == [x \in M3CBlocks \cup M3GBlocks |->
                CASE x = "c0" -> 9 [] x = "c1" -> 8 [] x = "c2" -> 4
                  [] x = "g0" -> 10 [] x = "g1" -> 1]

M3HeaderNone == {}

M3ValidAll == [x \in M3All |-> TRUE]
M3Tips ==
    [P |-> [canonical |-> "p4", validated |-> "p4"],
     C |-> [canonical |-> "c2", validated |-> "c2"],
     G |-> [canonical |-> "g1", validated |-> "g1"]]

=============================================================================
