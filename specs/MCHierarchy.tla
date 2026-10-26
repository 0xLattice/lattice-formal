---------------------------- MODULE MCHierarchy ----------------------------
(***************************************************************************)
(* Parent chain                      Child chain                            *)
(*                                                                         *)
(*   pg (genesis)                     c0 (genesis; anchor pg, via p0)      *)
(*    |                               /  \           c5 (genesis; anchor    *)
(*   p0 (commits c0)                c2    c1             EMPTY: invalid)    *)
(*   /   \                           |     |                               *)
(* p1     p2 (heavy, 4;             c4    c3                               *)
(*  |      commits c6,                                                     *)
(* p3      never held)         c1: anchor p1 (via p3), merged grind,       *)
(*  | (commits c1)                 credited 2 in the child, 1 in parent    *)
(* p4                          c2: anchor pg (same as c0)                  *)
(*                             c3: anchor p2, SIDEWAYS from c1's p1: held  *)
(*                             c4: anchor p2, forward from c2's pg         *)
(*                             c6: committed by p2, never held             *)
(*                                                                         *)
(* Deepest carriers: p0 and p1 -> p0; p2 -> p2; p3 and p4 -> p3.  So the   *)
(* parent fork below p0 places each branch in its own carrier's run.       *)
(*   attributed(c0, p0) = 1 (p1); attributed(c1, p3) = 1 (p4);             *)
(*   p2's run is never credited, because the child never holds c6.         *)
(*                                                                         *)
(* - The parent's canonical tip is p2 while c1 anchors on the NONcanonical *)
(*   p1 branch: c1 must still validate (§9.5).                             *)
(* - c1 vs c2: own work 2 + 3 = 5 vs 4 + 1 = 5, and c2 has the smaller     *)
(*   CID.  Only c1's attributed run (1) makes c1 win.                      *)
(* - c3 is never validated and never excluded (sideways = held), so the    *)
(*   weighed descent reaches it.                                           *)
(* - c5 is excluded once c0 executes (root rule, §9.9).                    *)
(*                                                                         *)
(* Child weights (the same in EVERY model):                                *)
(*   c3 = 3, c1 = 2 + 3 + 1 = 6, c4 = 1, c2 = 4 + 1 = 5,                    *)
(*   c0 = 1 + 6 + 5 + 1 = 13, c5 = 1.                                       *)
(***************************************************************************)
EXTENDS HierarchyProps

MCPBlocks == {"pg", "p0", "p1", "p2", "p3", "p4"}
MCCBlocks == {"c0", "c1", "c2", "c3", "c4", "c5", "c6"}
MCGBlocks == {}   \* two levels; MCHierarchy3 adds a grandchild

MCParent == [x \in MCPBlocks \cup MCCBlocks |->
                CASE x = "p0" -> "pg"
                  [] x = "p1" -> "p0" [] x = "p2" -> "p0"
                  [] x = "p3" -> "p1" [] x = "p4" -> "p3"
                  [] x = "c1" -> "c0" [] x = "c2" -> "c0"
                  [] x = "c3" -> "c1" [] x = "c4" -> "c2"
                  [] x = "c6" -> "c0"
                  [] OTHER    -> "none"]

MCCidRank == [x \in MCPBlocks \cup MCCBlocks |->
                CASE x = "pg" -> 0
                  [] x = "p0" -> 1 [] x = "p1" -> 2 [] x = "p2" -> 3
                  [] x = "p3" -> 4 [] x = "p4" -> 5
                  [] x = "c0" -> 6 [] x = "c2" -> 7 [] x = "c1" -> 8
                  [] x = "c3" -> 9 [] x = "c4" -> 10 [] x = "c5" -> 11
                  [] x = "c6" -> 12]

MCGrinds == {"g_pg", "g_p0", "g_p1", "g_p2", "g_p3", "g_p4",
             "g_c2", "g_c3", "g_c4", "g_c5"}

MCObs ==
    { [ch |-> "P", g |-> "g_pg", b |-> "pg", q |-> 1],
      [ch |-> "P", g |-> "g_p0", b |-> "p0", q |-> 1],
      [ch |-> "P", g |-> "g_p1", b |-> "p1", q |-> 1],
      [ch |-> "P", g |-> "g_p2", b |-> "p2", q |-> 4],
      [ch |-> "P", g |-> "g_p3", b |-> "p3", q |-> 1],
      [ch |-> "P", g |-> "g_p4", b |-> "p4", q |-> 1],
      [ch |-> "C", g |-> "g_p0", b |-> "c0", q |-> 1],
      [ch |-> "C", g |-> "g_p3", b |-> "c1", q |-> 2],
      [ch |-> "C", g |-> "g_c2", b |-> "c2", q |-> 4],
      [ch |-> "C", g |-> "g_c3", b |-> "c3", q |-> 3],
      [ch |-> "C", g |-> "g_c4", b |-> "c4", q |-> 1],
      [ch |-> "C", g |-> "g_c5", b |-> "c5", q |-> 1] }

MCCommits == { <<"p0", "c0">>, <<"p3", "c1">>, <<"p2", "c6">> }

MCAnchor == [x \in MCCBlocks |->
                CASE x = "c0" -> "pg" [] x = "c1" -> "p1" [] x = "c2" -> "pg"
                  [] x = "c3" -> "p2" [] x = "c4" -> "p2" [] x = "c6" -> "p0"
                  [] OTHER    -> "none"]

MCExpectedChildWork == [x \in MCCBlocks |->
                CASE x = "c0" -> 13 [] x = "c1" -> 6 [] x = "c2" -> 5
                  [] x = "c3" -> 3 [] x = "c4" -> 1 [] x = "c5" -> 1
                  [] x = "c6" -> 0]

AllBlocks == MCPBlocks \cup MCCBlocks

\* Every block valid by its own transition, every body available.
MCValidAll == [x \in AllBlocks |-> TRUE]
MCAvailAll == AllBlocks
MCTipsMain ==
    [P |-> [canonical |-> "p2", validated |-> "p2"],
     C |-> [canonical |-> "c3", validated |-> "c1"],
     G |-> [canonical |-> "none", validated |-> "none"]]

\* PARENT VERDICTS: p2 and p4 are invalid.  The parent's canonical tip
\* moves to p3.  c4, anchored at the excluded p2, is held forever, not
\* excluded.  p4 stays in p3's run, so c1 keeps its attributed 1 and still
\* beats c2; nothing else in the child moves (§12.5.7, §9.10 "a run only
\* grows, including when a block in it is later excluded").
MCValidParentBad == [x \in AllBlocks |-> x \notin {"p2", "p4"}]
MCTipsParentBad ==
    [P |-> [canonical |-> "p3", validated |-> "p3"],
     C |-> [canonical |-> "c3", validated |-> "c1"],
     G |-> [canonical |-> "none", validated |-> "none"]]

\* HELD AND INVALID: c3's anchor is sideways (continuity held) and its
\* transition is invalid.  The transition failure is a verdict under any
\* continuity outcome, so c3 is excluded: the child's canonical descent
\* stops at c1.  Its work still weighs.
MCValidHeldInvalid == [x \in AllBlocks |-> x # "c3"]
MCTipsHeldInvalid ==
    [P |-> [canonical |-> "p2", validated |-> "p2"],
     C |-> [canonical |-> "c1", validated |-> "c1"],
     G |-> [canonical |-> "none", validated |-> "none"]]

MCHeaderNone == {}

\* HEADER RULES (§9.9): p3, the carrier of c1, and c3 break a header
\* validity rule, so each is excluded the moment it is weighed.  p3 and
\* its descendant p4 still weigh, and p3's run still holds p4, so c1 keeps
\* its attributed 1 and the child weights do not move.  c3 is excluded
\* rather than held, so the child's canonical descent stops at c1.
MCHeaderBadSet == {"p3", "c3"}
MCTipsHeaderBad ==
    [P |-> [canonical |-> "p2", validated |-> "p2"],
     C |-> [canonical |-> "c1", validated |-> "c1"],
     G |-> [canonical |-> "none", validated |-> "none"]]

\* PARENT AVAILABILITY: p1's body never arrives, so c1's anchor is never
\* executed: c1 is HELD (not invalid) and the child acts on c2's branch,
\* up to c4.  Child weights do not move.
MCAvailP1Gap == AllBlocks \ {"p1"}
MCTipsP1Gap ==
    [P |-> [canonical |-> "p2", validated |-> "p2"],
     C |-> [canonical |-> "c3", validated |-> "c4"],
     G |-> [canonical |-> "none", validated |-> "none"]]

=============================================================================
