-------------------------- MODULE MCHierarchyFork --------------------------
(***************************************************************************)
(* Merged-mining forks at every level, each level choosing for itself.     *)
(*                                                                         *)
(*   P                  C                          G                       *)
(*   pg (genesis)       c0 (genesis; via p0,       ga (genesis; via ca2,   *)
(*    |                    merged grind)               anchor ca)          *)
(*   p0 (commits c0)    /   \                       gb (genesis; via cb,    *)
(*   /   \             ca    cb (via pb,               anchor c0)          *)
(* pa     pb          (via pa)  anchor p0)                                 *)
(*  |      |           |                                                   *)
(* pa2    pb2         ca2 (via pa2, anchor pa)                             *)
(*                                                                         *)
(* Every parent grind is 1, so pa's and pb's subtrees tie at 2 and the     *)
(* parent's tips (canonical and validated) are decided by CID alone: pa2.  *)
(* Reversing the CID order moves both to pb2, and nothing below may move.  *)
(*                                                                         *)
(* Runs: P: pa {pa}, pa2 {pa2}, pb {pb, pb2}; C: ca2, cb each alone.       *)
(* attributed(P, pa) = attributed(P, pa2) = 0, (P, pb) = 1; the C runs     *)
(* pass those on: attributed(C, ca2) = 0, (C, cb) = 1.                     *)
(*                                                                         *)
(* C: ca = 1 + ca2 (1) = 2; cb = 2 + 1 = 3: the child takes cb, the side   *)
(*    the parent did NOT choose.  c0 = 1 + 2 + 3 = 6.                       *)
(* G: a genesis fork.  ga = 3, gb = 1 + 1 = 2: the grandchild takes ga,    *)
(*    the side the child did not choose.                                   *)
(*                                                                         *)
(* Backing: ca by {pa, pa2}, cb by {pb, pb2}; ga by {ca2, pa2}, gb by      *)
(* {cb, pb, pb2}.  No work above backs both sides of either fork.          *)
(*                                                                         *)
(* ca2 anchors at pa, on one parent branch: its validity must not depend   *)
(* on which parent branch is the tip.                                      *)
(***************************************************************************)
EXTENDS HierarchyProps

FPBlocks == {"pg", "p0", "pa", "pa2", "pb", "pb2"}
FCBlocks == {"c0", "ca", "ca2", "cb"}
FGBlocks == {"ga", "gb"}
FAll == FPBlocks \cup FCBlocks \cup FGBlocks

FParent == [x \in FAll |->
               CASE x = "p0" -> "pg"
                 [] x = "pa" -> "p0" [] x = "pb" -> "p0"
                 [] x = "pa2" -> "pa" [] x = "pb2" -> "pb"
                 [] x = "ca" -> "c0" [] x = "cb" -> "c0" [] x = "ca2" -> "ca"
                 [] OTHER    -> "none"]

FCidRank == [x \in FAll |->
               CASE x = "pg" -> 0 [] x = "p0" -> 1
                 [] x = "pa" -> 2 [] x = "pa2" -> 3
                 [] x = "pb" -> 4 [] x = "pb2" -> 5
                 [] x = "c0" -> 6 [] x = "ca" -> 7 [] x = "ca2" -> 8 [] x = "cb" -> 9
                 [] x = "ga" -> 10 [] x = "gb" -> 11]

FGrinds == {"g_pg", "g_p0", "g_pa", "g_pa2", "g_pb", "g_pb2",
            "g_ca", "g_ca2", "g_cb", "g_ga", "g_gb"}

FObs ==
    { [ch |-> "P", g |-> "g_pg",  b |-> "pg",  q |-> 1],
      [ch |-> "P", g |-> "g_p0",  b |-> "p0",  q |-> 1],
      [ch |-> "P", g |-> "g_pa",  b |-> "pa",  q |-> 1],
      [ch |-> "P", g |-> "g_pa2", b |-> "pa2", q |-> 1],
      [ch |-> "P", g |-> "g_pb",  b |-> "pb",  q |-> 1],
      [ch |-> "P", g |-> "g_pb2", b |-> "pb2", q |-> 1],
      [ch |-> "C", g |-> "g_p0",  b |-> "c0",  q |-> 1],
      [ch |-> "C", g |-> "g_ca",  b |-> "ca",  q |-> 1],
      [ch |-> "C", g |-> "g_ca2", b |-> "ca2", q |-> 1],
      [ch |-> "C", g |-> "g_cb",  b |-> "cb",  q |-> 2],
      [ch |-> "G", g |-> "g_ga",  b |-> "ga",  q |-> 3],
      [ch |-> "G", g |-> "g_gb",  b |-> "gb",  q |-> 1] }

FCommits == { <<"p0", "c0">>, <<"pa", "ca">>, <<"pa2", "ca2">>, <<"pb", "cb">>,
              <<"ca2", "ga">>, <<"cb", "gb">> }

\* A committed block's anchor is its carrier's prevState (here its parent).
FAnchor == [x \in FCBlocks \cup FGBlocks |->
               CASE x = "c0" -> "pg" [] x = "ca2" -> "pa"
                 [] x = "ga" -> "ca" [] x = "gb" -> "c0"
                 [] OTHER -> "p0"]

FExpectedChildWork == [x \in FCBlocks \cup FGBlocks |->
               CASE x = "c0" -> 6 [] x = "ca" -> 2 [] x = "ca2" -> 1 [] x = "cb" -> 3
                 [] x = "ga" -> 3 [] OTHER -> 2]

FValidAll == [x \in FAll |-> TRUE]
FHeaderNone == {}
FTips ==
    [P |-> [canonical |-> "pa2", validated |-> "pa2"],
     C |-> [canonical |-> "cb",  validated |-> "cb"],
     G |-> [canonical |-> "ga",  validated |-> "ga"]]

=============================================================================
