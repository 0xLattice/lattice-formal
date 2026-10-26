-------------------------- MODULE MCHierarchyFork --------------------------
(***************************************************************************)
(* A merged-mining fork: the parent forks, and each side carries its own   *)
(* child block, so the child forks with parent work behind both sides.     *)
(*                                                                         *)
(* Parent chain                       Child chain                          *)
(*                                                                         *)
(*   pg (genesis)                       c0 (genesis; via p0, merged grind) *)
(*    |                                /  \                                *)
(*   p0 (commits c0)                 ca    cb                              *)
(*   /   \                                                                 *)
(* pa     pb        pa commits ca: run {pa, pa2}, attributed 1             *)
(*  |      |        pb commits cb: run {pb, pb2, pb3}, attributed 2        *)
(* pa2    pb2                                                              *)
(*         |                                                               *)
(*        pb3                                                              *)
(*                                                                         *)
(* - The parent's canonical tip is pb3 (3 vs 2), yet the child chooses ca: *)
(*   ca = 3 + 1 = 4 beats cb = 1 + 2 = 3.  Parent canonicity does not pick *)
(*   the child's branch (§12.5.7); the work committed to each side does.   *)
(* - ca is backed by {pa, pa2} and cb by {pb, pb2, pb3}: no parent work    *)
(*   backs both sides of the child fork.                                   *)
(*                                                                         *)
(* Child weights: ca = 4, cb = 3, c0 = 1 + 4 + 3 = 8.                       *)
(***************************************************************************)
EXTENDS HierarchyProps

FPBlocks == {"pg", "p0", "pa", "pa2", "pb", "pb2", "pb3"}
FCBlocks == {"c0", "ca", "cb"}
FGBlocks == {}
FAll == FPBlocks \cup FCBlocks

FParent == [x \in FAll |->
               CASE x = "p0" -> "pg"
                 [] x = "pa" -> "p0" [] x = "pb" -> "p0"
                 [] x = "pa2" -> "pa"
                 [] x = "pb2" -> "pb" [] x = "pb3" -> "pb2"
                 [] x = "ca" -> "c0" [] x = "cb" -> "c0"
                 [] OTHER    -> "none"]

FCidRank == [x \in FAll |->
               CASE x = "pg" -> 0 [] x = "p0" -> 1
                 [] x = "pa" -> 2 [] x = "pa2" -> 3
                 [] x = "pb" -> 4 [] x = "pb2" -> 5 [] x = "pb3" -> 6
                 [] x = "c0" -> 7 [] x = "ca" -> 8 [] x = "cb" -> 9]

FGrinds == {"g_pg", "g_p0", "g_pa", "g_pa2", "g_pb", "g_pb2", "g_pb3",
            "g_ca", "g_cb"}

FObs ==
    { [ch |-> "P", g |-> "g_pg",  b |-> "pg",  q |-> 1],
      [ch |-> "P", g |-> "g_p0",  b |-> "p0",  q |-> 1],
      [ch |-> "P", g |-> "g_pa",  b |-> "pa",  q |-> 1],
      [ch |-> "P", g |-> "g_pa2", b |-> "pa2", q |-> 1],
      [ch |-> "P", g |-> "g_pb",  b |-> "pb",  q |-> 1],
      [ch |-> "P", g |-> "g_pb2", b |-> "pb2", q |-> 1],
      [ch |-> "P", g |-> "g_pb3", b |-> "pb3", q |-> 1],
      [ch |-> "C", g |-> "g_p0",  b |-> "c0",  q |-> 1],
      [ch |-> "C", g |-> "g_ca",  b |-> "ca",  q |-> 3],
      [ch |-> "C", g |-> "g_cb",  b |-> "cb",  q |-> 1] }

FCommits == { <<"p0", "c0">>, <<"pa", "ca">>, <<"pb", "cb">> }

\* A committed child's anchor is its carrier's prevState (here its parent).
FAnchor == [x \in FCBlocks |->
               CASE x = "c0" -> "pg" [] OTHER -> "p0"]

FExpectedChildWork == [x \in FCBlocks |->
               CASE x = "c0" -> 8 [] x = "ca" -> 4 [] OTHER -> 3]

FValidAll == [x \in FAll |-> TRUE]
FHeaderNone == {}
FTips ==
    [P |-> [canonical |-> "pb3", validated |-> "pb3"],
     C |-> [canonical |-> "ca",  validated |-> "ca"],
     G |-> [canonical |-> "none", validated |-> "none"]]

=============================================================================
