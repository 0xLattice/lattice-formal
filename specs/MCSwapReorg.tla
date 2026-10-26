-------------------------- MODULE MCSwapReorg ---------------------------
(***************************************************************************)
(* Three further blocks on each chain and one swap: enough for a parent   *)
(* fork with the receipt on one side only, a forged parent block with a    *)
(* valid block above it, and a child deposit, release and sibling.         *)
(***************************************************************************)
EXTENDS SwapReorg

MCPIds == <<"p1", "p2", "p3">>
MCCIds == <<"c1", "c2", "c3">>
MCSwaps == {"s"}

\* MCSwapReorg_Replay: one further P block, four C blocks: deposit,
\* release, and room to deposit and release the same key again.
MCPIds1 == <<"p1">>
MCCIds4 == <<"c1", "c2", "c3", "c4">>

=============================================================================
