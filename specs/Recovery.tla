------------------------------ MODULE Recovery ------------------------------
(***************************************************************************)
(* Import, durability and recovery of one chain, modelled from the         *)
(* normative spec (Lattice docs/spec.md §9.3 steps 8-9, §9.8, §9.9 and     *)
(* §12.5.11), not from the implementation.                                 *)
(*                                                                         *)
(* One node imports candidate batches.  Each import attempt is checked     *)
(* against the live graph, staged as one immutable batch in a durable log, *)
(* and then applied to the volatile in-memory graph through the reducer.   *)
(* The node may crash in any state.  A crash loses everything volatile;    *)
(* recovery replays the durable log through the same reducer, in any       *)
(* order, and only then exposes the runtime.                               *)
(*                                                                         *)
(* A batch is a record [k, b, m, g, q, v]:                                  *)
(*   k = "block": block b with consensus metadata m, its securing grind g  *)
(*                of quantity q, and, if v, its validation (eager tier);   *)
(*   k = "work" : grind g located at b with quantity q (a location, or a   *)
(*                strengthening of one already held);                      *)
(*   k = "excl" : the invalidity exclusion of b;                           *)
(*   k = "valid": the deferred validation of b.                            *)
(* Unused fields are None, 0 or FALSE.                                     *)
(*                                                                         *)
(* The durable write of one batch is atomic: the node writes every fact    *)
(* of a step in one SQLite transaction, which a crash or error rolls back  *)
(* whole.  A crash therefore falls between steps, never inside a batch.    *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Blocks,         \* every block that could ever be held
    None,           \* "no block" / unused field
    Parent,         \* Blocks -> Blocks \cup {None}; a static tree
    CidRank,        \* Blocks -> Nat, injective; smaller = smaller CID
    Grinds,         \* grind identities
    Batches,        \* the candidate batches import attempts may stage
    Genesis,        \* the bootstrap batch (a root block, executed)
    Rebuild,        \* Batches -> Batches: what re-resolving a candidate
                    \* after durability would produce (used by a mutant)
    MaxLog,         \* bound on the durable log's length
    MaxCrashes,     \* bound on crashes, so every behaviour stops crashing
    FloorPersisted, \* staging also records the reserved revision as a floor
    SortedReplay    \* replay follows the implementation's sort order

ASSUME /\ None \notin Blocks
       /\ \A b \in Blocks : Parent[b] \in Blocks \cup {None}
       /\ \A x, y \in Blocks : x # y => CidRank[x] # CidRank[y]
       /\ Genesis \in Batches /\ Genesis.k = "block" /\ Parent[Genesis.b] = None
       /\ \A x \in Batches : Rebuild[x] \in Batches
       /\ FloorPersisted \in BOOLEAN /\ SortedReplay \in BOOLEAN

VARIABLES
    log,      \* durable: the staged batches, in staging order
    floor,    \* durable: the revision floor (0 unless FloorPersisted)
    ptip,     \* durable: a persisted tip, a derived cache (§9.8)
    mem,      \* volatile: the in-memory accepted graph
    tip,      \* volatile: the canonical projection of mem
    rev,      \* volatile: the current revision
    up,       \* the runtime is exposed (bootstrap / recovery complete)
    cur,      \* the commit in flight under the mutation lease
    rec,      \* during recovery: the log indices already replayed
    crashes,  \* crashes so far
    seen,     \* ghost: the highest revision ever exposed before a crash
    lost,     \* ghost: batches durable but not yet visible at a crash
    refused   \* ghost: the store refused conflicting metadata

vars == <<log, floor, ptip, mem, tip, rev, up, cur, rec, crashes, seen, lost, refused>>

Idle == [p |-> "idle", x |-> Genesis]  \* x unused while idle

Roots == {b \in Blocks : Parent[b] = None}

RECURSIVE AncOrSelf(_)
AncOrSelf(b) == IF b = None THEN {} ELSE {b} \cup AncOrSelf(Parent[b])

Max(a, b) == IF a >= b THEN a ELSE b

-----------------------------------------------------------------------------
(* The accepted graph and its projection (§9.1, §9.2, §9.4, §9.9).  The    *)
(* work algebra and tip rule are ForkChoice.tla's, restated over a graph   *)
(* value G instead of per-node state, so a replayed graph and a live one   *)
(* can be compared.                                                        *)

EmptyG == [held |-> {}, meta |-> [b \in Blocks |-> None],
           loc |-> [g \in Grinds |-> None], qty |-> [g \in Grinds |-> 0],
           val |-> {}, exc |-> {}]

RECURSIVE SumQty(_, _)
SumQty(G, S) ==
    IF S = {} THEN 0
    ELSE LET g == CHOOSE x \in S : TRUE IN G.qty[g] + SumQty(G, S \ {g})

Subtree(G, b) == {x \in G.held : b \in AncOrSelf(x)}

TrueCumWork(G, b) == SumQty(G, {g \in Grinds : G.loc[g] \in Subtree(G, b)})

Better(G, x, y) ==
    \/ TrueCumWork(G, x) > TrueCumWork(G, y)
    \/ TrueCumWork(G, x) = TrueCumWork(G, y) /\ CidRank[x] < CidRank[y]

Best(G, S) == CHOOSE x \in S : \A y \in S \ {x} : Better(G, x, y)

RECURSIVE Descend(_, _, _)
Descend(G, b, E) ==
    LET C == {c \in E : Parent[c] = b}
    IN  IF C = {} THEN b ELSE Descend(G, Best(G, C), E)

TipOver(G, E) == IF Roots \cap E = {} THEN None ELSE Descend(G, Best(G, Roots \cap E), E)

Selectable(G) == {b \in G.held : AncOrSelf(b) \cap G.exc = {}}

CanonicalTip(G) == TipOver(G, Selectable(G))
ValidatedTip(G) == TipOver(G, G.val)

-----------------------------------------------------------------------------
(* The reducer (§9.3 step 9, §9.8): one function shared by live import and *)
(* recovery.                                                               *)

\* What replay needs before a batch can apply.  A batch that is not ready
\* is deferred and retried, never dropped.  A root exclusion waits for
\* another root's validation (§9.9 root rule).
Ready(G, x) ==
    CASE x.k = "block" -> Parent[x.b] \in G.held \cup {None}
      [] x.k = "work"  -> x.b \in G.held
      [] x.k = "valid" -> x.b \in G.held
      [] x.k = "excl"  -> /\ x.b \in G.held
                          /\ x.b \in Roots => \E r \in Roots \ {x.b} : r \in G.val

\* Apply one batch.  A repeated block keeps its first metadata (conflicting
\* metadata never reaches the log, ConflictRejected).  Quantities ratchet:
\* the strongest observation wins (§9.1), so identical or weaker replay is a
\* duplicate.
Apply(G, x) ==
    CASE x.k = "block" ->
            [G EXCEPT !.held = @ \cup {x.b},
                      !.meta[x.b] = IF x.b \in G.held THEN @ ELSE x.m,
                      !.loc[x.g] = x.b,
                      !.qty[x.g] = IF x.q > @ THEN x.q ELSE @,
                      !.val = IF x.v THEN @ \cup {x.b} ELSE @]
      [] x.k = "work" ->
            [G EXCEPT !.loc[x.g] = x.b,
                      !.qty[x.g] = IF x.q > @ THEN x.q ELSE @]
      [] x.k = "excl"  -> [G EXCEPT !.exc = @ \cup {x.b}]
      [] x.k = "valid" -> [G EXCEPT !.val = @ \cup {x.b}]

\* A consensus mutation, which takes a revision (§12.5.11).  A validation
\* moves the executed set only; the implementation numbers it with no
\* revision, and so does the model.
Mutates(G, H) == G.held # H.held \/ G.loc # H.loc \/ G.qty # H.qty \/ G.exc # H.exc

\* The batch's facts are all in G.
Reflects(G, x) ==
    CASE x.k = "block" -> /\ x.b \in G.held /\ G.loc[x.g] = x.b /\ G.qty[x.g] >= x.q
                          /\ x.v => x.b \in G.val
      [] x.k = "work"  -> G.loc[x.g] = x.b /\ G.qty[x.g] >= x.q
      [] x.k = "excl"  -> x.b \in G.exc
      [] x.k = "valid" -> x.b \in G.val

\* The reference: the graph the durable batches produce, applied in
\* staging order (the order live import made them durable).
RECURSIVE Fold(_, _)
Fold(G, s) == IF s = <<>> THEN G ELSE Fold(Apply(G, Head(s)), Tail(s))

-----------------------------------------------------------------------------
(* Live import (§9.3).  Steps 1-7 (resolution, proof, validation, content  *)
(* storage) are folded into Admissible: the local rules a candidate must   *)
(* pass against the live graph.  It is checked under the mutation lease,   *)
(* so the graph cannot move between the check and the apply.              *)

Admissible(G, x) ==
    CASE x.k = "block" -> /\ Parent[x.b] \in G.held \cup {None}
                          /\ G.loc[x.g] \in {None, x.b}
                          /\ x.v => /\ x.b \notin G.exc
                                    /\ Parent[x.b] \in G.val \cup {None}
                          \* a held block's batch is its deferred validation,
                          \* re-stating the strongest grind held there
                          \* (ChainTree.connectJob)
                          /\ x.b \in G.held =>
                                /\ x.v /\ G.loc[x.g] = x.b /\ x.q = G.qty[x.g]
                                /\ \A g \in Grinds : G.loc[g] = x.b => G.qty[g] <= x.q
      [] x.k = "work"  -> /\ x.b \in G.held /\ G.loc[x.g] \in {None, x.b}
                          \* weaker or equal is a duplicate: no fact (addWork)
                          /\ x.q > G.qty[x.g]
      [] x.k = "excl"  -> /\ x.b \in G.held \ G.val
                          /\ x.b \in Roots => \E r \in Roots \ {x.b} : r \in G.val
      [] x.k = "valid" -> /\ x.b \in G.held \ G.exc
                          /\ Parent[x.b] \in G.val \cup {None}

\* The store refuses a block fact whose identity is held with different
\* metadata (the fact ID is the block CID; the whole transaction rolls back).
StoreAccepts(x) ==
    x.k = "block" =>
        \A i \in DOMAIN log : log[i].k = "block" /\ log[i].b = x.b => log[i].m = x.m

\* Step 1-7: an attempt passes the local rules and takes the lease.  A
\* refused candidate records no fact and changes nothing.
Begin(x) ==
    /\ up /\ cur.p = "idle" /\ Len(log) < MaxLog
    /\ x \in Batches \ {Genesis}
    /\ \A i \in DOMAIN log : log[i] # x   \* re-staging an identical batch: see ReplayIdempotent
    /\ Admissible(mem, x)
    /\ cur' = [p |-> "checked", x |-> x]
    /\ UNCHANGED <<log, floor, ptip, mem, tip, rev, up, rec, crashes, seen, lost, refused>>

\* Step 8: atomic durability of the one immutable batch.  With
\* FloorPersisted the same transaction records the revision the batch was
\* reserved (rev + 1) as the floor.
Stage ==
    /\ up /\ cur.p = "checked"
    /\ StoreAccepts(cur.x)
    /\ log' = Append(log, cur.x)
    /\ floor' = IF FloorPersisted THEN rev + 1 ELSE floor
    /\ cur' = [cur EXCEPT !.p = "durable"]
    /\ UNCHANGED <<ptip, mem, tip, rev, up, rec, crashes, seen, lost, refused>>

\* Storage or durability failure: nothing became durable, the reservation
\* is released, and the graph is unchanged.  An I/O error may happen at any
\* attempt; conflicting metadata always fails here.
StageFail ==
    /\ up /\ cur.p = "checked"
    /\ cur' = Idle
    /\ refused' = (refused \/ ~StoreAccepts(cur.x))
    /\ UNCHANGED <<log, floor, ptip, mem, tip, rev, up, rec, crashes, seen, lost>>

\* Step 9: apply exactly the staged batch, then project.
ApplyStaged ==
    /\ up /\ cur.p = "durable"
    /\ LET H == Apply(mem, cur.x)
       IN  /\ mem' = H
           /\ rev' = IF Mutates(mem, H) THEN rev + 1 ELSE rev
           /\ tip' = CanonicalTip(H)
    /\ cur' = Idle
    /\ UNCHANGED <<log, floor, ptip, up, rec, crashes, seen, lost, refused>>

\* The node may persist its tip as a cache at any time; it may lag.
PersistTip ==
    /\ up /\ ptip # tip
    /\ ptip' = tip
    /\ UNCHANGED <<log, floor, mem, tip, rev, up, cur, rec, crashes, seen, lost, refused>>

-----------------------------------------------------------------------------
(* Crash and recovery (§9.8).                                              *)

Crash ==
    /\ crashes < MaxCrashes
    /\ crashes' = crashes + 1
    /\ up' = FALSE
    /\ mem' = EmptyG /\ tip' = None /\ rev' = 0
    /\ cur' = Idle /\ rec' = {}
    /\ seen' = IF up THEN Max(seen, rev) ELSE seen
    /\ lost' = IF up /\ cur.p = "durable" /\ ~Reflects(mem, cur.x) THEN lost \cup {cur.x} ELSE lost
    /\ UNCHANGED <<log, floor, ptip, refused>>

\* Genesis bootstrap: the genesis batch is staged before any runtime exists;
\* the runtime appears only through Restore (§9.3).
BootStage ==
    /\ ~up /\ log = <<>>
    /\ log' = <<Genesis>>
    /\ floor' = IF FloorPersisted THEN 1 ELSE floor
    /\ UNCHANGED <<ptip, mem, tip, rev, up, cur, rec, crashes, seen, lost, refused>>

\* With SortedReplay, replay follows the implementation's sort
\* (ChainTree.replay): block batches by height, then by work; then
\* work-only batches by work; then validations, then exclusions.  Equal
\* keys may go in either order.  A batch that is not Ready is deferred, so
\* the next replayed batch is the smallest-keyed one that is Ready (the
\* implementation retries deferred batches in later rounds; with parents
\* sorted before children nothing here defers).
Height(b) == Cardinality(AncOrSelf(b)) - 1

SortKey(x) ==
    CASE x.k = "block" -> <<0, Height(x.b), x.q>>
      [] x.k = "work"  -> <<1, 0, x.q>>
      [] x.k = "valid" -> <<2, 0, 0>>
      [] x.k = "excl"  -> <<3, 0, 0>>

KeyLess(s, t) ==
    \/ s[1] < t[1]
    \/ s[1] = t[1] /\ s[2] < t[2]
    \/ s[1] = t[1] /\ s[2] = t[2] /\ s[3] < t[3]

SortedOK(i) ==
    SortedReplay =>
        ~\E j \in DOMAIN log \ rec :
            Ready(mem, log[j]) /\ KeyLess(SortKey(log[j]), SortKey(log[i]))

\* Replay one durable batch through the same reducer, in any order the
\* prerequisites allow.  The projection is deferred to the end.
ReplayOne(i) ==
    /\ ~up /\ i \in DOMAIN log \ rec
    /\ Ready(mem, log[i]) /\ SortedOK(i)
    /\ LET H == Apply(mem, log[i])
       IN  /\ mem' = H
           /\ rev' = IF Mutates(mem, H) THEN rev + 1 ELSE rev
    /\ rec' = rec \cup {i}
    /\ UNCHANGED <<log, floor, ptip, tip, up, cur, crashes, seen, lost, refused>>

\* Every durable batch replayed: reproject canonicality, raise the revision
\* to the durable floor, expose the runtime.
Restore ==
    /\ ~up /\ log # <<>> /\ rec = DOMAIN log
    /\ tip' = CanonicalTip(mem)
    /\ rev' = Max(rev, floor)
    /\ up' = TRUE
    /\ UNCHANGED <<log, floor, ptip, mem, cur, rec, crashes, seen, lost, refused>>

Init ==
    /\ log = <<>> /\ floor = 0 /\ ptip = None
    /\ mem = EmptyG /\ tip = None /\ rev = 0
    /\ up = FALSE /\ cur = Idle /\ rec = {}
    /\ crashes = 0 /\ seen = 0 /\ lost = {} /\ refused = FALSE

Next ==
    \/ \E x \in Batches : Begin(x)
    \/ Stage \/ StageFail \/ ApplyStaged \/ PersistTip
    \/ Crash \/ BootStage \/ Restore
    \/ \E i \in 1..MaxLog : ReplayOne(i)

Spec ==
    /\ Init /\ [][Next]_vars
    /\ WF_vars(ApplyStaged) /\ WF_vars(BootStage) /\ WF_vars(Restore)
    /\ WF_vars(\E i \in 1..MaxLog : ReplayOne(i))

-----------------------------------------------------------------------------
(* Properties.                                                             *)

TypeOK ==
    /\ Len(log) <= MaxLog /\ \A i \in DOMAIN log : log[i] \in Batches
    /\ mem.held \subseteq Blocks /\ mem.val \subseteq mem.held /\ mem.exc \subseteq mem.held
    /\ cur.p \in {"idle", "checked", "durable"}
    /\ rec \subseteq DOMAIN log
    /\ rev \in Nat /\ floor \in Nat /\ seen \in Nat

\* The durable batches that should be visible: all of them, except the one
\* a commit has staged and not yet applied.
VisibleLog == IF cur.p = "durable" THEN SubSeq(log, 1, Len(log) - 1) ELSE log

\* §9.3, §9.8: the exposed graph, weights and tip are exactly what the
\* durable prefix produces, whether built live or rebuilt by replay in any
\* order.  The tip is reprojected from the graph, never a cached value.
RecoveredEqualsLive ==
    up => LET R == Fold(EmptyG, VisibleLog)
          IN  /\ mem = R
              /\ tip = CanonicalTip(R)

\* §9.3 "Durability MUST precede visible graph mutation": nothing exposed
\* is missing from the durable log, and no runtime exists before genesis is
\* durable.
VisibleImpliesDurable ==
    up => LET D == Fold(EmptyG, log)
          IN  /\ log # <<>>
              /\ mem.held \subseteq D.held /\ mem.val \subseteq D.val /\ mem.exc \subseteq D.exc
              /\ \A g \in Grinds : mem.loc[g] # None =>
                     mem.loc[g] = D.loc[g] /\ mem.qty[g] <= D.qty[g]

\* §9.3, §9.8: identical replay is idempotent.  Applying any durable batch
\* again to the exposed graph changes nothing.
ReplayIdempotent ==
    up => \A i \in DOMAIN VisibleLog : Apply(mem, log[i]) = mem

\* §9.3: conflicting immutable metadata is rejected.  The log never holds
\* two metadata values for one block, nor one grind at two blocks, and the
\* graph holds the durable metadata.
ConflictRejected ==
    /\ \A i, j \in DOMAIN log :
          /\ log[i].k = "block" /\ log[j].k = "block" /\ log[i].b = log[j].b
                 => log[i].m = log[j].m
          /\ log[i].k \in {"block", "work"} /\ log[j].k \in {"block", "work"}
             /\ log[i].g = log[j].g => log[i].b = log[j].b
    /\ up => \A i \in DOMAIN log :
                log[i].k = "block" /\ log[i].b \in mem.held => mem.meta[log[i].b] = log[i].m

\* §12.5.11 across crashes: no exposed revision is ever lower than one
\* exposed before (seen), and live mutations take strictly greater ones.
RevisionMonotone == up => rev >= seen

RevisionAdvances ==
    [][up /\ up' /\ Mutates(mem, mem') => rev' > rev]_vars

\* §9.3: a storage or durability failure leaves the graph unchanged.
FailureLeavesGraphUnchanged ==
    [][up /\ up' /\ cur.p = "checked" /\ cur'.p = "idle" /\ log' = log
           => mem' = mem /\ tip' = tip /\ rev' = rev]_vars

\* Liveness: once crashes stop (they are bounded), the runtime comes up and
\* every durable batch becomes visible, for good.  The log is bounded, so
\* this covers every batch ever staged.
StagedBecomesVisible ==
    <>[](up /\ \A i \in DOMAIN log : Reflects(mem, log[i]))

\* Witnesses (each must be VIOLATED in its config).
\* A batch durable but not visible at a crash is shown after recovery.
NoLostBatchRecovered == ~(up /\ \E x \in lost : Reflects(mem, x))
\* The store refuses conflicting metadata in some behaviour.
NoConflictRefused == ~refused

=============================================================================
