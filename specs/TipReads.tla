------------------------------ MODULE TipReads ------------------------------
(***************************************************************************)
(* Reads of a tip's state on a lattice-node host whose store has gaps.     *)
(* Not protocol: what a host stores is the operator's choice (`state:`),   *)
(* and on `state: tip` the store is a cache of the tip's state. Nodes of   *)
(* it may be gone: let go of, swept, never fetched. Nothing heals the      *)
(* store (retention as on lattice-node main), so a read is answered only   *)
(* if its reader reads what the store lacks through peers.                 *)
(*                                                                         *)
(* A read needs the path from the state's root to its target (an account  *)
(* read goes through the account tree's root). A reader in `Through`       *)
(* judges from the store first and, only when that verdict is              *)
(* `unavailable`, again through peers (`NodeRuntime.reading`): what peers  *)
(* answer is checked against its CID and kept in memory, never written to  *)
(* the store. A reader not in `Through` reads the store alone. A           *)
(* preflight's transaction may be refused on itself alone (a bad          *)
(* signature, the wrong chain, a stale nonce): kind "bad".                 *)
(*                                                                         *)
(* Peers: an honest one, up or not (`up`), and liars, whose forged copies  *)
(* fail the CID check. A refused read (`unavailable`) is retried; the      *)
(* client keeps asking.                                                    *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS Readers, Through, MaxLosses

Nodes == {"R", "Acc", "A1", "Oth"}
Targets == {"A1", "Oth"}
Path(t) == CASE t = "A1" -> {"R", "Acc", "A1"} [] t = "Oth" -> {"R", "Oth"}
KindsOf(r) == IF r = "preflight" THEN {"good", "bad"} ELSE {"good"}
Status == {"wanted", "answered", "refused", "unavailable"}

(* What the read keeps of a peer's answer: the CID check refuses a forged  *)
(* copy, and the honest peer's copy is kept.                               *)
Served == {"true"}

VARIABLES
    held,      \* nodes of the tip's state the store holds
    mem,       \* node -> "none" | "true" | "forged": what reads kept in memory
    req,       \* reader -> its current read
    up,        \* the honest peer serves
    losses,    \* bound on the store's losses
    askedBad   \* a transaction refused on itself alone was asked of peers

vars == <<held, mem, req, up, losses, askedBad>>

NoMem == [n \in Nodes |-> "none"]

Init ==
    /\ held = Nodes
    /\ mem = NoMem
    /\ req \in {f \in [Readers -> [st : {"wanted"}, t : Targets, k : {"good", "bad"}, right : {TRUE}]] :
                  \A r \in Readers : f[r].k \in KindsOf(r)}
    /\ up \in BOOLEAN
    /\ losses = 0
    /\ askedBad = FALSE

(* The store loses a node of the tip's state, for good.                    *)
Lose(n) ==
    /\ losses < MaxLosses /\ n \in held
    /\ held' = held \ {n} /\ losses' = losses + 1
    /\ UNCHANGED <<mem, req, up, askedBad>>

(* A restart, or the read cache's budget, empties memory.                  *)
Evict ==
    /\ mem # NoMem /\ mem' = NoMem
    /\ UNCHANGED <<held, req, up, losses, askedBad>>

Flip == up' = ~up /\ UNCHANGED <<held, mem, req, losses, askedBad>>

(* A new read: a transaction submitted, a block executed, an RPC call.     *)
Ask(r, t, k) ==
    /\ req[r].st \in {"answered", "refused"} /\ k \in KindsOf(r)
    /\ req' = [req EXCEPT ![r] = [st |-> "wanted", t |-> t, k |-> k, right |-> TRUE]]
    /\ UNCHANGED <<held, mem, up, losses, askedBad>>

Retry(r) ==
    /\ req[r].st = "unavailable"
    /\ req' = [req EXCEPT ![r].st = "wanted"]
    /\ UNCHANGED <<held, mem, up, losses, askedBad>>

(* The verdict from this store alone.                                      *)
LocalVerdict(r) ==
    IF req[r].k = "bad" THEN "refused"
    ELSE IF Path(req[r].t) \subseteq held THEN "answered"
    ELSE "unavailable"

(* Judged again through peers: memory first, then the honest peer if up.   *)
ReadThrough(r) ==
    LET need == Path(req[r].t)
        missing == {n \in need \ held : mem[n] = "none"}
        done == IF req[r].k = "bad" THEN "refused" ELSE "answered"
    IN  /\ askedBad' = (askedBad \/ req[r].k = "bad")
        /\ IF missing = {} \/ up
           THEN \E got \in [missing -> Served] :
                  LET m1 == [n \in Nodes |-> IF n \in missing THEN got[n] ELSE mem[n]]
                  IN  /\ mem' = m1
                      /\ req' = [req EXCEPT ![r].st = done,
                                            ![r].right = \A n \in need \ held : m1[n] = "true"]
           ELSE /\ mem' = mem
                /\ req' = [req EXCEPT ![r].st = "unavailable"]

Judge(r) ==
    /\ req[r].st = "wanted"
    /\ IF r \in Through /\ LocalVerdict(r) = "unavailable"
       THEN ReadThrough(r)
       ELSE /\ req' = [req EXCEPT ![r].st = LocalVerdict(r), ![r].right = TRUE]
            /\ UNCHANGED <<mem, askedBad>>
    /\ UNCHANGED <<held, up, losses>>

Next ==
    \/ \E n \in Nodes : Lose(n)
    \/ Evict \/ Flip
    \/ \E r \in Readers : Judge(r) \/ Retry(r) \/ \E t \in Targets, k \in {"good", "bad"} : Ask(r, t, k)

Spec == Init /\ [][Next]_vars /\ \A r \in Readers : WF_vars(Judge(r)) /\ WF_vars(Retry(r))

TypeOK ==
    /\ held \subseteq Nodes
    /\ mem \in [Nodes -> {"none", "true", "forged"}]
    /\ req \in [Readers -> [st : Status, t : Targets, k : {"good", "bad"}, right : BOOLEAN]]
    /\ up \in BOOLEAN /\ losses \in 0..MaxLosses /\ askedBad \in BOOLEAN

(* An answer is judged on the true state: no forged copy is read.          *)
RightAnswers == \A r \in Readers : req[r].st = "answered" => req[r].right

(* What the store refuses on the transaction alone costs no peer request.  *)
StoreFirst == ~askedBad

(* With the honest peer serving from some point on, every read is          *)
(* answered (or refused on itself), whatever the store lost.               *)
Answered ==
    <>[]up => \A r \in Readers :
                 (req[r].st = "wanted") ~> (req[r].st \in {"answered", "refused"})

(* Witness: a read goes through peers (must be violated).                  *)
NoPeerRead == mem = NoMem
=============================================================================
