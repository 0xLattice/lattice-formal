------------------------ MODULE DerivedChildGrinds -------------------------
(***************************************************************************)
(* One node deriving a hosted child chain's credited grinds from the      *)
(* parent blocks (carriers) it weighs, push only: the node never fetches  *)
(* a child block.  The child block's bytes are in the node's store from   *)
(* the start (Authored: the node is its author) or arrive by gossip, with *)
(* or without a peer proof.                                                *)
(*                                                                         *)
(*   carrier  commits  grinds (meets the committed block's target?)        *)
(*   B1       C1       g1 (yes), g2 (no)                                   *)
(*   B2       C1       g3 (yes)                                            *)
(*   B3       C2       g4 (yes)                                            *)
(*                                                                         *)
(* A child block is unknown, awaiting (in memory, waiting for a proof;     *)
(* at most Cap at once) or held (durable).  The first credit a block       *)
(* takes makes it held.                                                    *)
(*                                                                         *)
(* Triggers, each inside the step that causes it (the step's `arrived`     *)
(* set is a LET, never state):                                             *)
(*  (a) carrier B weighed: derive(B, C), carrying C's bytes if C is known, *)
(*      else as a read of the local store;                                 *)
(*  (b) C arrives (unknown -> awaiting, by gossip or by a store read):     *)
(*      derive(Bi, C) for every weighed carrier Bi committing C.           *)
(* A derive job answers later, in any order, with the verified proofs of   *)
(* its carrier's grinds that meet C's target, or nothing if it had no      *)
(* bytes and the store has none.  Answers are always applied; jobs are     *)
(* never deduplicated; `deriving` (jobs issued per child, in memory) only  *)
(* guards an awaiting block from eviction.                                 *)
(*                                                                         *)
(* Environment: peer gossip with real or bogus proofs, peer purge, at most *)
(* MaxRestarts restarts and MaxUnhosts unhost/re-host cycles.  A restart   *)
(* loses jobs, `deriving`, awaiting blocks and peer proofs; an unhost      *)
(* loses the same except the jobs, which may answer into the re-hosted     *)
(* level.  Weighed carriers and held blocks with their credits persist,    *)
(* and the boot pass of a hosted level takes every held block as arrived.  *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    Authored,       \* child blocks in this node's store from the start
    AuthorHolds,    \* whether those are held from the start, or only stored
    Cap,            \* awaiting capacity
    MaxRestarts,
    MaxUnhosts

Carriers == {"B1", "B2", "B3"}
Children == {"C1", "C2"}
Commit == [b \in Carriers |-> IF b = "B3" THEN "C2" ELSE "C1"]
Grinds == {"g1", "g2", "g3", "g4"}
CarrierOf == [g \in Grinds |-> CASE g \in {"g1", "g2"} -> "B1"
                                 [] g = "g3" -> "B2"
                                 [] OTHER -> "B3"]
Meets == {"g1", "g3", "g4"}
\* What a peer may attach: a real proof (g3), one for a grind that misses
\* (g2), or garbage.
PeerProofs == {"g2", "g3", "bogus"}

\* A job: <<carrier, child, the child's bytes carried at issue>>.
JobKeys == {<<b, Commit[b], k>> : b \in Carriers, k \in BOOLEAN}

ASSUME Authored \subseteq Children /\ AuthorHolds \in BOOLEAN /\ Cap \in Nat \ {0}

VARIABLES
    weighed,    \* carriers weighed (persisted)
    status,     \* child -> "unknown" | "awaiting" | "held" (held persisted)
    credited,   \* child -> grinds credited (persisted with held)
    jobs,       \* JobKeys -> number in flight
    deriving,   \* child -> jobs issued since the last restart or unhost
    peerQ,      \* child -> peer proofs queued or in a check
    hosted,
    restarts,
    unhosts

vars == <<weighed, status, credited, jobs, deriving, peerQ, hosted, restarts, unhosts>>

Full(c) == {g \in Meets : CarrierOf[g] \in weighed /\ Commit[CarrierOf[g]] = c}
Proofs(b) == {g \in Meets : CarrierOf[g] = b}
StoreHas(c) == c \in Authored \/ status[c] = "held"
Awaiting(st) == {c \in Children : st[c] = "awaiting"}
Committers(c) == {b \in weighed : Commit[b] = c}

NoJobs == [k \in JobKeys |-> 0]
NoDeriving == [c \in Children |-> 0]
NoPeer == [c \in Children |-> {}]
Forget(st) == [c \in Children |-> IF st[c] = "held" THEN "held" ELSE "unknown"]

\* Jobs for the committers of every block in arr.
ArrivalKeys(arr) == {<<b, Commit[b], TRUE>> : b \in {x \in weighed : Commit[x] \in arr}}
\* Trigger (b).
ArrivalJobs(arr) == ArrivalKeys(arr)
\* What issuing S puts in flight (nothing dedups).
Issued(js, S) == S
AddJobs(js, S) == [k \in JobKeys |-> IF k \in S THEN js[k] + 1 ELSE js[k]]
AddDeriving(dv, S) == [c \in Children |-> dv[c] + Cardinality({k \in S : k[2] = c})]

\* The status functions after c enters awaiting, evicting an awaiting
\* block with no derivation counted if full; {} when there is no room.
Admit(st, dv, c) ==
    IF Cardinality(Awaiting(st)) < Cap THEN {[st EXCEPT ![c] = "awaiting"]}
    ELSE {[x \in Children |-> IF x = c THEN "awaiting" ELSE IF x = v THEN "unknown" ELSE st[x]] :
            v \in {y \in Awaiting(st) : dv[y] = 0}}

\* Credit P at c (known in st); the first credit makes c held.
Credit(st, c, P) ==
    /\ credited' = [credited EXCEPT ![c] = @ \cup P]
    /\ status' = IF P # {} THEN [st EXCEPT ![c] = "held"] ELSE st

Init ==
    /\ weighed = {}
    /\ status = [c \in Children |-> IF AuthorHolds /\ c \in Authored THEN "held" ELSE "unknown"]
    /\ credited = [c \in Children |-> {}]
    /\ jobs = NoJobs
    /\ deriving = NoDeriving
    /\ peerQ = NoPeer
    /\ hosted = TRUE
    /\ restarts = 0
    /\ unhosts = 0

\* Trigger (a).
Weigh(b) ==
    /\ b \notin weighed
    /\ weighed' = weighed \cup {b}
    /\ IF hosted
         THEN LET S == Issued(jobs, {<<b, Commit[b], status[Commit[b]] # "unknown">>})
              IN /\ jobs' = AddJobs(jobs, S)
                 /\ deriving' = AddDeriving(deriving, S)
         ELSE UNCHANGED <<jobs, deriving>>
    /\ UNCHANGED <<status, credited, peerQ, hosted, restarts, unhosts>>

\* A peer sends c, with proof p or none ("none").  Re-sending a known block
\* only queues its proof.  An unknown block without a proof is taken only
\* if a weighed carrier commits it.
Gossip(c, p) ==
    /\ hosted
    /\ peerQ' = IF p = "none" THEN peerQ ELSE [peerQ EXCEPT ![c] = @ \cup {p}]
    /\ IF status[c] # "unknown"
         THEN UNCHANGED <<status, jobs, deriving>>
         ELSE /\ p # "none" \/ Committers(c) # {}
              /\ \E st \in Admit(status, deriving, c) :
                    LET S == Issued(jobs, ArrivalJobs({c}))
                    IN /\ status' = st
                       /\ jobs' = AddJobs(jobs, S)
                       /\ deriving' = AddDeriving(deriving, S)
    /\ UNCHANGED <<weighed, credited, hosted, restarts, unhosts>>

\* The author republishes c, without a proof, until it is credited here.
AuthorGossip(c) == credited[c] = {} /\ Gossip(c, "none")

CheckPeerProof(c, p) ==
    /\ p \in peerQ[c]
    /\ peerQ' = [peerQ EXCEPT ![c] = @ \ {p}]
    /\ IF p \in Meets /\ CarrierOf[p] \in weighed /\ Commit[CarrierOf[p]] = c
          /\ status[c] # "unknown"
         THEN Credit(status, c, {p})
         ELSE UNCHANGED <<status, credited>>
    /\ UNCHANGED <<weighed, jobs, deriving, hosted, restarts, unhosts>>

Purge ==
    /\ peerQ # NoPeer
    /\ peerQ' = NoPeer
    /\ UNCHANGED <<weighed, status, credited, jobs, deriving, hosted, restarts, unhosts>>

\* Whether an answer is applied, given the count before it is taken off.
Applies(dv, c) == TRUE

Answer(k) ==
    LET b == k[1]
        c == k[2]
        carried == k[3]
        js1 == [jobs EXCEPT ![k] = @ - 1]
        dv1 == [deriving EXCEPT ![c] = IF @ > 0 THEN @ - 1 ELSE 0]
    IN
    /\ jobs[k] > 0
    /\ IF ~hosted \/ ~Applies(deriving, c)
         THEN /\ jobs' = js1
              /\ deriving' = IF hosted THEN dv1 ELSE deriving
              /\ UNCHANGED <<status, credited>>
       ELSE IF ~carried /\ status[c] = "unknown" /\ StoreHas(c)
         \* The store read brings c in: an arrival.
         THEN IF Admit(status, dv1, c) = {}
                THEN /\ jobs' = js1 /\ deriving' = dv1
                     /\ UNCHANGED <<status, credited>>
                ELSE \E st \in Admit(status, dv1, c) :
                       LET S == Issued(js1, ArrivalJobs({c}))
                       IN /\ jobs' = AddJobs(js1, S)
                          /\ deriving' = AddDeriving(dv1, S)
                          /\ Credit(st, c, Proofs(b))
       ELSE /\ jobs' = js1
            /\ deriving' = dv1
            /\ IF (carried \/ StoreHas(c)) /\ status[c] # "unknown"
                 THEN Credit(status, c, Proofs(b))
                 ELSE UNCHANGED <<status, credited>>
    /\ UNCHANGED <<weighed, peerQ, hosted, restarts, unhosts>>

\* The boot pass: every held block arrives.
BootKeys(st) == ArrivalKeys({c \in Children : st[c] = "held"})

Restart ==
    /\ restarts < MaxRestarts
    /\ restarts' = restarts + 1
    /\ status' = Forget(status)
    /\ peerQ' = NoPeer
    /\ LET S == IF hosted THEN Issued(NoJobs, BootKeys(Forget(status))) ELSE {}
       IN /\ jobs' = AddJobs(NoJobs, S)
          /\ deriving' = AddDeriving(NoDeriving, S)
    /\ UNCHANGED <<weighed, credited, hosted, unhosts>>

Unhost ==
    /\ hosted /\ unhosts < MaxUnhosts
    /\ hosted' = FALSE
    /\ unhosts' = unhosts + 1
    /\ status' = Forget(status)
    /\ deriving' = NoDeriving
    /\ peerQ' = NoPeer
    /\ UNCHANGED <<weighed, credited, jobs, restarts>>

Rehost ==
    /\ ~hosted
    /\ hosted' = TRUE
    /\ LET S == Issued(jobs, BootKeys(status))
       IN /\ jobs' = AddJobs(jobs, S)
          /\ deriving' = AddDeriving(NoDeriving, S)
    /\ UNCHANGED <<weighed, status, credited, peerQ, restarts, unhosts>>

Next ==
    \/ \E b \in Carriers : Weigh(b)
    \/ \E c \in Children, p \in PeerProofs \cup {"none"} : Gossip(c, p)
    \/ \E c \in Children, p \in PeerProofs : CheckPeerProof(c, p)
    \/ Purge
    \/ \E k \in JobKeys : Answer(k)
    \/ Restart \/ Unhost \/ Rehost

\* Every job eventually answers; the author eventually re-gossips a block
\* it has not seen credited; an unhosted chain is eventually re-hosted.
Fairness ==
    /\ \A k \in JobKeys : WF_vars(Answer(k))
    /\ \A c \in Children \ Authored : WF_vars(AuthorGossip(c))
    /\ WF_vars(Rehost)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------

TypeOK ==
    /\ weighed \subseteq Carriers
    /\ status \in [Children -> {"unknown", "awaiting", "held"}]
    /\ credited \in [Children -> SUBSET Grinds]
    /\ jobs \in [JobKeys -> Nat]
    /\ deriving \in [Children -> Nat]
    /\ peerQ \in [Children -> SUBSET PeerProofs]
    /\ Cardinality(Awaiting(status)) <= Cap

\* Nothing unverified is credited.
Safety == \A c \in Children : credited[c] \subseteq Full(c)

\* Credit is only ever held at a held block.
CreditHeld == \A c \in Children : credited[c] # {} => status[c] = "held"

\* The author is done with c once it is credited here (or it is this node).
AuthorDone(c) == c \in Authored \/ credited[c] # {}

\* With nothing in flight, a held block whose author is done is fully credited.
QuiescentFull ==
    (hosted /\ jobs = NoJobs) =>
        \A c \in Children : status[c] = "held" /\ AuthorDone(c) => credited[c] = Full(c)

\* Results are invariant to arrival order and restart: in the end every
\* grind of a weighed carrier that meets its block's target is credited.
Converges == <>[](\A c \in Children : credited[c] = Full(c))

\* Witness, must FAIL: some credit is reachable.
NoCredit == \A c \in Children : credited[c] = {}

=============================================================================
