------------------------ MODULE DerivedChildGrinds -------------------------
(***************************************************************************)
(* One node crediting a hosted child level Y with the grinds of the       *)
(* parent-level blocks (carriers) that commit Y's blocks, push only: the  *)
(* node never fetches a child block.  A child block enters the node only  *)
(* by gossip (with or without a peer proof) or by its author's local      *)
(* submit, which is gossip from no peer.                                   *)
(*                                                                         *)
(*   carrier  commits  grinds (meets the committed block's target?)        *)
(*   B1       C1       g1 (yes), g2 (no)                                   *)
(*   B2       C1       g3 (yes)                                            *)
(*   B3       C2       g4 (yes), g5 (no)                                   *)
(*                                                                         *)
(* C1's parent is Y's genesis (in the tree); C2's parent is C1.            *)
(*                                                                         *)
(* A child block is unknown, awaiting (in memory, waiting for its first   *)
(* proof; at most Cap at once), pending (in memory: credited, waiting for *)
(* its parent to be in the tree or for its children index; evictable by   *)
(* the pending budget) or in the tree (durable, with its credits).  With  *)
(* DeferSettle a credited block stays pending after its parent is in the  *)
(* tree until a separate (fair) Settle step weighs it, as a pending       *)
(* header waits for its timestamp; without it, the step that promotes it  *)
(* also weighs it when its parent is in the tree and its index is held:   *)
(* the step weighs what it can before the budget evicts.                  *)
(*                                                                         *)
(* Children index (idx): a block arrives with its index inline ("held")   *)
(* or, with IndexFetched, without it ("asked": a request to an announcer).  A nil answer      *)
(* keeps the header and its credits: it is asked of the next announcer    *)
(* ("asked" again) or, with none left, waits ("waiting") until a tick     *)
(* re-asks its stream hole.  Nobody is blamed.  An index asked again and  *)
(* again is eventually served (its author holds it and pushes the block   *)
(* until it is weighed).                                                   *)
(*                                                                         *)
(* Proof queue: queued peer proofs (peerQ) never exceed the operator's    *)
(* total budget QBudget.  A proof over it is dropped without blame and    *)
(* its hole stays lacking (lack); a later tick re-asks it.  An honest     *)
(* peer logs a block once: while its relay's hole is lacking it waits to  *)
(* be asked again.  A blamed honest peer is disconnected (honest).        *)
(*                                                                         *)
(* Carriers' credited grind sets (cgr) only grow.  With Grow, the parent  *)
(* level is itself a child level X: a carrier is weighed with some of its *)
(* grinds and credited more later (each growth re-triggers derivation, as *)
(* a parent block whose work changed does), and X can be unhosted, which  *)
(* unhosts Y too.  Without Grow the parent is the root: a carrier is      *)
(* weighed with all its grinds and never unhosted.                         *)
(*                                                                         *)
(* Triggers, each inside the step that causes it:                          *)
(*  (a) carrier B weighed or credited a grind: derive(B, C) if C is known  *)
(*      (awaiting, pending or in the tree); an unknown C issues nothing;  *)
(*  (b) C arrives (unknown -> awaiting): derive(Bi, C) for every weighed  *)
(*      carrier Bi committing C;                                           *)
(*  (c) the boot pass of a hosted level (restart, re-host): every block   *)
(*      in the tree arrives.                                               *)
(* A derivation of (B, C) is issued only for the grinds of B not yet      *)
(* credited at C (a snapshot) and answers later, in any order, with the   *)
(* verified proofs of those grinds that meet C's target.  Answers are     *)
(* always applied while Y is hosted; nothing deduplicates.  An awaiting   *)
(* block with a derivation counted or a peer proof queued is held: never  *)
(* evicted; an arrival with every awaiting block held is refused.          *)
(*                                                                         *)
(* Environment: peers gossip blocks with real or failing proofs; a        *)
(* failing proof and a purge each spend one of MaxStrikes (a peer that    *)
(* sends a failing proof is disconnected).  At most MaxRestarts restarts, *)
(* MaxUnhosts unhost/re-host cycles (of Y, or with Grow of X and Y) and   *)
(* MaxEvicts pending evictions.  A restart loses jobs, counts, awaiting   *)
(* and pending blocks with their credits, and peer proofs; an unhost      *)
(* loses the same but the jobs, which may answer into the re-hosted       *)
(* level.  Carriers and tree blocks with their credits persist.            *)
(*                                                                         *)
(* With ParentsFetched only leaf blocks are pushed (by their author and,  *)
(* with PeerPush, by peers): a parent comes in only as the answer to the  *)
(* one ancestor request a block makes when it is promoted to pending     *)
(* with its parent unknown.  That request is asked once; an answer the node     *)
(* does not take is not asked again.  (The code asks only a block's       *)
(* source peer, so a locally submitted block asks nothing; the model lets *)
(* every promotion ask, as if each block had a live source.)               *)
(*                                                                         *)
(* Assumptions.  Converges is claimed only under these:                    *)
(*  (A1) no operator finality window, or only blocks within it (a block   *)
(*       past finality is declined, and nothing here weighs it);           *)
(*  (A3) pending-budget pressure on blocks the node cannot weigh yet      *)
(*       eventually leaves room: evictions of orphans (parent not in the  *)
(*       tree) and of blocks waiting on their index or timestamp are      *)
(*       bounded (MaxEvicts).  The budget evicts the largest-hash pending *)
(*       leaf and orphans never expire, so unbounded pressure can evict   *)
(*       such a block forever.  Any other pending block may be evicted    *)
(*       without bound: that none ever is (a block promoted above a       *)
(*       weighed parent is weighed in its step, before the budget runs)   *)
(*       is checked, not assumed;                                          *)
(*  (A4) failing proofs and purges (MaxStrikes), restarts (MaxRestarts)   *)
(*       and unhosts (MaxUnhosts) are bounded.                             *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    Cap,                \* awaiting capacity
    Grow,               \* parent is a child level: grinds grow, X unhostable
    PeerPush,           \* honest peers re-send each block with its real proof
    AuthorStopsOnCredit,\* the author stops at the first credit, not weighing
    DeferSettle,        \* a credited block may stay pending above a tree parent
    ParentsFetched,     \* only leaves are pushed; parents come by ancestor fetch
    IndexFetched,       \* a block may arrive without its children index
    MaxRestarts,
    MaxUnhosts,
    MaxEvicts,
    MaxStrikes,
    QBudget             \* the operator's total budget of queued peer proofs

Carriers == {"B1", "B2", "B3"}
Children == {"C1", "C2"}
Parent == [c \in Children |-> IF c = "C2" THEN "C1" ELSE "genesis"]
Commit == [b \in Carriers |-> IF b = "B3" THEN "C2" ELSE "C1"]
Grinds == {"g1", "g2", "g3", "g4", "g5"}
CarrierOf == [g \in Grinds |-> CASE g \in {"g1", "g2"} -> "B1"
                                 [] g = "g3" -> "B2"
                                 [] OTHER -> "B3"]
GrindsOf(b) == {g \in Grinds : CarrierOf[g] = b}
Meets == {"g1", "g3", "g4"}
\* What a peer may attach: a grind's proof (real only if it meets the
\* target and its carrier commits the block) or garbage.
PeerProofs == {"g2", "g3", "g4", "g5", "bogus"}
Real == [c \in Children |-> IF c = "C1" THEN "g3" ELSE "g4"]

\* A job: <<carrier, child, grinds owed at issue>>.
JobKeys == UNION {{<<b, Commit[b], G>> : G \in SUBSET GrindsOf(b) \ {{}}} : b \in Carriers}

ASSUME Cap \in Nat \ {0} /\ Grow \in BOOLEAN /\ PeerPush \in BOOLEAN
       /\ AuthorStopsOnCredit \in BOOLEAN /\ DeferSettle \in BOOLEAN
       /\ ParentsFetched \in BOOLEAN /\ IndexFetched \in BOOLEAN /\ QBudget \in Nat \ {0}

VARIABLES
    weighed,    \* carriers in the parent level's tree (persisted)
    cgr,        \* carrier -> its credited grinds (persisted, grows)
    status,     \* child -> "unknown" | "awaiting" | "pending" | "tree"
    credited,   \* child -> grinds credited (persisted only in the tree)
    dcred,      \* child -> grinds credited by a derivation (lost with credit)
    seen,       \* children ever credited here (what an author may watch)
    jobs,       \* JobKeys -> number in flight
    deriving,   \* child -> jobs counted since the last restart or unhost
    peerQ,      \* child -> peer proofs queued or in a check
    fetch,      \* pending blocks whose one ancestor request is unanswered
    idx,        \* child -> its children index: "held" | "asked" | "waiting"
    lack,       \* <<child, proof>> holes whose proof was dropped over budget
    honest,     \* honest peers connected (only blame disconnects them)
    hosted,     \* Y
    xHosted,    \* X (always TRUE without Grow)
    restarts, unhosts, evicts, strikes

vars == <<weighed, cgr, status, credited, dcred, seen, jobs, deriving, peerQ,
          fetch, idx, lack, honest, hosted, xHosted, restarts, unhosts, evicts, strikes>>

InTree(c) == status[c] = "tree"
Known(st, c) == st[c] # "unknown"
\* Grinds of weighed carriers committing c that meet c's target.
Full(c) == {g \in Meets : CarrierOf[g] \in weighed /\ g \in cgr[CarrierOf[g]] /\ Commit[CarrierOf[g]] = c}
\* Grinds any verified root carries for c: what a proof can show.
Verifiable(c) == {g \in Meets : Commit[CarrierOf[g]] = c}
Valid(c, p) == p \in Meets /\ Commit[CarrierOf[p]] = c
Proofs(b) == {g \in Meets : CarrierOf[g] = b}
Committers(c) == {b \in weighed : Commit[b] = c}
Awaiting(st) == {c \in Children : st[c] = "awaiting"}
\* A block a waiting or pending child names as parent is wanted too.
Wanted(c) == Committers(c) # {} \/ \E x \in Children : Parent[x] = c /\ status[x] \in {"awaiting", "pending"}

NoJobs == [k \in JobKeys |-> 0]
NoDeriving == [c \in Children |-> 0]
NoPeer == [c \in Children |-> {}]
AllHeld == [c \in Children |-> "held"]
\* Peer proofs queued or in a check, all sources together.
QSize(pq) == Cardinality(UNION {{<<c, p>> : p \in pq[c]} : c \in Children})
\* The blocks someone pushes until weighed.
Pushed == IF ParentsFetched THEN {c \in Children : ~\E x \in Children : Parent[x] = c} ELSE Children

\* Derivations for carriers in B whose block is known in st, of the grinds
\* not yet credited; a fully credited pair issues nothing.
DeriveKeys(st, B, cg) ==
    {<<b, Commit[b], cg[b] \ credited[Commit[b]]>> :
        b \in {x \in B : Known(st, Commit[x]) /\ cg[x] \ credited[Commit[x]] # {}}}
\* Trigger (b).
ArrivalKeys(st, arr) == DeriveKeys(st, {b \in weighed : Commit[b] \in arr}, cgr)
ArrivalJobs(st, arr) == ArrivalKeys(st, arr)
\* What issuing S puts in flight (nothing dedups).
Issued(js, S) == S
AddJobs(js, S) == [k \in JobKeys |-> IF k \in S THEN js[k] + 1 ELSE js[k]]
AddDeriving(dv, S) == [c \in Children |-> dv[c] + Cardinality({k \in S : k[2] = c})]

\* A pending block whose parent is in the tree and whose index is held is
\* weighed (twice: C1 then C2).
Settle1(st, ix) == [c \in Children |-> IF st[c] = "pending" /\ (Parent[c] = "genesis" \/ st[Parent[c]] = "tree")
                                           /\ ix[c] = "held"
                                        THEN "tree" ELSE st[c]]
Settle(st, ix) == Settle1(Settle1(st, ix), ix)

Holds(dv, pq, y) == dv[y] > 0 \/ pq[y] # {}

\* The status functions after c enters awaiting, evicting an awaiting
\* block that is not held if full; {} (refused) when every one is held.
Admit(st, dv, pq, c) ==
    IF Cardinality(Awaiting(st)) < Cap THEN {[st EXCEPT ![c] = "awaiting"]}
    ELSE {[x \in Children |-> IF x = c THEN "awaiting" ELSE IF x = v THEN "unknown" ELSE st[x]] :
            v \in {y \in Awaiting(st) : ~Holds(dv, pq, y)}}

\* Credit P at c (known in st), D of it derived; the first credit of an
\* awaiting block promotes it to pending, weighed once its parent is.
Promote(st, c) == IF DeferSettle THEN [st EXCEPT ![c] = "pending"] ELSE Settle([st EXCEPT ![c] = "pending"], idx)
Credit(st, c, P, D) ==
    /\ credited' = [credited EXCEPT ![c] = @ \cup P]
    /\ dcred' = [dcred EXCEPT ![c] = @ \cup D]
    /\ seen' = IF P # {} THEN seen \cup {c} ELSE seen
    /\ status' = IF P # {} /\ st[c] = "awaiting" THEN Promote(st, c) ELSE st
    \* With ParentsFetched, a promoted block asks once for its unknown parent.
    /\ fetch' = IF /\ ParentsFetched /\ st[c] = "awaiting" /\ P # {}
                   /\ Parent[c] # "genesis" /\ st[Parent[c]] = "unknown"
                THEN fetch \cup {c} ELSE fetch

\* What survives: blocks in kept keep their status and credits.
Durable(st) == {c \in Children : st[c] = "tree"}
Lose(kept) ==
    /\ status' = [c \in Children |-> IF c \in kept THEN status[c] ELSE "unknown"]
    /\ credited' = [c \in Children |-> IF c \in kept THEN credited[c] ELSE {}]
    /\ dcred' = [c \in Children |-> IF c \in kept THEN dcred[c] ELSE {}]
    /\ idx' = AllHeld

Init ==
    /\ weighed = {}
    /\ cgr = [b \in Carriers |-> {}]
    /\ status = [c \in Children |-> "unknown"]
    /\ credited = [c \in Children |-> {}]
    /\ dcred = [c \in Children |-> {}]
    /\ seen = {}
    /\ jobs = NoJobs
    /\ deriving = NoDeriving
    /\ peerQ = NoPeer
    /\ fetch = {}
    /\ idx = AllHeld
    /\ lack = {}
    /\ honest = TRUE
    /\ hosted = TRUE
    /\ xHosted = TRUE
    /\ restarts = 0 /\ unhosts = 0 /\ evicts = 0 /\ strikes = 0

\* Trigger (a): carrier b's grinds are now cg.
Retrigger(b, cg) ==
    IF hosted
      THEN LET S == Issued(jobs, DeriveKeys(status, {b}, cg))
           IN /\ jobs' = AddJobs(jobs, S)
              /\ deriving' = AddDeriving(deriving, S)
      ELSE UNCHANGED <<jobs, deriving>>

\* A carrier is weighed with its first credited grinds (at the root: all).
Weigh(b) ==
    /\ xHosted /\ b \notin weighed
    /\ \E G \in IF Grow THEN SUBSET GrindsOf(b) \ {{}} ELSE {GrindsOf(b)} :
         LET cg == [cgr EXCEPT ![b] = G]
         IN /\ weighed' = weighed \cup {b}
            /\ cgr' = cg
            /\ Retrigger(b, cg)
    /\ UNCHANGED <<status, credited, dcred, seen, peerQ, fetch, idx, lack, honest, hosted, xHosted, restarts, unhosts, evicts, strikes>>

\* A weighed X block is credited another grind: its work changed, so it
\* re-triggers like a weigh.
GrowGrind(b, g) ==
    /\ Grow /\ xHosted /\ b \in weighed /\ g \in GrindsOf(b) \ cgr[b]
    /\ LET cg == [cgr EXCEPT ![b] = @ \cup {g}]
       IN /\ cgr' = cg
          /\ Retrigger(b, cg)
    /\ UNCHANGED <<weighed, status, credited, dcred, seen, peerQ, fetch, idx, lack, honest, hosted, xHosted, restarts, unhosts, evicts, strikes>>

\* Unknown c enters awaiting (refused when Admit is empty), its children
\* index inline or asked of its announcer; its arrival derives (trigger (b)).
Arrive(c) ==
    \E st \in Admit(status, deriving, peerQ, c), ix \in IF IndexFetched THEN {"held", "asked"} ELSE {"held"} :
        LET S == Issued(jobs, ArrivalJobs(st, {c}))
        IN /\ status' = st
           /\ idx' = [x \in Children |-> IF x = c THEN ix ELSE IF st[x] = "unknown" THEN "held" ELSE idx[x]]
           /\ jobs' = AddJobs(jobs, S)
           /\ deriving' = AddDeriving(deriving, S)

\* Over the budget a proof is dropped without blame: its hole stays lacking.
Drop(c, p) == lack' = lack \cup {<<c, p>>} /\ UNCHANGED honest

\* Queue p for c within the operator's total budget, or drop it (a proof
\* already queued is the same proof, not another).
Offer(c, p) ==
    IF p \in peerQ[c] \/ QSize(peerQ) < QBudget
      THEN /\ peerQ' = [peerQ EXCEPT ![c] = @ \cup {p}]
           /\ lack' = lack \ {<<c, p>>}
           /\ UNCHANGED honest
      ELSE /\ UNCHANGED peerQ
           /\ Drop(c, p)

\* c is sent with proof p or none ("none").  A known block only queues a
\* new proof.  An unknown block without a proof is taken only if wanted.
\* A failing proof costs the adversary a strike.
Gossip(c, p) ==
    /\ hosted
    /\ LET bad == p # "none" /\ ~Valid(c, p)
       IN /\ bad => strikes < MaxStrikes
          /\ strikes' = IF bad THEN strikes + 1 ELSE strikes
    /\ IF Known(status, c)
         THEN /\ p # "none" /\ p \notin peerQ[c] /\ p \notin credited[c]
              /\ Offer(c, p)
              /\ UNCHANGED <<status, idx, jobs, deriving>>
         ELSE /\ p # "none" \/ Wanted(c)
              /\ Arrive(c)
              /\ IF p = "none" THEN UNCHANGED <<peerQ, lack, honest>> ELSE Offer(c, p)
    /\ UNCHANGED <<weighed, cgr, credited, dcred, seen, fetch, hosted, xHosted, restarts, unhosts, evicts>>

\* The author submits c to its own node or gossips it, until it is weighed.
AuthorPush(c) ==
    /\ c \in Pushed /\ ~InTree(c)
    /\ (AuthorStopsOnCredit => c \notin seen)
    /\ Gossip(c, "none")

\* An honest peer re-sends c with its real proof until it is weighed, but
\* not while its relay's hole is lacking here: it waits to be asked again.
PeerSend(c) == PeerPush /\ honest /\ c \in Pushed /\ ~InTree(c) /\ <<c, Real[c]>> \notin lack
               /\ Gossip(c, Real[c])

\* A tick re-asks a lacking proof hole: filled already, or sent again.
ReAskProof(c, p) ==
    /\ hosted /\ <<c, p>> \in lack
    /\ IF Known(status, c) /\ (p \in peerQ[c] \/ p \in credited[c])
         THEN /\ lack' = lack \ {<<c, p>>}
              /\ UNCHANGED <<weighed, cgr, status, credited, dcred, seen, jobs, deriving, peerQ, fetch, idx,
                             honest, hosted, xHosted, restarts, unhosts, evicts, strikes>>
         ELSE Gossip(c, p)

\* A pending block's children index is served: the step weighs what it can.
IndexServed(c) ==
    /\ status[c] = "pending" /\ idx[c] = "asked"
    /\ LET ix == [idx EXCEPT ![c] = "held"]
       IN /\ idx' = ix
          /\ status' = IF DeferSettle THEN status ELSE Settle(status, ix)
    /\ UNCHANGED <<weighed, cgr, credited, dcred, seen, jobs, deriving, peerQ, fetch, lack, honest, hosted, xHosted,
                   restarts, unhosts, evicts, strikes>>

\* A nil index answer: the announcer lacks what its header commits.  The
\* header and its credits are kept; it is asked of its next announcer, or
\* with none left waits for a tick.  Nobody is blamed.
NilKeeps(c) == idx' \in {[idx EXCEPT ![c] = "asked"], [idx EXCEPT ![c] = "waiting"]} /\ UNCHANGED <<status, credited, dcred>>
IndexNil(c) ==
    /\ status[c] = "pending" /\ idx[c] = "asked"
    /\ NilKeeps(c)
    /\ UNCHANGED <<weighed, cgr, seen, jobs, deriving, peerQ, fetch, lack, honest, hosted, xHosted,
                   restarts, unhosts, evicts, strikes>>

\* A tick re-asks the stream hole of a header waiting on nobody.
ReAskIndex(c) ==
    /\ status[c] = "pending" /\ idx[c] = "waiting"
    /\ idx' = [idx EXCEPT ![c] = "asked"]
    /\ UNCHANGED <<weighed, cgr, status, credited, dcred, seen, jobs, deriving, peerQ, fetch, lack, honest, hosted,
                   xHosted, restarts, unhosts, evicts, strikes>>

\* A peer's proof is judged on its own: it verifies against its root,
\* whether or not this node weighed the carrier.
CheckPeerProof(c, p) ==
    /\ p \in peerQ[c]
    /\ peerQ' = [peerQ EXCEPT ![c] = @ \ {p}]
    /\ IF Valid(c, p) /\ Known(status, c)
         THEN Credit(status, c, {p}, {})
         ELSE UNCHANGED <<status, credited, dcred, seen, fetch>>
    /\ UNCHANGED <<weighed, cgr, jobs, deriving, idx, lack, honest, hosted, xHosted, restarts, unhosts, evicts, strikes>>

\* The ancestor answer: x's parent, without proofs, taken as any proofless
\* arrival is (only if wanted), else dropped and never asked again.
ParentAnswer(x) ==
    /\ x \in fetch
    /\ fetch' = fetch \ {x}
    /\ LET c == Parent[x]
       IN IF /\ hosted /\ status[x] = "pending" /\ ~Known(status, c) /\ Wanted(c)
             /\ Admit(status, deriving, peerQ, c) # {}
            THEN Arrive(c)
            ELSE UNCHANGED <<status, idx, jobs, deriving>>
    /\ UNCHANGED <<weighed, cgr, credited, dcred, seen, peerQ, lack, honest, hosted, xHosted, restarts, unhosts, evicts, strikes>>

Purge ==
    /\ peerQ # NoPeer /\ strikes < MaxStrikes
    /\ strikes' = strikes + 1
    /\ peerQ' = NoPeer
    /\ UNCHANGED <<weighed, cgr, status, credited, dcred, seen, jobs, deriving, fetch, idx, lack, honest, hosted, xHosted,
                   restarts, unhosts, evicts>>

\* Whether an answer is applied, given the count before it is taken off.
Applies(dv, c) == TRUE

Answer(k) ==
    LET b == k[1]
        c == k[2]
        P == k[3] \cap Proofs(b)
        js1 == [jobs EXCEPT ![k] = @ - 1]
        dv1 == [deriving EXCEPT ![c] = IF @ > 0 THEN @ - 1 ELSE 0]
    IN
    /\ jobs[k] > 0
    /\ jobs' = js1
    /\ IF ~hosted \/ ~Applies(deriving, c)
         THEN /\ deriving' = IF hosted THEN dv1 ELSE deriving
              /\ UNCHANGED <<status, credited, dcred, seen, fetch>>
         ELSE /\ deriving' = dv1
              /\ IF Known(status, c)
                   THEN Credit(status, c, P, P)
                   ELSE UNCHANGED <<status, credited, dcred, seen, fetch>>
    /\ UNCHANGED <<weighed, cgr, peerQ, idx, lack, honest, hosted, xHosted, restarts, unhosts, evicts, strikes>>

\* Blocks the node cannot weigh yet: orphans, and blocks waiting on their
\* index or (with DeferSettle) their timestamp.  Only their evictions are
\* bounded (A3).
Unweighable(v) == (Parent[v] # "genesis" /\ status[Parent[v]] # "tree") \/ idx[v] # "held" \/ DeferSettle

\* The pending budget evicts a pending leaf (the code: the largest hash),
\* once the step's headers are processed.  Any other pending block may be
\* evicted without bound: none is ever pending here (CreditHeld).
EvictPending ==
    /\ \E v \in {c \in Children : status[c] = "pending"} :
         /\ ~\E x \in Children : Parent[x] = v /\ status[x] = "pending"
         /\ Unweighable(v) => evicts < MaxEvicts
         /\ status' = [status EXCEPT ![v] = "unknown"]
         /\ credited' = [credited EXCEPT ![v] = {}]
         /\ dcred' = [dcred EXCEPT ![v] = {}]
         /\ idx' = [idx EXCEPT ![v] = "held"]
         /\ evicts' = IF Unweighable(v) THEN evicts + 1 ELSE evicts
    /\ UNCHANGED <<weighed, cgr, seen, jobs, deriving, peerQ, fetch, lack, honest, hosted, xHosted, restarts, unhosts, strikes>>

\* With DeferSettle: pending blocks whose parent is in the tree are weighed.
SettleStep ==
    /\ hosted /\ Settle(status, idx) # status
    /\ status' = Settle(status, idx)
    /\ UNCHANGED <<weighed, cgr, credited, dcred, seen, jobs, deriving, peerQ, fetch, idx, lack, honest, hosted, xHosted,
                   restarts, unhosts, evicts, strikes>>

\* The boot pass: every block in the tree arrives.
BootKeys(st) == ArrivalKeys(st, {c \in Children : st[c] = "tree"})

Restart ==
    /\ restarts < MaxRestarts
    /\ restarts' = restarts + 1
    /\ Lose(Durable(status))
    /\ peerQ' = NoPeer
    /\ fetch' = {}
    /\ lack' = {}
    /\ LET S == IF hosted THEN Issued(NoJobs, BootKeys(status)) ELSE {}
       IN /\ jobs' = AddJobs(NoJobs, S)
          /\ deriving' = AddDeriving(NoDeriving, S)
    /\ UNCHANGED <<weighed, cgr, seen, honest, hosted, xHosted, unhosts, evicts, strikes>>

\* Unhost Y, or (x, with Grow) X with its descendant Y.
Unhost(x) ==
    /\ unhosts < MaxUnhosts
    /\ IF x THEN Grow /\ xHosted ELSE hosted
    /\ unhosts' = unhosts + 1
    /\ xHosted' = IF x THEN FALSE ELSE xHosted
    /\ hosted' = FALSE
    /\ IF hosted
         THEN /\ Lose(Durable(status))
              /\ deriving' = NoDeriving
              /\ peerQ' = NoPeer
              /\ fetch' = {}
              /\ lack' = {}
         ELSE UNCHANGED <<status, credited, dcred, idx, deriving, peerQ, fetch, lack>>
    /\ UNCHANGED <<weighed, cgr, seen, jobs, honest, restarts, evicts, strikes>>

RehostX ==
    /\ ~xHosted
    /\ xHosted' = TRUE
    /\ UNCHANGED <<weighed, cgr, status, credited, dcred, seen, jobs, deriving, peerQ, fetch, idx, lack, honest, hosted,
                   restarts, unhosts, evicts, strikes>>

Rehost ==
    /\ ~hosted /\ xHosted
    /\ hosted' = TRUE
    /\ LET S == Issued(jobs, BootKeys(status))
       IN /\ jobs' = AddJobs(jobs, S)
          /\ deriving' = AddDeriving(NoDeriving, S)
    /\ UNCHANGED <<weighed, cgr, status, credited, dcred, seen, peerQ, fetch, idx, lack, honest, xHosted,
                   restarts, unhosts, evicts, strikes>>

Next ==
    \/ \E b \in Carriers : Weigh(b)
    \/ \E b \in Carriers, g \in Grinds : GrowGrind(b, g)
    \/ \E c \in Children, p \in PeerProofs \cup {"none"} : Gossip(c, p)
    \/ \E c \in Children : AuthorPush(c)
    \/ \E c \in Children, p \in PeerProofs : CheckPeerProof(c, p)
    \/ Purge
    \/ \E k \in JobKeys : Answer(k)
    \/ EvictPending
    \/ SettleStep
    \/ \E x \in Children : ParentAnswer(x)
    \/ \E c \in Children, p \in PeerProofs : ReAskProof(c, p)
    \/ \E c \in Children : IndexServed(c) \/ IndexNil(c) \/ ReAskIndex(c)
    \/ Restart \/ Unhost(TRUE) \/ Unhost(FALSE) \/ RehostX \/ Rehost

\* Every job answers and every queued proof is checked; the author pushes
\* each block until it is weighed (and honest peers too, with PeerPush);
\* an unhosted level is eventually hosted again; a block pending above a
\* tree parent is weighed; an ancestor request is answered; a tick re-asks
\* every lacking hole; an index asked again and again is served.
Fairness ==
    /\ \A k \in JobKeys : WF_vars(Answer(k))
    /\ \A c \in Children, p \in PeerProofs : WF_vars(CheckPeerProof(c, p)) /\ WF_vars(ReAskProof(c, p))
    /\ \A c \in Children : WF_vars(AuthorPush(c)) /\ WF_vars(PeerSend(c)) /\ WF_vars(ParentAnswer(c))
    /\ \A c \in Children : WF_vars(ReAskIndex(c)) /\ SF_vars(IndexServed(c))
    /\ WF_vars(RehostX) /\ WF_vars(Rehost) /\ WF_vars(SettleStep)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------

TypeOK ==
    /\ weighed \subseteq Carriers
    /\ cgr \in [Carriers -> SUBSET Grinds]
    /\ status \in [Children -> {"unknown", "awaiting", "pending", "tree"}]
    /\ credited \in [Children -> SUBSET Grinds]
    /\ dcred \in [Children -> SUBSET Grinds]
    /\ jobs \in [JobKeys -> Nat]
    /\ deriving \in [Children -> Nat]
    /\ peerQ \in [Children -> SUBSET PeerProofs]
    /\ fetch \subseteq Children
    /\ idx \in [Children -> {"held", "asked", "waiting"}]
    /\ lack \subseteq Children \X PeerProofs
    /\ honest \in BOOLEAN
    /\ Cardinality(Awaiting(status)) <= Cap
    /\ QSize(peerQ) <= QBudget

\* Every credit is a grind some verified root carries for the block and
\* meets its target, whether or not this node weighed its carrier.
Safety == \A c \in Children : credited[c] \subseteq Verifiable(c)

\* Every derived credit is a grind of a weighed carrier committing the
\* block that meets its target.
DerivedSafety == \A c \in Children : dcred[c] \subseteq credited[c] /\ dcred[c] \subseteq Full(c)

\* Credit sits exactly on pending and tree blocks; a block is in the tree
\* only above its parent, and (without DeferSettle) pending with its index
\* held only while its parent is not: no block the node can weigh is left
\* for the budget to evict.
CreditHeld ==
    \A c \in Children :
        /\ (credited[c] # {}) = (status[c] \in {"pending", "tree"})
        /\ ~DeferSettle /\ status[c] = "pending" /\ idx[c] = "held" => Parent[c] # "genesis" /\ status[Parent[c]] # "tree"
        /\ status[c] = "tree" => Parent[c] = "genesis" \/ status[Parent[c]] = "tree"

\* With nothing in flight, every credited block holds all it is owed.
QuiescentFull ==
    (hosted /\ jobs = NoJobs) =>
        \A c \in Children : status[c] \in {"pending", "tree"} => Full(c) \subseteq credited[c]

\* A block whose every ancestor up to genesis is owed work can be weighed.
Reach(c) == Full(c) # {} /\ (Parent[c] = "genesis" \/ Full(Parent[c]) # {})

\* In the end every grind of a weighed carrier that meets its block's
\* target is credited, and every block that can be weighed is.
Converges == <>[](\A c \in Children : Full(c) \subseteq credited[c] /\ (Reach(c) => InTree(c)))

\* With honest peers pushing real proofs, every block ends in the tree.
PeerConverges == <>[](\A c \in Children : InTree(c))

\* Witness, must FAIL: some credit is reachable.
NoCredit == \A c \in Children : credited[c] = {}

=============================================================================
