---------------------- MODULE TraceDerivedChildGrinds -----------------------
(***************************************************************************)
(* Trace validation for derived child grinds: replay events recorded from *)
(* lattice-node's DerivedChildGrindTests (its Host harness, one hosted    *)
(* level Y) through DerivedChildGrinds, one action per event.              *)
(*                                                                         *)
(* - The trace's fixture replaces the spec's (Carriers, Children, Commit, *)
(*   Grinds, Meets, ...; MCTrace overrides them) and its first state is   *)
(*   the host's when tracing began: carriers already weighed and blocks   *)
(*   already in the tree, nothing in flight.                               *)
(* - Each event must be the named spec action with the logged choices     *)
(*   (a weigh's grinds, an arrival's evicted block); a gossip the code    *)
(*   refused must be one the spec cannot take.  If an event is not a      *)
(*   step, TLC reports a deadlock at it.                                   *)
(* - One host step may be several actions (a check, then a purge as the   *)
(*   peer is disconnected): only the last event of a step carries the     *)
(*   state after it.  There each child's status, credits, derivation      *)
(*   count, queued peer proofs, and every derivation in flight must equal *)
(*   the spec's (while Y is hosted; the jobs always).                      *)
(* - A "tamper" event is a test reaching into the code's state outside    *)
(*   any step: the spec takes the logged status, credits and counts.      *)
(***************************************************************************)
EXTENDS DerivedChildGrinds, Sequences

CONSTANTS
    Trace,   \* Seq of events (see Replay), each with checked and after
    TInit    \* [hosted, weighed, cgr, status, credited]

VARIABLE i   \* next event to replay

traceVars == <<vars, i>>

Key(e) == <<e.carrier, e.child, e.grinds>>

Replay(e) ==
    CASE e.kind = "weigh" -> Weigh(e.carrier) /\ cgr'[e.carrier] = e.grinds
      [] e.kind = "grow" -> GrowGrind(e.carrier, e.grind)
      [] e.kind = "gossip" ->
           IF e.accepted
             THEN /\ Gossip(e.child, e.proof)
                  /\ \A v \in Children \ {e.child} :
                        status'[v] = IF v = e.victim THEN "unknown" ELSE status[v]
             ELSE ~ENABLED Gossip(e.child, e.proof) /\ UNCHANGED vars
      [] e.kind = "check" -> CheckPeerProof(e.child, e.proof)
      [] e.kind = "purge" -> Purge
      [] e.kind = "answer" -> Key(e) \in JobKeys /\ Answer(Key(e))
      [] e.kind = "evictPending" -> EvictPending /\ status'[e.child] = "unknown"
      [] e.kind = "restart" -> Restart
      [] e.kind = "unhost" -> Unhost(e.x)
      [] e.kind = "rehostX" -> RehostX
      [] e.kind = "rehost" -> Rehost
      [] e.kind = "internal" -> UNCHANGED vars
      [] e.kind = "tamper" ->
           /\ status' = e.after.status
           /\ credited' = e.after.credited
           /\ dcred' = [c \in Children |-> dcred[c] \cap e.after.credited[c]]
           /\ deriving' = e.after.deriving
           /\ UNCHANGED <<weighed, cgr, seen, jobs, peerQ, hosted, xHosted, restarts, unhosts, evicts, strikes>>

TraceInit ==
    /\ weighed = TInit.weighed
    /\ cgr = TInit.cgr
    /\ status = TInit.status
    /\ credited = TInit.credited
    /\ dcred = [c \in Children |-> {}]
    /\ seen = {c \in Children : TInit.credited[c] # {}}
    /\ jobs = NoJobs
    /\ deriving = NoDeriving
    /\ peerQ = NoPeer
    /\ hosted = TInit.hosted
    /\ xHosted = TRUE
    /\ restarts = 0 /\ unhosts = 0 /\ evicts = 0 /\ strikes = 0
    /\ i = 1

TraceNext ==
    \/ /\ i <= Len(Trace)
       /\ Replay(Trace[i])
       /\ i' = i + 1
    \* Replayed every event: stutter, so the end is not a deadlock.
    \/ /\ i = Len(Trace) + 1
       /\ UNCHANGED traceVars

TraceSpec == TraceInit /\ [][TraceNext]_traceVars

\* The code's state after event i - 1 equals the spec's, one invariant per
\* part so a failure names what differs.  Every choice is pinned by the
\* event, so each state has one successor and these can be invariants.
Last == Trace[i - 1]
Checked == i > 1 /\ Last.checked
Count(S, k) == IF \E p \in S : p[1] = k THEN (CHOOSE p \in S : p[1] = k)[2] ELSE 0

HostedMatches == Checked => hosted = Last.after.hosted
StatusMatches == Checked /\ hosted => status = Last.after.status
CreditedMatches == Checked /\ hosted => credited = Last.after.credited
DerivingMatches == Checked /\ hosted => deriving = Last.after.deriving
PeerQMatches == Checked /\ hosted => peerQ = Last.after.peerQ
JobsMatch ==
    Checked =>
        /\ \A p \in Last.after.jobs : p[1] \in JobKeys
        /\ \A k \in JobKeys : jobs[k] = Count(Last.after.jobs, k)

=============================================================================
