--------------------------- MODULE TraceForkChoice ---------------------------
(***************************************************************************)
(* Trace validation: replay a fact sequence recorded from the Lattice      *)
(* implementation through ForkChoice, one event per step.                  *)
(*                                                                         *)
(* - Each event must be a step of the spec, and the implementation's       *)
(*   accept/refuse must agree with whether the spec allows it.  If not, no *)
(*   step is enabled and TLC reports a deadlock at that event.             *)
(* - After each event, the implementation's canonical tip, validated tip,  *)
(*   and every held block's subtree and prefix work must equal the spec's  *)
(*   (the *Matches invariants).                                            *)
(***************************************************************************)
EXTENDS ForkChoice, Sequences

CONSTANT Trace   \* Seq of [kind, block, grind, qty, accepted, after]

VARIABLE i       \* next event to replay

N == CHOOSE n \in Nodes : TRUE

traceVars == <<vars, i>>

\* An implementation admit is one batch: the block and its grind's work.
\* In the spec that is Observe then Admit; this is their composition.
AdmitWithWork(o) ==
    /\ o.b \notin weighed[N]
    /\ Parent[o.b] \in weighed[N] \cup {None}
    /\ loc[N][o.g] \in {None, o.b}
    /\ delivered' = [delivered EXCEPT ![N] = @ \cup {o}]
    /\ loc'       = [loc EXCEPT ![N][o.g] = o.b]
    /\ qty'       = [qty EXCEPT ![N][o.g] = IF o.q > @ THEN o.q ELSE @]
    /\ weighed'   = [weighed EXCEPT ![N] = @ \cup {o.b}]
    /\ UNCHANGED <<validated, excluded>>

\* A repeated observation is a no-op in the spec.
ObserveAgain(o) == IF o \in delivered[N] THEN UNCHANGED vars ELSE Observe(N, o)

Replay(e) ==
    LET o == [g |-> e.grind, b |-> e.block, q |-> e.qty]
    IN  CASE e.kind = "admit" ->
               IF e.accepted THEN AdmitWithWork(o)
               ELSE ~ENABLED AdmitWithWork(o) /\ UNCHANGED vars
          [] e.kind = "observe" ->
               \* Accepted exactly when the spec's state changes.
               /\ ObserveAgain(o)
               /\ e.accepted = (<<loc', qty'>> # <<loc, qty>>)
          [] e.kind = "validate" ->
               IF e.accepted THEN ValidateOk(N, e.block)
               ELSE ~ENABLED ValidateOk(N, e.block) /\ UNCHANGED vars
          [] e.kind = "exclude" ->
               IF e.accepted THEN Exclude(N, e.block)
               ELSE ~ENABLED Exclude(N, e.block) /\ UNCHANGED vars

TraceInit == Init /\ i = 1

TraceNext ==
    \/ /\ i <= Len(Trace)
       /\ Replay(Trace[i])
       /\ i' = i + 1
    \* Replayed every event: stutter, so the end is not a deadlock.
    \/ /\ i = Len(Trace) + 1
       /\ UNCHANGED traceVars

TraceSpec == TraceInit /\ [][TraceNext]_traceVars

\* The implementation's outputs after event i - 1 equal the spec's, one
\* invariant per output so a failure names what differs.
After == Trace[i - 1].after

CanonicalTipMatches == i > 1 => CanonicalTip(N) = After.canonicalTip
ValidatedTipMatches == i > 1 => ValidatedTip(N) = After.validatedTip
WeightsMatch ==
    i > 1 =>
        /\ DOMAIN After.weights = weighed[N]
        /\ \A b \in weighed[N] : TrueCumWork(N, b) = After.weights[b]
CumulativeMatches ==
    i > 1 =>
        /\ DOMAIN After.cumulative = weighed[N]
        /\ \A b \in weighed[N] : CumulativeWork(N, b) = After.cumulative[b]

=============================================================================
