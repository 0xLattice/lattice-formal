--------------------------- MODULE TraceHierarchy ---------------------------
(***************************************************************************)
(* Trace validation for two levels: replay events recorded from Lattice's  *)
(* parent and child ChainTrees through Hierarchy, one event per step.      *)
(*                                                                         *)
(* - Each event must be a spec step with the same accept/refuse; a child   *)
(*   validation refused for continuity must be one the spec holds.  If an  *)
(*   event is not a step, TLC reports a deadlock at it.                    *)
(* - After each event, on both chains, the canonical tip, act-on tip and   *)
(*   every held block's weight (attributed runs included) must equal the   *)
(*   spec's, and so must every held child block's continuity.             *)
(***************************************************************************)
EXTENDS Hierarchy, Sequences

CONSTANT Trace   \* Seq of [kind, ch, block, grind, qty, accepted, reason, cause, after]

VARIABLE i       \* next event to replay

traceVars == <<vars, i>>

ObsOf(e) == [ch |-> e.ch, g |-> e.grind, b |-> e.block, q |-> e.qty]

\* A repeated observation is a no-op in the spec.
ObserveAgain(o) == IF o \in delivered THEN UNCHANGED vars ELSE Observe(o)

\* A child exclusion names its cause: a failed transition, which is a
\* verdict first (§5.3), else an invalid anchor.
CauseMatches(e) ==
    e.ch # "P" =>
        e.cause = IF ~Valid[e.block] THEN "transition" ELSE "continuity"

Replay(e) ==
    CASE e.kind = "admit" ->
           IF e.accepted THEN Admit(ObsOf(e))
           ELSE ~ENABLED Admit(ObsOf(e)) /\ UNCHANGED vars
      [] e.kind = "observe" ->
           \* Accepted exactly when the spec's state changes; refused as
           \* located elsewhere exactly when the spec holds it elsewhere.
           /\ e.reason = "grindElsewhere" <=> loc[e.ch][e.grind] \notin {None, e.block}
           /\ ObserveAgain(ObsOf(e))
           /\ e.accepted = (<<loc', qty'>> # <<loc, qty>>)
      [] e.kind = "validate" ->
           IF e.accepted THEN ValidateOk(e.ch, e.block)
           ELSE IF e.reason = "continuity"
                \* Not proven here: the spec holds it too.
                THEN /\ CanExecute(e.ch, e.block)
                     /\ Verdict(e.ch, e.block) = "held"
                     /\ UNCHANGED vars
                ELSE ~ENABLED ValidateOk(e.ch, e.block) /\ UNCHANGED vars
      [] e.kind = "exclude" ->
           /\ CauseMatches(e)
           /\ IF e.accepted THEN Exclude(e.ch, e.block)
              ELSE IF e.reason = "rootExclusion"
                \* An invalid root kept because no other root executed.
                THEN /\ CanExecute(e.ch, e.block)
                     /\ Verdict(e.ch, e.block) = "invalid"
                     /\ e.block \in Roots(e.ch)
                     /\ \A r \in Roots(e.ch) \ {e.block} : r \notin validated[e.ch]
                     /\ UNCHANGED vars
                ELSE ~ENABLED Exclude(e.ch, e.block) /\ UNCHANGED vars

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

CanonicalTipMatches ==
    i > 1 => \A ch \in Chains : CanonicalTip(ch) = After[ch].canonicalTip
ValidatedTipMatches ==
    i > 1 => \A ch \in Chains : ValidatedTip(ch) = After[ch].validatedTip
WeightsMatch ==
    i > 1 =>
        \A ch \in Chains :
            /\ DOMAIN After[ch].weights = weighed[ch]
            /\ \A b \in weighed[ch] : TrueCumWork(ch, b) = After[ch].weights[b]
ContinuityMatches ==
    i > 1 =>
        /\ DOMAIN After["C"].continuity = weighed["C"]
        /\ \A b \in weighed["C"] : Continuity(b) = After["C"].continuity[b]

=============================================================================
