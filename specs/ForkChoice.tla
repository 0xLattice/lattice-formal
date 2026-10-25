----------------------------- MODULE ForkChoice -----------------------------
(***************************************************************************)
(* Single-chain Lattice fork choice, modelled from the normative spec       *)
(* (Lattice docs/spec.md §9.1-9.4 and §9.9), not from the implementation.   *)
(*                                                                         *)
(* Each node receives the same universe of immutable facts (grind          *)
(* observations, headers, bodies) in any order and derives two             *)
(* projections from them:                                                  *)
(*   CanonicalTip - heaviest selectable path over pure-work weights        *)
(*   ValidatedTip - heaviest validated path, the tip a node acts on        *)
(*                                                                         *)
(* The block tree, each block's validity verdict, and body availability    *)
(* are constants: they are facts about immutable bytes, so every node      *)
(* would compute the same verdict.                                         *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    Nodes,      \* nodes that independently receive the facts
    Blocks,     \* every block that could ever be admitted
    None,       \* "no block": a root's parent, the tip of an empty chain
    Parent,     \* Blocks -> Blocks \cup {None}; a static tree
    CidRank,    \* Blocks -> Nat, injective; smaller = lexicographically smaller CID
    Grinds,     \* grind identities (root CIDs)
    Obs,        \* observations [g |-> grind, b |-> location, q |-> quantity]
    Valid,      \* Blocks -> BOOLEAN; the deterministic verdict of executing b
    Available,  \* blocks whose bodies can be obtained (all others never arrive)
    ExpectedCanonical, ExpectedValidated  \* hand-computed answers (oracle)

ASSUME /\ None \notin Blocks
       /\ \A b \in Blocks : Parent[b] \in Blocks \cup {None}
       /\ \A x, y \in Blocks : x # y => CidRank[x] # CidRank[y]
       /\ \A o \in Obs : o.g \in Grinds /\ o.b \in Blocks /\ o.q \in Nat \ {0}
       /\ Available \subseteq Blocks

VARIABLES
    delivered,  \* delivered[n] : observations n has seen
    loc,        \* loc[n][g]    : g's located block at n, or None
    qty,        \* qty[n][g]    : strongest quantity n has verified for g
    weighed,    \* weighed[n]   : admitted (accepted) blocks
    validated,  \* validated[n] : executed blocks whose post-state matched
    excluded    \* excluded[n]  : blocks with a recorded invalidity exclusion

vars == <<delivered, loc, qty, weighed, validated, excluded>>

Roots == {b \in Blocks : Parent[b] = None}

RECURSIVE AncOrSelf(_)
AncOrSelf(b) == IF b = None THEN {} ELSE {b} \cup AncOrSelf(Parent[b])

-----------------------------------------------------------------------------
(* Work algebra (§9.1, §9.2).  A grind has one location per chain, so the  *)
(* union-by-max of a subtree's measures is the sum of each located grind's *)
(* strongest quantity.                                                     *)

RECURSIVE SumQty(_, _)
SumQty(n, G) ==
    IF G = {} THEN 0
    ELSE LET g == CHOOSE x \in G : TRUE IN qty[n][g] + SumQty(n, G \ {g})

\* Only connected (weighed) locations contribute; a staged location whose
\* block is not admitted is durable but not routed (§9.1).
Subtree(n, b) == {x \in weighed[n] : b \in AncOrSelf(x)}

TrueCumWork(n, b) ==
    SumQty(n, {g \in Grinds : loc[n][g] \in Subtree(n, b)})

\* §9.4: greatest trueCumWork wins; exact tie -> smaller CID.
Better(n, x, y) ==
    \/ TrueCumWork(n, x) > TrueCumWork(n, y)
    \/ /\ TrueCumWork(n, x) = TrueCumWork(n, y)
       /\ CidRank[x] < CidRank[y]

Best(n, S) == CHOOSE x \in S : \A y \in S \ {x} : Better(n, x, y)

\* Descend from the best eligible root, at each fork taking the best
\* eligible child, stopping where no child is eligible.
RECURSIVE Descend(_, _, _)
Descend(n, b, E) ==
    LET C == {c \in E : Parent[c] = b}
    IN  IF C = {} THEN b ELSE Descend(n, Best(n, C), E)

TipOver(n, E) ==
    IF Roots \cap E = {} THEN None ELSE Descend(n, Best(n, Roots \cap E), E)

\* §9.9: "the canonical descent never steps into an excluded block".
Selectable(n) == {b \in weighed[n] : AncOrSelf(b) \cap excluded[n] = {}}

CanonicalTip(n) == TipOver(n, Selectable(n))

\* §9.9: "at each fork it follows the heaviest child that is validated
\* (heaviest by the whole subtree's work, unvalidated descendants included),
\* and stops where no child is validated."
ValidatedTip(n) == TipOver(n, validated[n])

-----------------------------------------------------------------------------
(* Actions.  Each is one immutable fact arriving at one node.              *)

\* A grind observation.  First location wins; a conflicting location is
\* rejected atomically (§9.1).  Repeated observations ratchet the quantity.
Observe(n, o) ==
    /\ o \notin delivered[n]
    /\ delivered' = [delivered EXCEPT ![n] = @ \cup {o}]
    /\ IF loc[n][o.g] \in {None, o.b}
          THEN /\ loc' = [loc EXCEPT ![n][o.g] = o.b]
               /\ qty' = [qty EXCEPT ![n][o.g] = IF o.q > @ THEN o.q ELSE @]
          ELSE UNCHANGED <<loc, qty>>
    /\ UNCHANGED <<weighed, validated, excluded>>

\* Header / genesis admission (§9.9): parent held (excluded or not, so roots
\* need none) and the block's own work verifies.
Admit(n, b) ==
    /\ b \notin weighed[n]
    /\ Parent[b] \in weighed[n] \cup {None}
    /\ \E g \in Grinds : loc[n][g] = b
    /\ weighed' = [weighed EXCEPT ![n] = @ \cup {b}]
    /\ UNCHANGED <<delivered, loc, qty, validated, excluded>>

\* Execution needs the body and the parent's validated post-state.  This
\* allows eager validation; the spec's lazy validation is a subset of these
\* behaviours.
CanExecute(n, b) ==
    /\ b \in weighed[n] \ (validated[n] \cup excluded[n])
    /\ b \in Available
    /\ Parent[b] \in validated[n] \cup {None}

ValidateOk(n, b) ==
    /\ CanExecute(n, b)
    /\ Valid[b]
    /\ validated' = [validated EXCEPT ![n] = @ \cup {b}]
    /\ UNCHANGED <<delivered, loc, qty, weighed, excluded>>

\* A genesis root may be excluded only while the chain has ANOTHER executed
\* root; otherwise the verdict is not recorded at all (§9.9).
Exclude(n, b) ==
    /\ CanExecute(n, b)
    /\ ~Valid[b]
    /\ b \in Roots => \E r \in Roots \ {b} : r \in validated[n]
    /\ excluded' = [excluded EXCEPT ![n] = @ \cup {b}]
    /\ UNCHANGED <<delivered, loc, qty, weighed, validated>>

Init ==
    /\ delivered = [n \in Nodes |-> {}]
    /\ loc       = [n \in Nodes |-> [g \in Grinds |-> None]]
    /\ qty       = [n \in Nodes |-> [g \in Grinds |-> 0]]
    /\ weighed   = [n \in Nodes |-> {}]
    /\ validated = [n \in Nodes |-> {}]
    /\ excluded  = [n \in Nodes |-> {}]

NodeNext(n) ==
    \/ \E o \in Obs : Observe(n, o)
    \/ \E b \in Blocks : Admit(n, b) \/ ValidateOk(n, b) \/ Exclude(n, b)

Next == \E n \in Nodes : NodeNext(n)

Spec == Init /\ [][Next]_vars /\ \A n \in Nodes : WF_vars(NodeNext(n))

-----------------------------------------------------------------------------
(* Properties.                                                             *)

TypeOK ==
    /\ \A n \in Nodes :
        /\ delivered[n] \subseteq Obs
        /\ weighed[n] \subseteq Blocks
        /\ validated[n] \subseteq weighed[n]
        /\ excluded[n] \subseteq weighed[n]
    /\ loc \in [Nodes -> [Grinds -> Blocks \cup {None}]]
    /\ qty \in [Nodes -> [Grinds -> Nat]]

\* Verdicts are deterministic and never contradict each other: an executed
\* block is never later excluded (§9.9).
VerdictsSound ==
    \A n \in Nodes :
        /\ validated[n] \cap excluded[n] = {}
        /\ \A b \in validated[n] : Valid[b]
        /\ \A b \in excluded[n] : ~Valid[b]

\* §9.9: nothing at or below an excluded block is extended or attested, so
\* nothing there is ever executed.
NothingValidatedBelowExcluded ==
    \A n \in Nodes : \A b \in validated[n] : AncOrSelf(b) \cap excluded[n] = {}

\* §12.3.3-4: the tip's whole path is admitted and hangs from one root.
\* §9.9: a node acts only on a path validated from genesis, and nothing at
\* or below an excluded block is ever the tip.
TipsWellFormed ==
    \A n \in Nodes :
        /\ ValidatedTip(n) # None =>
               /\ AncOrSelf(ValidatedTip(n)) \subseteq validated[n]
               /\ Cardinality(AncOrSelf(ValidatedTip(n)) \cap Roots) = 1
        /\ CanonicalTip(n) # None =>
               /\ AncOrSelf(CanonicalTip(n)) \subseteq weighed[n]
               /\ AncOrSelf(CanonicalTip(n)) \cap excluded[n] = {}

\* Missing bodies are the only reason the two tips differ: once the whole
\* canonical path is validated, the node acts on exactly the canonical tip.
AgreeWhenValidated ==
    \A n \in Nodes :
        /\ CanonicalTip(n) # None
        /\ AncOrSelf(CanonicalTip(n)) \subseteq validated[n]
        => ValidatedTip(n) = CanonicalTip(n)

\* A node is quiescent once it has every fact and nothing more can happen.
Quiescent(n) == delivered[n] = Obs /\ ~ENABLED NodeNext(n)

\* Convergence: nodes holding the same facts derive the same weights and
\* select the same tips, whatever order the facts arrived in (§9.4; §9.8:
\* replay "reconstructs exact measures").  Weights are compared directly: a
\* weight that depends on arrival order is a fault even where it happens not
\* to move this model's tips.
Convergence ==
    \A m, n \in Nodes :
        Quiescent(m) /\ Quiescent(n) =>
            /\ \A b \in Blocks : TrueCumWork(m, b) = TrueCumWork(n, b)
            /\ CanonicalTip(m) = CanonicalTip(n)
            /\ ValidatedTip(m) = ValidatedTip(n)

\* Independent oracle: the tips a human computed from the rules for this
\* model.  Catches a rule that is consistent but wrong (e.g. a reversed
\* tie-break), which no consistency invariant can.
ExpectedAnswer ==
    \A n \in Nodes :
        Quiescent(n) =>
            /\ CanonicalTip(n) = ExpectedCanonical
            /\ ValidatedTip(n) = ExpectedValidated

\* §9.1/§12.5.4: work is monotone.  No step lowers any block's weight;
\* in particular an exclusion removes no weight (§9.9, "work weighs").
WorkMonotone ==
    [][\A n \in Nodes, b \in Blocks :
            TrueCumWork(n, b)' >= TrueCumWork(n, b)]_vars

\* Verdicts are never retracted.
VerdictsPermanent ==
    [][\A n \in Nodes :
            /\ validated[n] \subseteq validated'[n]
            /\ excluded[n] \subseteq excluded'[n]]_vars

\* Liveness: with every fact delivered and every body obtainable, the
\* validated tip eventually catches up with the canonical tip for good.
CatchesUp ==
    Available = Blocks =>
        \A n \in Nodes : <>[](ValidatedTip(n) = CanonicalTip(n))

=============================================================================
