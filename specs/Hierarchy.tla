------------------------------ MODULE Hierarchy ------------------------------
(***************************************************************************)
(* A parent chain and one child chain on one node, modelled from the       *)
(* normative spec (Lattice docs/spec.md): parent-attributed run work       *)
(* (§9.10), parent-state continuity (§5.3 step 6, §9.5), and fork choice   *)
(* with weighed and validated tiers on each chain (§9.2-9.4, §9.9).        *)
(*                                                                         *)
(* The parent is the root chain.  The child is reached under one           *)
(* directory, so "commits into d" is the constant relation Commits.        *)
(*                                                                         *)
(* A parent block is identified with the state it produced, so a child     *)
(* block's parentState is the parent block that produced it (Anchor), or   *)
(* None for emptyHeader.  §5.3 step 3 binds a child to its carrier's       *)
(* prevState, i.e. the state its carrier's predecessor produced.           *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    None,       \* no block / emptyHeader
    PBlocks,    \* parent-chain blocks
    CBlocks,    \* child-chain blocks
    Parent,     \* same-chain predecessor, or None for a root
    CidRank,    \* injective; smaller = lexicographically smaller CID
    Grinds,     \* grind identities (root CIDs); a merged grind is in both chains
    Obs,        \* [ch |-> "P" or "C", g |-> grind, b |-> location, q |-> quantity]
    Commits,    \* set of <<p, c>>: parent block p's children index names c
    Anchor,     \* CBlocks -> PBlocks \cup {None}: the child's parentState
    Valid,      \* Blocks -> BOOLEAN: the block's own transition verdict
    Available,  \* blocks whose bodies can be obtained
    ExpectedTips,       \* [ch -> [canonical |-> b, validated |-> b]] (oracle)
    ExpectedChildWork   \* CBlocks -> Nat (oracle, shared by every model)

Chains == {"P", "C"}
Blocks == PBlocks \cup CBlocks
ChainBlocks(ch) == IF ch = "P" THEN PBlocks ELSE CBlocks

ASSUME /\ None \notin Blocks /\ PBlocks \cap CBlocks = {}
       /\ \A b \in PBlocks : Parent[b] \in PBlocks \cup {None}
       /\ \A b \in CBlocks : Parent[b] \in CBlocks \cup {None}
       /\ \A x, y \in Blocks : x # y => CidRank[x] # CidRank[y]
       /\ \A o \in Obs : o.ch \in Chains /\ o.g \in Grinds
                         /\ o.b \in ChainBlocks(o.ch) /\ o.q \in Nat \ {0}
       /\ Commits \subseteq PBlocks \X CBlocks
       \* §5.3 step 3: a committed child's parentState is its carrier's prevState.
       /\ \A pc \in Commits : Anchor[pc[2]] = Parent[pc[1]]
       \* A merged grind reaches the child only through a carrier that
       \* commits the child it lands on.
       /\ \A o1, o2 \in Obs :
              (o1.ch = "P" /\ o2.ch = "C" /\ o1.g = o2.g) => <<o1.b, o2.b>> \in Commits

VARIABLES
    delivered,  \* observations seen
    loc,        \* loc[ch][g]: g's located block in chain ch, or None
    qty,        \* qty[ch][g]: strongest verified quantity
    weighed,    \* weighed[ch]: admitted blocks
    validated,  \* validated[ch]: executed and matched
    excluded    \* excluded[ch]: recorded invalidity exclusions

vars == <<delivered, loc, qty, weighed, validated, excluded>>

Roots(ch) == {b \in ChainBlocks(ch) : Parent[b] = None}

RECURSIVE AncOrSelf(_)
AncOrSelf(b) == IF b = None THEN {} ELSE {b} \cup AncOrSelf(Parent[b])

\* Sum of f[x] over x in S.
RECURSIVE Sum(_, _)
Sum(S, f) ==
    IF S = {} THEN 0 ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + Sum(S \ {x}, f)

-----------------------------------------------------------------------------
(* Parent-attributed run work (§9.10).                                     *)

\* The nearest block at or above q, by parent pointer, that commits into
\* the child directory.  Never by canonical chain.
RECURSIVE NearestCarrier(_)
NearestCarrier(q) ==
    IF \E c \in CBlocks : <<q, c>> \in Commits THEN q
    ELSE IF Parent[q] = None THEN None
    ELSE NearestCarrier(Parent[q])

GrindsAt(ch, b) == {g \in Grinds : loc[ch][g] = b}

\* grindWork(P): credited work of P's own grinds.
GrindWork(p) == Sum(GrindsAt("P", p), qty["P"])

Run(p) == {q \in weighed["P"] : NearestCarrier(q) = p}
RunWork(p) == Sum(Run(p), [q \in Run(p) |-> GrindWork(q)])

\* attributed(C, P, d) = runWork(P, d) - grindWork(P).  The parent is the
\* root chain, so no run is attributed to it from above.
Attributed(p) == RunWork(p) - GrindWork(p)

-----------------------------------------------------------------------------
(* Weights and fork choice, per chain (§9.2-9.4, §9.9).                    *)

Subtree(ch, b) == {x \in weighed[ch] : b \in AncOrSelf(x)}

\* Child weight: located grinds, plus each attributed run of a weighed
\* parent carrier committing a block in the subtree (§12.5.5).
TrueCumWork(ch, b) ==
    LET grinds == Sum({g \in Grinds : loc[ch][g] \in Subtree(ch, b)}, qty[ch])
        cs     == IF ch = "P" THEN {}
                  ELSE {pc \in Commits : pc[1] \in weighed["P"]
                                         /\ pc[2] \in Subtree("C", b)}
    IN  grinds + Sum(cs, [pc \in cs |-> Attributed(pc[1])])

Better(ch, x, y) ==
    \/ TrueCumWork(ch, x) > TrueCumWork(ch, y)
    \/ /\ TrueCumWork(ch, x) = TrueCumWork(ch, y)
       /\ CidRank[x] < CidRank[y]

Best(ch, S) == CHOOSE x \in S : \A y \in S \ {x} : Better(ch, x, y)

RECURSIVE Descend(_, _, _)
Descend(ch, b, E) ==
    LET C == {c \in E : Parent[c] = b}
    IN  IF C = {} THEN b ELSE Descend(ch, Best(ch, C), E)

TipOver(ch, E) ==
    IF Roots(ch) \cap E = {} THEN None
    ELSE Descend(ch, Best(ch, Roots(ch) \cap E), E)

Selectable(ch) == {b \in weighed[ch] : AncOrSelf(b) \cap excluded[ch] = {}}
CanonicalTip(ch) == TipOver(ch, Selectable(ch))
ValidatedTip(ch) == TipOver(ch, validated[ch])

-----------------------------------------------------------------------------
(* Parent-state continuity (§5.3 step 6).                                  *)
(*                                                                         *)
(*   old = predecessor's parentState (None for a genesis), new = Anchor[b] *)
(*                                                                         *)
(* "proven": the parent's executed-from-genesis frontier produced new, at  *)
(*   or below a block that produced old.  A noncanonical branch may prove  *)
(*   it.  Equality is never evidence on its own.                           *)
(* "invalid": a completed check that the anchor moved backward or          *)
(*   sideways: back to emptyHeader, or both anchors held and old is not an *)
(*   ancestor of new.                                                      *)
(* "held": not proven here yet (anchor unexecuted or not held); retried,   *)
(*   never a verdict.                                                      *)

OldAnchor(b) == IF Parent[b] = None THEN None ELSE Anchor[Parent[b]]

Continuity(b) ==
    LET old == OldAnchor(b)
        new == Anchor[b]
    IN  IF new = None THEN IF old = None THEN "proven" ELSE "invalid"
        ELSE IF /\ old # None
                /\ {old, new} \subseteq weighed["P"]
                /\ old \notin AncOrSelf(new)
             THEN "invalid"
        ELSE IF /\ new \in validated["P"]
                /\ old \in AncOrSelf(new) \cup {None}
             THEN "proven"
        ELSE "held"

-----------------------------------------------------------------------------
(* Actions.                                                                *)

Observe(o) ==
    /\ o \notin delivered
    /\ delivered' = delivered \cup {o}
    /\ IF loc[o.ch][o.g] \in {None, o.b}
          THEN /\ loc' = [loc EXCEPT ![o.ch][o.g] = o.b]
               /\ qty' = [qty EXCEPT ![o.ch][o.g] = IF o.q > @ THEN o.q ELSE @]
          ELSE UNCHANGED <<loc, qty>>
    /\ UNCHANGED <<weighed, validated, excluded>>

Admit(ch, b) ==
    /\ b \notin weighed[ch]
    /\ Parent[b] \in weighed[ch] \cup {None}
    /\ GrindsAt(ch, b) # {}
    /\ weighed' = [weighed EXCEPT ![ch] = @ \cup {b}]
    /\ UNCHANGED <<delivered, loc, qty, validated, excluded>>

CanExecute(ch, b) ==
    /\ b \in weighed[ch] \ (validated[ch] \cup excluded[ch])
    /\ b \in Available
    /\ Parent[b] \in validated[ch] \cup {None}

\* The child's own verdict: continuity first, then its transition.
Verdict(ch, b) ==
    IF ch = "P" THEN IF Valid[b] THEN "valid" ELSE "invalid"
    ELSE CASE Continuity(b) = "invalid" -> "invalid"
           [] Continuity(b) = "held"    -> "held"
           [] OTHER -> IF Valid[b] THEN "valid" ELSE "invalid"

ValidateOk(ch, b) ==
    /\ CanExecute(ch, b)
    /\ Verdict(ch, b) = "valid"
    /\ validated' = [validated EXCEPT ![ch] = @ \cup {b}]
    /\ UNCHANGED <<delivered, loc, qty, weighed, excluded>>

Exclude(ch, b) ==
    /\ CanExecute(ch, b)
    /\ Verdict(ch, b) = "invalid"
    /\ b \in Roots(ch) => \E r \in Roots(ch) \ {b} : r \in validated[ch]
    /\ excluded' = [excluded EXCEPT ![ch] = @ \cup {b}]
    /\ UNCHANGED <<delivered, loc, qty, weighed, validated>>

Init ==
    /\ delivered = {}
    /\ loc       = [ch \in Chains |-> [g \in Grinds |-> None]]
    /\ qty       = [ch \in Chains |-> [g \in Grinds |-> 0]]
    /\ weighed   = [ch \in Chains |-> {}]
    /\ validated = [ch \in Chains |-> {}]
    /\ excluded  = [ch \in Chains |-> {}]

Next ==
    \/ \E o \in Obs : Observe(o)
    \/ \E ch \in Chains : \E b \in ChainBlocks(ch) :
           Admit(ch, b) \/ ValidateOk(ch, b) \/ Exclude(ch, b)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Properties.                                                             *)

TypeOK ==
    /\ delivered \subseteq Obs
    /\ \A ch \in Chains :
        /\ weighed[ch] \subseteq ChainBlocks(ch)
        /\ validated[ch] \subseteq weighed[ch]
        /\ excluded[ch] \subseteq weighed[ch]
        /\ validated[ch] \cap excluded[ch] = {}

\* §5.3 step 6 / §9.5: every validated child block is anchored at a state
\* the parent's executed frontier produced (or emptyHeader).
AnchoredAtExecuted ==
    \A b \in validated["C"] : Anchor[b] \in validated["P"] \cup {None}

\* §5.3: along validated child history, anchors only advance along the
\* parent's ancestry: never backward to emptyHeader, never sideways.
AnchorsAdvance ==
    \A b \in validated["C"] :
        Parent[b] # None =>
            \/ OldAnchor(b) = None
            \/ /\ Anchor[b] # None
               /\ OldAnchor(b) \in AncOrSelf(Anchor[b])

\* §9.10: each physical grind is counted once in a child block's weight.
\* A child block's weight is built from components: each located child
\* grind, and each attributed run, which stands for the parent grinds of
\* that run other than the carrier's own.  The components' grind sets must
\* be disjoint, and the weight must equal the sum over distinct grinds.
RunGrinds(p) == {g \in Grinds : loc["P"][g] \in Run(p) \ {p}}

\* Keyed, so two components holding the same grinds stay two components.
Components(b) ==
    { [key |-> <<"grind", g>>, grinds |-> {g}] :
          g \in {g \in Grinds : loc["C"][g] \in Subtree("C", b)} }
    \cup { [key |-> <<"run", pc>>, grinds |-> RunGrinds(pc[1])] :
          pc \in {pc \in Commits : pc[1] \in weighed["P"]
                                  /\ pc[2] \in Subtree("C", b)} }

\* A grind's credited quantity where this child counts it: at its child
\* location if it has one, otherwise in the parent run that carries it.
PhysicalQty(g) == IF loc["C"][g] # None THEN qty["C"][g] ELSE qty["P"][g]

PhysicalWorkOnce ==
    \A b \in weighed["C"] :
        LET cs      == Components(b)
            counted == UNION {c.grinds : c \in cs}
        IN  /\ Sum(cs, [c \in cs |-> Cardinality(c.grinds)]) = Cardinality(counted)
            /\ TrueCumWork("C", b) = Sum(counted, [g \in counted |-> PhysicalQty(g)])

TipsWellFormed ==
    \A ch \in Chains :
        /\ ValidatedTip(ch) # None =>
               AncOrSelf(ValidatedTip(ch)) \subseteq validated[ch]
        /\ CanonicalTip(ch) # None =>
               AncOrSelf(CanonicalTip(ch)) \cap excluded[ch] = {}

Quiescent == delivered = Obs /\ ~ENABLED Next

\* Oracle.  ExpectedChildWork is ONE table shared by every model, while
\* the models differ in the parent's verdicts and body availability, so
\* parent canonicity and parent execution cannot move child weights
\* (§12.5.7, §9.10 "independent of exclusion and of parent canonicity").
\* Exploring every arrival order and reaching only this answer is order
\* independence (§9.4, §9.10).
ExpectedAnswer ==
    Quiescent =>
        /\ \A b \in CBlocks : TrueCumWork("C", b) = ExpectedChildWork[b]
        /\ \A ch \in Chains :
               /\ CanonicalTip(ch) = ExpectedTips[ch].canonical
               /\ ValidatedTip(ch) = ExpectedTips[ch].validated

\* Work is monotone on both chains, attributed runs included (§9.10 "only
\* ever raised"; a run grows even when a block in it is excluded).
WorkMonotone ==
    [][\A ch \in Chains : \A b \in ChainBlocks(ch) :
            TrueCumWork(ch, b)' >= TrueCumWork(ch, b)]_vars

VerdictsPermanent ==
    [][\A ch \in Chains :
            /\ validated[ch] \subseteq validated'[ch]
            /\ excluded[ch] \subseteq excluded'[ch]]_vars

=============================================================================
