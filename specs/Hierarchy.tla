------------------------------ MODULE Hierarchy ------------------------------
(***************************************************************************)
(* A root chain P, a child chain C and, optionally, a grandchild chain G  *)
(* (GBlocks may be empty) on one node, modelled from the                   *)
(* normative spec (Lattice docs/spec.md): parent-attributed run work       *)
(* (§9.10), parent-state continuity (§5.3 step 6, §9.5), and fork choice   *)
(* with weighed and validated tiers on each chain (§9.2-9.4, §9.9).        *)
(*                                                                         *)
(* P is the root chain.  Each lower chain is reached under one directory  *)
(* of the chain above it, so "commits into d" is the constant relation     *)
(* Commits, from P blocks to C blocks and from C blocks to G blocks.  The  *)
(* recursion P -> C -> G is §9.10's "level by level": a run a chain's own  *)
(* parent attributed to one of its blocks is credited work there, so it    *)
(* reaches the next level down.                                            *)
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
    GBlocks,    \* grandchild-chain blocks (may be empty)
    Parent,     \* same-chain predecessor, or None for a root
    CidRank,    \* injective; smaller = lexicographically smaller CID
    Grinds,     \* grind identities (root CIDs); a merged grind is in both chains
    Obs,        \* [ch |-> "P", "C" or "G", g |-> grind, b |-> location, q |-> quantity]
    Commits,    \* set of <<u, l>>: block u's children index names l, one level down
    Anchor,     \* lower-chain block -> block of the chain above, or None: its parentState
    Valid,      \* Blocks -> BOOLEAN: the block's own transition verdict
    Available,  \* blocks whose bodies can be obtained
    ExpectedTips,       \* [ch -> [canonical |-> b, validated |-> b]] (oracle)
    ExpectedChildWork   \* CBlocks \cup GBlocks -> Nat (oracle, shared by every model)

Chains == {"P", "C", "G"}
Lower(ch) == IF ch = "P" THEN "C" ELSE "G"   \* the chain ch commits into
Up(ch) == IF ch = "G" THEN "C" ELSE "P"      \* the chain above a lower chain
LowerChains == {"C", "G"}
Blocks == PBlocks \cup CBlocks \cup GBlocks
ChainBlocks(ch) == CASE ch = "P" -> PBlocks [] ch = "C" -> CBlocks [] OTHER -> GBlocks
ChainOf(b) == CHOOSE ch \in Chains : b \in ChainBlocks(ch)

ASSUME /\ None \notin Blocks
       /\ PBlocks \cap CBlocks = {} /\ PBlocks \cap GBlocks = {} /\ CBlocks \cap GBlocks = {}
       /\ \A ch \in Chains : \A b \in ChainBlocks(ch) : Parent[b] \in ChainBlocks(ch) \cup {None}
       /\ \A x, y \in Blocks : x # y => CidRank[x] # CidRank[y]
       /\ \A o \in Obs : o.ch \in Chains /\ o.g \in Grinds
                         /\ o.b \in ChainBlocks(o.ch) /\ o.q \in Nat \ {0}
       /\ Commits \subseteq (PBlocks \X CBlocks) \cup (CBlocks \X GBlocks)
       \* A block's children index names one block per directory.
       /\ \A pc, qc \in Commits : pc[1] = qc[1] => pc = qc
       \* §5.3 step 3: a committed child's parentState is its carrier's prevState.
       /\ \A pc \in Commits : Anchor[pc[2]] = Parent[pc[1]]
       \* A merged grind lies on one proof path: at each lower level it
       \* lands on the block its carrier above commits.
       /\ \A o1, o2 \in Obs :
              o1.g = o2.g =>
                  /\ (o1.ch = "P" /\ o2.ch = "C") => <<o1.b, o2.b>> \in Commits
                  /\ (o1.ch = "C" /\ o2.ch = "G") => <<o1.b, o2.b>> \in Commits
                  /\ (o1.ch = "P" /\ o2.ch = "G") =>
                         \E c \in CBlocks : <<o1.b, c>> \in Commits /\ <<c, o2.b>> \in Commits

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

\* The nearest block at or above q on chain ch, by parent pointer, that
\* commits into the chain below.  Never by canonical chain.
Commits1(ch, q) == \E l \in ChainBlocks(Lower(ch)) : <<q, l>> \in Commits
RECURSIVE NearestCarrier(_, _)
NearestCarrier(ch, q) ==
    IF Commits1(ch, q) THEN q
    ELSE IF Parent[q] = None THEN None
    ELSE NearestCarrier(ch, Parent[q])

GrindsAt(ch, b) == {g \in Grinds : loc[ch][g] = b}

\* grindWork(P): credited work of P's own grinds.
GrindWork(ch, p) == Sum(GrindsAt(ch, p), qty[ch])

Run(ch, p) == {q \in weighed[ch] : NearestCarrier(ch, q) = p}

\* runWork sums CREDITED work, grinds and attributed runs alike, so a run
\* the chain above attributed to a block of this run reaches the chain below.
RECURSIVE Credited(_, _), RunWork(_, _), Attributed(_, _)

\* attributed(C, P, d) = runWork(P, d) - grindWork(P).
Attributed(ch, p) == RunWork(ch, p) - GrindWork(ch, p)

RunWork(ch, p) == Sum(Run(ch, p), [q \in Run(ch, p) |-> Credited(ch, q)])

\* A block's credited work: its grinds, and on a lower chain the attributed
\* run of each weighed carrier above that commits it.
Credited(ch, q) ==
    GrindWork(ch, q)
    + IF ch = "P" THEN 0
      ELSE LET us == {u \in weighed[Up(ch)] : <<u, q>> \in Commits}
           IN  Sum(us, [u \in us |-> Attributed(Up(ch), u)])

-----------------------------------------------------------------------------
(* Weights and fork choice, per chain (§9.2-9.4, §9.9).                    *)

Subtree(ch, b) == {x \in weighed[ch] : b \in AncOrSelf(x)}

\* Weight: located grinds, plus each attributed run of a weighed carrier
\* above committing a block in the subtree (§12.5.5).
TrueCumWork(ch, b) ==
    LET grinds == Sum({g \in Grinds : loc[ch][g] \in Subtree(ch, b)}, qty[ch])
        cs     == IF ch = "P" THEN {}
                  ELSE {pc \in Commits : pc[1] \in weighed[Up(ch)]
                                         /\ pc[2] \in Subtree(ch, b)}
    IN  grinds + Sum(cs, [pc \in cs |-> Attributed(Up(ch), pc[1])])

\* W is the chain's weight table, computed once per descent.
Better(W, x, y) ==
    \/ W[x] > W[y]
    \/ W[x] = W[y] /\ CidRank[x] < CidRank[y]

Best(W, S) == CHOOSE x \in S : \A y \in S \ {x} : Better(W, x, y)

RECURSIVE Descend(_, _, _)
Descend(W, b, E) ==
    LET C == {c \in E : Parent[c] = b}
    IN  IF C = {} THEN b ELSE Descend(W, Best(W, C), E)

TipOver(ch, E) ==
    LET W == [x \in ChainBlocks(ch) |-> TrueCumWork(ch, x)]
    IN  IF Roots(ch) \cap E = {} THEN None
        ELSE Descend(W, Best(W, Roots(ch) \cap E), E)

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
(* "invalid": the anchor is emptyHeader where the spec forbids it: a child *)
(*   genesis carried by a genesis (§5.1 rule 4), or a non-genesis block    *)
(*   dropping back to empty from a real anchor (§5.3 step 6).              *)
(* "held": not proven here, including a sideways anchor; retried, never a  *)
(*   verdict (§9.5: anchoring elsewhere gets "not proven here").  State    *)
(*   CIDs are not block IDs, so a later header could still supply a path.  *)

OldAnchor(b) == IF Parent[b] = None THEN None ELSE Anchor[Parent[b]]

Continuity(b) ==
    LET old == OldAnchor(b)
        new == Anchor[b]
    IN  IF new = None
           THEN IF Parent[b] # None /\ old = None THEN "proven" ELSE "invalid"
        ELSE IF /\ new \in validated[Up(ChainOf(b))]
                /\ old \in AncOrSelf(new) \cup {None}
             THEN "proven"
        ELSE "held"

-----------------------------------------------------------------------------
(* Actions.                                                                *)

Record(o) ==
    /\ delivered' = delivered \cup {o}
    /\ IF loc[o.ch][o.g] \in {None, o.b}
          THEN /\ loc' = [loc EXCEPT ![o.ch][o.g] = o.b]
               /\ qty' = [qty EXCEPT ![o.ch][o.g] = IF o.q > @ THEN o.q ELSE @]
          ELSE UNCHANGED <<loc, qty>>

\* A further observation at an admitted block.
Observe(o) ==
    /\ o \notin delivered
    /\ o.b \in weighed[o.ch]
    /\ Record(o)
    /\ UNCHANGED <<weighed, validated, excluded>>

\* Admission carries the block's securing grind in the same batch, as the
\* implementation's import does.  (Staged locations ahead of admission are
\* covered by ForkChoice.tla; folding them here keeps the state space small.)
Admit(o) ==
    /\ o \notin delivered
    /\ o.b \notin weighed[o.ch]
    /\ Parent[o.b] \in weighed[o.ch] \cup {None}
    /\ loc[o.ch][o.g] \in {None, o.b}
    /\ Record(o)
    /\ weighed' = [weighed EXCEPT ![o.ch] = @ \cup {o.b}]
    /\ UNCHANGED <<validated, excluded>>

CanExecute(ch, b) ==
    /\ b \in weighed[ch] \ (validated[ch] \cup excluded[ch])
    /\ b \in Available
    /\ Parent[b] \in validated[ch] \cup {None}

\* A block's own verdict.  A failed transition (§5.3 step 7) is invalid
\* under any continuity outcome, so it is a verdict even while the anchor's
\* continuity (step 6) is held; a valid transition still needs a proven
\* anchor.
Verdict(ch, b) ==
    IF ~Valid[b] THEN "invalid"
    ELSE IF ch = "P" THEN "valid"
    ELSE CASE Continuity(b) = "invalid" -> "invalid"
           [] Continuity(b) = "held"    -> "held"
           [] OTHER -> "valid"

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
    \/ \E o \in Obs : Admit(o) \/ Observe(o)
    \/ \E ch \in Chains : \E b \in ChainBlocks(ch) :
           ValidateOk(ch, b) \/ Exclude(ch, b)

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
\* the parent's executed frontier produced.  Only a non-genesis block whose
\* predecessor commits none may commit emptyHeader (§5.1 rule 4).
AnchoredAtExecuted ==
    \A ch \in LowerChains : \A b \in validated[ch] :
        \/ Anchor[b] \in validated[Up(ch)]
        \/ Anchor[b] = None /\ Parent[b] # None /\ OldAnchor(b) = None

\* §5.3: along validated child history, anchors only advance along the
\* parent's ancestry: never backward to emptyHeader, never sideways.
AnchorsAdvance ==
    \A ch \in LowerChains : \A b \in validated[ch] :
        Parent[b] # None =>
            \/ OldAnchor(b) = None
            \/ /\ Anchor[b] # None
               /\ OldAnchor(b) \in AncOrSelf(Anchor[b])

\* §9.10: each physical grind is counted once in a lower block's weight.
\* A weight is built from components: each located grind, and each
\* attributed run, which stands for the grinds of that run other than the
\* carrier's own, together with what the runs attributed into that run
\* from further up stand for ("level by level").  The weight must equal the
\* sum over the distinct grinds, computed from the reference below rather
\* than from Attributed; no two components, and no two entries of one,
\* may share a grind.  (Disjointness also follows from the ASSUME that a
\* merged grind lies on one proof path.)
\* Reference, independent of NearestCarrier and Run: the carrier whose run
\* holds q is the deepest committing block on q's ancestry.
Committer(ch, x) == \E l \in ChainBlocks(Lower(ch)) : <<x, l>> \in Commits
RefCarrier(ch, q) ==
    LET cs == {x \in AncOrSelf(q) : Committer(ch, x)}
    IN  IF cs = {} THEN None ELSE CHOOSE x \in cs : cs \subseteq AncOrSelf(x)

\* The <<chain, grind>> pairs the attributed run of carrier u on chain ch
\* stands for, each counted at the chain whose quantity it carries there.
RECURSIVE Stands(_, _)
Stands(ch, u) ==
    LET members == {q \in weighed[ch] : RefCarrier(ch, q) = u}
        above   == IF ch = "P" THEN {}
                   ELSE {w \in weighed[Up(ch)] : \E q \in members : <<w, q>> \in Commits}
    IN  {<<ch, g>> : g \in {g \in Grinds : loc[ch][g] \in members \ {u}}}
        \cup UNION {Stands(Up(ch), w) : w \in above}

\* Keyed, so two components holding the same grinds stay two components.
Components(ch, b) ==
    { [key |-> <<"grind", g>>, grinds |-> {<<ch, g>>}] :
          g \in {g \in Grinds : loc[ch][g] \in Subtree(ch, b)} }
    \cup { [key |-> <<"run", pc>>, grinds |-> Stands(Up(ch), pc[1])] :
          pc \in {pc \in Commits : pc[1] \in weighed[Up(ch)]
                                  /\ pc[2] \in Subtree(ch, b)} }

PhysicalWorkOnce ==
    \A ch \in LowerChains : \A b \in weighed[ch] :
        LET cs      == Components(ch, b)
            counted == UNION {c.grinds : c \in cs}
            ids     == {pg[2] : pg \in counted}
        IN  /\ Sum(cs, [c \in cs |-> Cardinality(c.grinds)]) = Cardinality(ids)
            /\ TrueCumWork(ch, b) = Sum(counted, [pg \in counted |-> qty[pg[1]][pg[2]]])

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
        /\ \A ch \in LowerChains : \A b \in ChainBlocks(ch) :
               TrueCumWork(ch, b) = ExpectedChildWork[b]
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
