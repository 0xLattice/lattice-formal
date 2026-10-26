--------------------------- MODULE HierarchyProps ---------------------------
(***************************************************************************)
(* Lattice-specific properties of the hierarchy model that are stated as   *)
(* independence ("X does not depend on Y").  Each is checked by evaluating *)
(* the model's own operators a second time, in an instance where Y is      *)
(* replaced, and requiring the same answer in every reachable state.        *)
(***************************************************************************)
EXTENDS Hierarchy

\* The same state with every verdict erased.
NoVerdicts == INSTANCE Hierarchy
    WITH validated <- [ch \in Chains |-> {}],
         excluded  <- [ch \in Chains |-> {}]

\* The same state with chain u's canonicity moved as far as it goes: every
\* non-root block of u excluded, and u's CID order reversed.  u's
\* validated set (what has executed) is untouched.
MaxRank == Sum(Blocks, CidRank)
OtherCanon(u) == INSTANCE Hierarchy
    WITH excluded <- [excluded EXCEPT ![u] = ChainBlocks(u) \ Roots(u)],
         CidRank  <- [x \in DOMAIN CidRank |->
                         IF x \in ChainBlocks(u) THEN MaxRank - CidRank[x]
                         ELSE CidRank[x]]

Below(u) == IF u = "P" THEN {"C", "G"} ELSE {"G"}

\* The same state with every chain below u erased: no lower-chain block,
\* location, quantity or verdict.
NoBelow(u) == INSTANCE Hierarchy
    WITH weighed   <- [ch \in Chains |-> IF ch \in Below(u) THEN {} ELSE weighed[ch]],
         validated <- [ch \in Chains |-> IF ch \in Below(u) THEN {} ELSE validated[ch]],
         excluded  <- [ch \in Chains |-> IF ch \in Below(u) THEN {} ELSE excluded[ch]],
         loc <- [ch \in Chains |-> IF ch \in Below(u) THEN [g \in Grinds |-> None] ELSE loc[ch]],
         qty <- [ch \in Chains |-> IF ch \in Below(u) THEN [g \in Grinds |-> 0] ELSE qty[ch]]

-----------------------------------------------------------------------------

\* §12.5.2, §9.9 "work weighs, validity selects": weights are verified
\* independently of every verdict, carriers' included.  No verdict on any
\* chain moves any block's weight.
WeightIgnoresVerdicts ==
    \A ch \in Chains : \A b \in ChainBlocks(ch) :
        TrueCumWork(ch, b) = NoVerdicts!TrueCumWork(ch, b)

\* §12.5.7: parent canonicity alone cannot change child validity, weight or
\* fork choice.  Every chain below u sees the same weights, the same
\* continuity and verdicts, and the same tips, whichever branch of u is
\* canonical.
ParentCanonicityIrrelevant ==
    \A u \in {"P", "C"} : \A ch \in Below(u) :
        /\ \A b \in ChainBlocks(ch) :
               /\ TrueCumWork(ch, b) = OtherCanon(u)!TrueCumWork(ch, b)
               /\ Verdict(ch, b) = OtherCanon(u)!Verdict(ch, b)
        /\ CanonicalTip(ch) = OtherCanon(u)!CanonicalTip(ch)
        /\ ValidatedTip(ch) = OtherCanon(u)!ValidatedTip(ch)

\* Not vacuous: at quiescence the perturbation really moves the parent's
\* canonical tip (only in models where that tip is not a root), and, where
\* the parent's branches tie (MCHierarchyFork), the validated tip it acts on.
ParentCanonMoves ==
    Quiescent =>
        OtherCanon("P")!CanonicalTip("P") # CanonicalTip("P")

ParentValidatedMoves ==
    Quiescent =>
        OtherCanon("P")!ValidatedTip("P") # ValidatedTip("P")

\* §9.10: attribution flows down only.  A chain's weights, verdicts and
\* tips are what they would be with every chain below it erased: no child
\* chain, however much work or spam it carries, moves its parent's fork
\* choice.
ChildrenCannotMoveParent ==
    \A u \in {"P", "C"} : \A ch \in Chains \ Below(u) :
        /\ \A b \in ChainBlocks(ch) :
               /\ TrueCumWork(ch, b) = NoBelow(u)!TrueCumWork(ch, b)
               /\ ch \in LowerChains => Verdict(ch, b) = NoBelow(u)!Verdict(ch, b)
        /\ CanonicalTip(ch) = NoBelow(u)!CanonicalTip(ch)
        /\ ValidatedTip(ch) = NoBelow(u)!ValidatedTip(ch)

\* Merged mining has nothing at stake: the work above behind one side of a
\* lower fork never also backs the other side.  Feeds(ch, q) is every block
\* above whose work reaches q's credited work through attributed runs,
\* followed level by level to the root (a run's members are credited with
\* the runs attributed to them in turn, §9.10).  Backing(ch, b) gathers it
\* over b's subtree; sibling subtrees, genesis forks included, share none.
RECURSIVE Feeds(_, _)
Feeds(ch, q) ==
    LET members == UNION {Run(Up(ch), u) : u \in CarriersOf(ch, q)}
    IN  members \cup IF Up(ch) = "P" THEN {}
                     ELSE UNION {Feeds(Up(ch), m) : m \in members}

Backing(ch, b) == UNION {Feeds(ch, q) : q \in Subtree(ch, b)}

NoDoubleBacking ==
    \A ch \in LowerChains : \A x, y \in weighed[ch] :
        (x # y /\ Parent[x] = Parent[y]) => Backing(ch, x) \cap Backing(ch, y) = {}

\* Not vacuous: some reachable state has a child fork whose two sides are
\* both backed by parent work.  Checked as a property that must FAIL.
BackedFork(ch) ==
    \E x, y \in weighed[ch] :
        x # y /\ Parent[x] = Parent[y] /\ Backing(ch, x) # {} /\ Backing(ch, y) # {}

NoBackedFork == ~BackedFork("C")
NoBackedGrandchildFork ==
    ~(BackedFork("G") /\ \E x \in weighed["G"] : Backing("G", x) \cap PBlocks # {})

\* §9.9, "unavailable is not invalid": a block is excluded only for a
\* cause its own bytes prove: a header rule, a failed transition, or an
\* anchor the spec forbids (emptyHeader under a genesis carrier or after a
\* real anchor, §5.1 rule 4, §5.3 step 6).  A missing body, a held anchor or
\* an excluded ancestor never excludes.  Independent of Continuity/Verdict.
ForbiddenAnchor(b) ==
    Anchor[b] = None /\ ~(Parent[b] # None /\ OldAnchor(b) = None)

ExcludedHasCause ==
    \A ch \in Chains : \A b \in excluded[ch] :
        \/ b \in HeaderBad
        \/ /\ b \in Available
           /\ \/ ~Valid[b]
              \/ ch # "P" /\ ForbiddenAnchor(b)

\* §9.4, §12.5.10: no finality.  At every fork on the canonical path, at
\* any depth and genesis forks included, the chosen block is the heaviest
\* selectable sibling by whole-subtree work, ties to the smaller CID; and
\* the tip has no selectable child.  Stated per fork, not by descent.
\* §9.9: the validated tip follows the same rule over validated blocks,
\* weighed by the whole subtree, unvalidated descendants included.
HeaviestPath(ch, t, S) ==
    /\ t = None => Roots(ch) \cap S = {}
    /\ t # None =>
         /\ \A y \in S : Parent[y] # t
         /\ \A x \in AncOrSelf(t) : \A y \in S :
                (y # x /\ Parent[y] = Parent[x]) =>
                    \/ TrueCumWork(ch, y) < TrueCumWork(ch, x)
                    \/ /\ TrueCumWork(ch, y) = TrueCumWork(ch, x)
                       /\ CidRank[x] < CidRank[y]

HeaviestAtEveryFork ==
    \A ch \in Chains :
        /\ HeaviestPath(ch, CanonicalTip(ch), Selectable(ch))
        /\ HeaviestPath(ch, ValidatedTip(ch), validated[ch])

\* §12.5.9: Lattice never prunes accepted graph or verified work facts.
NothingPruned ==
    [][/\ delivered \subseteq delivered'
       /\ \A ch \in Chains :
            /\ weighed[ch] \subseteq weighed'[ch]
            /\ \A g \in Grinds :
                   /\ loc[ch][g] # None => loc'[ch][g] = loc[ch][g]
                   /\ qty'[ch][g] >= qty[ch][g]]_vars

=============================================================================
