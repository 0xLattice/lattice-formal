------------------------------ MODULE SwapReorg ------------------------------
(***************************************************************************)
(* What a cross-chain swap guarantees when either chain forks or           *)
(* reorganizes (Lattice docs/spec.md §8, §5.3 step 6, §9.5, §12.4).        *)
(*                                                                         *)
(* A parent chain P and one child chain C grow block by block; any block   *)
(* may be extended, so both chains fork freely, and either canonical tip   *)
(* may move to any selectable block at any time.  Fork choice is not      *)
(* modelled (Hierarchy.tla does that): a tip may land anywhere enough      *)
(* work could put it, so a property here holds under every reorg.         *)
(*                                                                         *)
(* Swap state is abstract.  Each swap s is one deposit key on C and its    *)
(* receipt key on P (one directory).  A P block inserts receipts (the      *)
(* withdrawer pays the demander, §6.5); a C block withdraws, then deposits *)
(* (§6.4).  A forged P block declares receipts in its postState without a  *)
(* transition that produces them; it is weighed, never executed.  A valid  *)
(* P block built on a forged one executes against the fetched state but is *)
(* not on the executed-from-genesis frontier (§8.3 rule 2).                *)
(*                                                                         *)
(* As in Hierarchy.tla, a P block is identified with the state it          *)
(* produced, so a C block's parentState is the P block named by Anchor.    *)
(* Only valid C blocks are mined: the validity rule is the guard under     *)
(* test.  A branch's swap state is its replay from genesis, so reading a   *)
(* branch after a reorg is replaying it.                                   *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    None,       \* no block
    PGen,       \* P genesis
    CGen,       \* C genesis, anchored at PGen (§5.1 rule 4)
    PIds,       \* sequence of further P block ids, used in order
    CIds,       \* sequence of further C block ids, used in order
    Swaps       \* deposit keys (and the receipt keys they consume)

PAll == {PGen} \cup {PIds[i] : i \in 1..Len(PIds)}
CAll == {CGen} \cup {CIds[i] : i \in 1..Len(CIds)}

ASSUME /\ None \notin PAll \cup CAll
       /\ PAll \cap CAll = {}

VARIABLES
    pMade,      \* P blocks weighed
    pPar,       \* P block -> predecessor or None
    pRc,        \* P block -> receipts its postState declares it inserted
    pExec,      \* P blocks whose own transition executed
    cMade,      \* C blocks (all valid)
    cPar,       \* C block -> predecessor or None
    cAnc,       \* C block -> its parentState (a P block)
    cDep,       \* C block -> deposits it inserts
    cWd,        \* C block -> deposits it releases
    tipP,       \* P canonical tip
    tipC        \* C canonical tip

vars == <<pMade, pPar, pRc, pExec, cMade, cPar, cAnc, cDep, cWd, tipP, tipC>>

RECURSIVE PLine(_), CLine(_)
PLine(b) == IF b = None THEN {} ELSE {b} \cup PLine(pPar[b])
CLine(b) == IF b = None THEN {} ELSE {b} \cup CLine(cPar[b])

\* §8.3 rule 2, §9.5: executed, and every ancestor executed.  (A forged
\* block is excluded on execution, so "not under an excluded block" adds
\* nothing here.)
Frontier == {p \in pExec : PLine(p) \subseteq pExec}

\* The receipt state p's postState declares.
ReceiptsAt(p) == UNION {pRc[q] : q \in PLine(p)}

\* The deposit state after applying a block's withdrawals, then deposits.
\* "spent" is the permanent zero-valued marker (§6.4).
Apply(st, wd, dep) ==
    [s \in Swaps |-> IF s \in wd THEN "spent"
                     ELSE IF s \in dep THEN "live" ELSE st[s]]

\* A branch's deposit state, replayed from genesis.
RECURSIVE StateAt(_)
StateAt(c) ==
    IF c = None THEN [s \in Swaps |-> "none"]
    ELSE Apply(StateAt(cPar[c]), cWd[c], cDep[c])

-----------------------------------------------------------------------------
(* Child validity (§5.3 steps 6-7, §6.4, §8.1 phase 3, §12.4).            *)

\* Step 6: the anchor is on the parent's executed-from-genesis frontier and
\* advances from the predecessor's anchor.
Continuity(c, a) ==
    /\ a \in Frontier
    /\ cAnc[c] \in PLine(a)

\* A withdrawal sees only prevState: the deposit is live there, and the
\* receipt is in the block's parentState.
WithdrawOk(c, a, s) ==
    /\ StateAt(c)[s] = "live"
    /\ s \in ReceiptsAt(a)

\* Insertion: the key is absent after the block's withdrawals.
DepositOk(c, wd, s) == Apply(StateAt(c), wd, {})[s] = "none"

\* A block on c, anchored at a, releasing wd and inserting dep.
ValidChild(c, a, dep, wd) ==
    /\ Continuity(c, a)
    /\ \A s \in wd : WithdrawOk(c, a, s)
    /\ \A s \in dep : DepositOk(c, wd, s)

-----------------------------------------------------------------------------
(* Actions.                                                                *)

\* A P block on q inserting receipts R (absent in q's state, §6.5).  A
\* forged one declares R without paying for it and is never executed.
MineP(q, R, forged) ==
    /\ Cardinality(pMade) <= Len(PIds)
    /\ q \in pMade
    /\ R \subseteq Swaps \ ReceiptsAt(q)
    /\ forged => R # {}
    /\ LET b == PIds[Cardinality(pMade)]
       IN  /\ pMade' = pMade \cup {b}
           /\ pPar' = [pPar EXCEPT ![b] = q]
           /\ pRc' = [pRc EXCEPT ![b] = R]
           /\ pExec' = IF forged THEN pExec ELSE pExec \cup {b}
    /\ UNCHANGED <<cMade, cPar, cAnc, cDep, cWd, tipP, tipC>>

\* A valid C block on c anchored at a.
MineC(c, a, dep, wd) ==
    /\ Cardinality(cMade) <= Len(CIds)
    /\ c \in cMade
    /\ ValidChild(c, a, dep, wd)
    /\ LET b == CIds[Cardinality(cMade)]
       IN  /\ cMade' = cMade \cup {b}
           /\ cPar' = [cPar EXCEPT ![b] = c]
           /\ cAnc' = [cAnc EXCEPT ![b] = a]
           /\ cDep' = [cDep EXCEPT ![b] = dep]
           /\ cWd' = [cWd EXCEPT ![b] = wd]
    /\ UNCHANGED <<pMade, pPar, pRc, pExec, tipP, tipC>>

\* Reorganizations: a canonical tip moves to any selectable block.
ReorgP(t) == t \in Frontier /\ tipP' = t /\ UNCHANGED <<pMade, pPar, pRc, pExec, cMade, cPar, cAnc, cDep, cWd, tipC>>
ReorgC(t) == t \in cMade /\ tipC' = t /\ UNCHANGED <<pMade, pPar, pRc, pExec, cMade, cPar, cAnc, cDep, cWd, tipP>>

Init ==
    /\ pMade = {PGen}
    /\ pPar = [b \in PAll |-> None]
    /\ pRc = [b \in PAll |-> {}]
    /\ pExec = {PGen}
    /\ cMade = {CGen}
    /\ cPar = [b \in CAll |-> None]
    /\ cAnc = [b \in CAll |-> IF b = CGen THEN PGen ELSE None]
    /\ cDep = [b \in CAll |-> {}]
    /\ cWd = [b \in CAll |-> {}]
    /\ tipP = PGen
    /\ tipC = CGen

\* A C block deposits or withdraws at most one swap, or does nothing.
COps == {<<{}, {}>>} \cup {<<{s}, {}>> : s \in Swaps} \cup {<<{}, {s}>> : s \in Swaps}

Next ==
    \/ \E q \in pMade, R \in SUBSET Swaps, f \in BOOLEAN : MineP(q, R, f)
    \/ \E c \in cMade, a \in pMade, op \in COps : MineC(c, a, op[1], op[2])
    \/ \E t \in PAll : ReorgP(t)
    \/ \E t \in CAll : ReorgC(t)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Properties.                                                             *)

TypeOK ==
    /\ pMade \subseteq PAll /\ pExec \subseteq pMade /\ cMade \subseteq CAll
    /\ tipP \in Frontier /\ tipC \in cMade
    /\ \A b \in cMade : cAnc[b] \in pMade

\* s is released on the C branch ending at c.
Released(s, c) == \E w \in CLine(c) : s \in cWd[w]

\* s's receipt was paid on the P branch ending at p: inserted by a block on
\* the executed-from-genesis frontier, whose transition debited the
\* withdrawer and credited the demander (§6.5).
PaidOn(s, p) == \E r \in PLine(p) \cap Frontier : s \in pRc[r]

\* §8.1, §8.3 "No forged parent state": the conditional atomicity the
\* protocol gives.  Every withdrawal on any C branch, canonical or not, is
\* backed by its paid receipt on EVERY P branch containing that block's
\* anchor, whichever P branch is canonical.
WithdrawalBackedOnAnchorBranch ==
    \A w \in cMade : \A s \in cWd[w] : \A t \in pMade :
        cAnc[w] \in PLine(t) => PaidOn(s, t)

\* §8.3 "No double-withdrawal", per branch: one deposit is released at
\* most once on any C branch, across every reorg.  (Two sibling branches
\* may each release it; at most one is canonical.)
NoDoubleRelease ==
    \A c \in cMade : \A s \in Swaps :
        Cardinality({w \in CLine(c) : s \in cWd[w]}) <= 1

\* §8.1 phase 3: a release needs the deposit in a strictly earlier block
\* of the same branch.
ReleaseHasDeposit ==
    \A w \in cMade : \A s \in cWd[w] : \E d \in CLine(cPar[w]) : s \in cDep[d]

\* §6.4: the replayed state of any branch shows a deposit spent exactly
\* when that branch released it.  A reorg undoes a release with its branch
\* and never revives a deposit the new branch has spent.
SpentIffReleased ==
    \A c \in cMade : \A s \in Swaps :
        (StateAt(c)[s] = "spent") <=> Released(s, c)

\* The demander's guarantee.  Once the canonical C tip anchors on the
\* canonical P chain, every release on the canonical C chain is paid on
\* the canonical P chain.  Anchors only advance (§5.3 step 6), so each
\* release's own anchor lies below the tip's.
DemanderSafeIfAnchorCanonical ==
    cAnc[tipC] \in PLine(tipP) =>
        \A s \in Swaps : Released(s, tipC) => PaidOn(s, tipP)

\* The withdrawer's guarantee.  A receipt paid on the canonical P chain
\* can be redeemed on the canonical C tip whenever the deposit is live
\* there and the tip anchors on the canonical P chain: a C block anchored
\* at the P tip may release it.  A release reorged out leaves the deposit
\* live (SpentIffReleased), so it can be released again.
WithdrawerCanRedeem ==
    \A s \in Swaps :
        (/\ PaidOn(s, tipP)
         /\ StateAt(tipC)[s] = "live"
         /\ cAnc[tipC] \in PLine(tipP))
            => ValidChild(tipC, tipP, {}, {s})

-----------------------------------------------------------------------------
(* Witnesses: each must FAIL, showing an exposure or a scenario a property *)
(* quantifies over is reachable.                                           *)

\* Off(line, x, t): x is on a branch that forks from t's (neither contains
\* the other), as after a reorganization from x's branch to t's.
POff(x, t) == x \notin PLine(t) /\ t \notin PLine(x)
COff(x, t) == x \notin CLine(t) /\ t \notin CLine(x)

\* The naive form: a release on the canonical C chain is paid on the
\* canonical P chain, even after the P chain reorganizes away from a
\* paid receipt.  Fails: the C chain keeps a release anchored on the
\* abandoned P branch (the demander's exposure).
NaiveCanonicalBacking ==
    \A s \in Swaps :
        (/\ Released(s, tipC)
         /\ \E r \in Frontier : s \in pRc[r] /\ POff(r, tipP))
            => PaidOn(s, tipP)

\* A receipt paid on the canonical P chain stays released on the canonical
\* C chain once released.  Fails: the C chain reorganizes away from the
\* release while the P chain keeps the payment (the withdrawer's exposure).
PaidImpliesReleased ==
    \A s \in Swaps :
        (/\ PaidOn(s, tipP)
         /\ \E w \in cMade : s \in cWd[w] /\ COff(w, tipC))
            => Released(s, tipC)

\* Fails: one deposit is released on two C branches.
ReleasedOnOneBranch ==
    \A s \in Swaps : Cardinality({w \in cMade : s \in cWd[w]}) <= 1

\* Fails: after a release is reorged out, the withdrawer can redeem again.
NoRedeemAfterReorg ==
    ~\E s \in Swaps :
        /\ PaidOn(s, tipP)
        /\ StateAt(tipC)[s] = "live"
        /\ cAnc[tipC] \in PLine(tipP)
        /\ \E w \in cMade : s \in cWd[w]

\* Fails: the demander is safe on the canonical chains while another
\* executed P branch has no receipt.
NoSafeReleaseBesideParentFork ==
    ~\E s \in Swaps :
        /\ cAnc[tipC] \in PLine(tipP)
        /\ Released(s, tipC)
        /\ \E p \in Frontier : ~PaidOn(s, p)

=============================================================================
