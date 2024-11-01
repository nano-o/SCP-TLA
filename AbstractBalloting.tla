------------- MODULE AbstractBalloting -------------

(**************************************************************************************)
(* This is a formalization of `^SCP^''s abstract balloting protocol described in      *)
(* Section 3.5 of the `^IETF^' draft at:                                              *)
(*                                                                                    *)
(* `^https://datatracker.ietf.org/doc/html/draft-mazieres-dinrg-scp-05\#section-3.5^' *)
(*                                                                                    *)
(* The goal if to then refine this specification to one that closely matches the      *)
(* concrete `^SCP^' protocol.                                                         *)
(*                                                                                    *)
(* We provide an inductive invariant showing that, by following the 2                 *)
(* ``restrictions on voting'' described in Section 3.5 of the above document,         *)
(* safety is guaranteed.                                                              *)
(*                                                                                    *)
(* Note that it is not true that a validator never votes to commit and abort the      *)
(* same ballot. This can happen when a validator votes to commit a ballot, but        *)
(* then accepts to abort it because a blocking set accepted to abort it. Moreover,    *)
(* it is necessary for liveness to allow this.                                        *)
(**************************************************************************************)

EXTENDS DomainModel

VARIABLES
    voteToAbort
,   acceptedAborted
,   voteToCommit
,   acceptedCommitted
,   externalized
,   byz

TypeOK ==
    /\  voteToAbort \in [N -> [Ballot -> BOOLEAN]]
    /\  acceptedAborted \in [N -> [Ballot -> BOOLEAN]]
    /\  voteToCommit \in [N -> [Ballot -> BOOLEAN]]
    /\  acceptedCommitted \in [N -> [Ballot -> BOOLEAN]]
    /\  externalized \in [N -> [Ballot -> BOOLEAN]]
    /\  byz \in SUBSET N

Init ==
    /\ voteToAbort = [n \in N |-> [b \in Ballot |-> FALSE]]
    /\ acceptedAborted = [n \in N |->  [b \in Ballot |-> FALSE]]
    /\ voteToCommit = [n \in N |->  [b \in Ballot |-> FALSE]]
    /\ acceptedCommitted = [n \in N |->  [b \in Ballot |-> FALSE]]
    /\ externalized = [n \in N |->  [b \in Ballot |-> FALSE]]
    /\ byz \in FailProneSet

IsPrepared(n, b1) ==
        \/  \A b2 \in Ballot : LessThanAndIncompatible(b2, b1) => 
                \E Q \in Quorum : \A n2 \in Q \ byz : acceptedAborted[n2][b2]
        \/ \E cnt \in BallotNumber : 
            /\  acceptedCommitted[n][[counter |-> cnt, value |-> b1.value]]
            /\  cnt < b1.counter \* really necessary?

Step(n) ==
    /\  UNCHANGED <<byz>>
    \* NOTE for TLC, we must update acceptedAborted before voteToAbort,
    \* because updating voteToAbort depends on acceptedAborted':
    /\  \E B \in SUBSET Ballot :
        /\  \A b \in B :
            /\  \/ \E Q \in Quorum : \A n2 \in Q \ byz : voteToAbort[n2][b] \/ acceptedAborted[n2][b]
                \/ \E Bl \in BlockingSet : \A n2 \in Bl \ byz : acceptedAborted[n2][b]
        /\  acceptedAborted' = [acceptedAborted EXCEPT ![n] = [b \in Ballot |-> IF b \in B THEN TRUE ELSE @[b]]]
    /\ \E B \in SUBSET Ballot :
        /\  \A b \in B : \neg voteToCommit[n][b] \/ acceptedAborted'[n][b]
        /\  voteToAbort' = [voteToAbort EXCEPT ![n] = [b \in Ballot |-> IF b \in B THEN TRUE ELSE @[b]]]
    \* NOTE for TLC, we must update acceptedCommitted before voteToCommit,
    \* because updating voteToCommit depends on acceptedCommitted':
    /\  \E B \in SUBSET Ballot :
        /\  \A b \in B :
            /\  \/ \E Q \in Quorum : \A n2 \in Q \ byz : voteToCommit[n2][b] \/ acceptedCommitted[n2][b]
                \/ \E Bl \in BlockingSet : \A n2 \in Bl \ byz : acceptedCommitted[n2][b]
        /\  acceptedCommitted' = [acceptedCommitted EXCEPT ![n] = [b \in Ballot |-> IF b \in B THEN TRUE ELSE @[b]]]
    /\  \E B \in SUBSET Ballot :
        /\  \A b \in B : 
            /\  b.counter > 0 \* we start at ballot 1
             \* if the ballot is already aborted, don't vote to commit
             \* (using the primed version ensures we don't vote to commit and abort at the same time):
            /\  \neg voteToAbort'[n][b] \/ acceptedAborted'[n][b]
             \* the prime allows us to consider prepared something we accepted committed in this very step:
            /\  IsPrepared(n, b)'
        /\  voteToCommit' = [voteToCommit EXCEPT ![n] = [b \in Ballot |-> IF b \in B THEN TRUE ELSE @[b]]]
        \* we vote to commit at most one value per ballot number:
        /\  \A b1,b2 \in Ballot : voteToCommit'[n][b1] /\ voteToCommit'[n][b2] /\ b1.counter = b2.counter => b1.value = b2.value
    /\  UNCHANGED <<externalized>>
    \* /\  \E B \in SUBSET Ballot :
    \*     /\  \A b \in B : \E Q \in Quorum :
    \*             \A n2 \in Q \ byz : acceptedCommitted[n2][b]
    \*     /\  externalized' = [externalized EXCEPT ![n] = [b \in Ballot |-> IF b \in B THEN TRUE ELSE @[b]]]

ByzantineHavoc ==
    /\ \E x \in [byz -> [Ballot -> BOOLEAN]] :
        voteToAbort' = [n \in N |-> IF n \in byz THEN x[n] ELSE voteToAbort[n]]
    /\ \E x \in [byz -> [Ballot -> BOOLEAN]] :
        acceptedAborted' = [n \in N |-> IF n \in byz THEN x[n] ELSE acceptedAborted[n]]
    /\ \E x \in [byz -> [Ballot -> BOOLEAN]] :
        voteToCommit' = [n \in N |-> IF n \in byz THEN x[n] ELSE voteToCommit[n]]
    /\ \E x \in [byz -> [Ballot -> BOOLEAN]] :
        acceptedCommitted' = [n \in N |-> IF n \in byz THEN x[n] ELSE acceptedCommitted[n]]
    /\  UNCHANGED <<externalized, byz>>

Next ==
    \/ \E n \in N : Step(n)
    \* \/  ByzantineHavoc

vars == <<voteToAbort, acceptedAborted, voteToCommit, acceptedCommitted, externalized, byz>>

Spec == Init /\ [][Next]_vars

Agreement ==
    \A n1,n2 \in N \ byz : \A b1,b2 \in Ballot :
        externalized[n1][b1] /\ externalized[n2][b2] => b1.value = b2.value

\* Inductive invariant proving safety:
InductiveInvariant ==
    /\  TypeOK
    /\  byz \in FailProneSet
    /\  \A n \in N \ byz :
        /\  \A b \in Ballot :
            /\  voteToCommit[n][b] => (\neg voteToAbort[n][b]) \/ acceptedAborted[n][b]
            /\  voteToCommit[n][b] \/ acceptedCommitted[n][b] \/ externalized[n][b] => b.counter > 0
            \* /\  \A b2 \in Ballot :
            \*         voteToCommit[n][b] /\ voteToCommit[n][b2] /\ b # b2 => b.counter # b2.counter
    \*         /\  acceptedAborted[n][b] => \E Q \in Quorum :
    \*                 \A n2 \in Q \ byz : voteToAbort[n2][b]
    \*         /\  acceptedCommitted[n][b] => \E Q \in Quorum :
    \*                 \A n2 \in Q \ byz : voteToCommit[n2][b]
    \*         /\  externalized[n][b] => \E Q \in Quorum :
    \*                 \A n2 \in Q \ byz : acceptedCommitted[n2][b]
    \*         /\  voteToCommit[n][b] =>
    \*             \/  b.counter = 1
    \*             \/  \A b2 \in Ballot : LessThanAndIncompatible(b2, b) =>
    \*                     \E Q \in Quorum : \A n2 \in Q \ byz : acceptedAborted[n2][b2]
    \*             \/  \E cnt \in BallotNumber :
    \*                 /\  cnt < b.counter
    \*                 /\  acceptedCommitted[n][[counter |-> cnt, value |-> b.value]]
    \*         /\  acceptedAborted[n][b] => \A Q \in Quorum : \E n2 \in Q \ byz : \neg voteToCommit[n2][b]
    \* /\  Agreement

==============================================