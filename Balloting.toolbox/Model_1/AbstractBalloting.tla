------------- MODULE AbstractBalloting -------------

(**************************************************************************************)
(* This is a formalization of SCP's abstract balloting protocol described in          *)
(* Section 3.5 of the IETF draft at                                                   *)
(* `^https://datatracker.ietf.org/doc/html/draft-mazieres-dinrg-scp-05\#section-3.5^' *)
(*                                                                                    *)
(* The goal if to then refine this specification to one that closely matches the      *)
(* concrete SCP protocol.                                                             *)
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
    /\  voteToAbort \in [N -> SUBSET Ballot]
    /\  acceptedAborted \in [N -> SUBSET Ballot]
    /\  voteToCommit \in [N -> SUBSET Ballot]
    /\  acceptedCommitted \in [N -> SUBSET Ballot]
    /\  externalized \in [N -> SUBSET Ballot]
    /\  byz \in SUBSET N

Init ==
    /\ voteToAbort = [n \in N |-> {}]
    /\ acceptedAborted = [n \in N |-> {}]
    /\ voteToCommit = [n \in N |-> {}]
    /\ acceptedCommitted = [n \in N |-> {}]
    /\ externalized = [n \in N |-> {}]
    /\ byz \in FailProneSet

IsPrepared(n, b1) ==
        \/  \A b2 \in Ballot : LessThanAndIncompatible(b2, b1) => 
                \E Q \in Quorum : \A m \in Q \ byz : b2 \in acceptedAborted[m]
        \/  b1.counter = 1 \* Initially, we can skip the prepare phase
        \/ \E cnt \in BallotNumber : cnt < b1.counter /\ [counter |-> cnt, value |-> b1.value] \in acceptedCommitted[n] \* NOTE: is cnt < b1.counter necessary?

Step(n) ==
    /\  UNCHANGED <<byz>>
    \* NOTE we must update acceptedAborted before voteToAbort because updating voteToAbort depends on acceptedAborted':
    /\  \E B \in SUBSET Ballot :
        /\  \A b \in B :
            /\  \/ \E Q \in Quorum : \A m \in Q \ byz : b \in voteToAbort[m] \cup acceptedAborted[m]
                \/ \E Bl \in BlockingSet : \A m \in Bl \ byz : b \in acceptedAborted[m]
        /\  acceptedAborted' = [acceptedAborted EXCEPT ![n] = @ \cup B]
    /\ \E B \in SUBSET Ballot :
        /\  \A b \in B : b \notin voteToCommit[n] \/ b \in acceptedAborted'[n]
        /\  voteToAbort' = [voteToAbort EXCEPT ![n] = @ \cup B]
    \* NOTE we must update acceptedCommitted before voteToCommit because updating voteToCommit depends on acceptedCommitted':
    /\  \E B \in SUBSET Ballot :
        /\  \A b \in B :
            /\  \/ \E Q \in Quorum : \A m \in Q \ byz : b \in voteToCommit[m] \cup acceptedCommitted[m]
                \/ \E Bl \in BlockingSet : \A m \in Bl \ byz : b \in acceptedCommitted[m]
        /\  acceptedCommitted' = [acceptedCommitted EXCEPT ![n] = @ \cup B]
    /\  \E B \in SUBSET Ballot :
        /\  \A b \in B : 
            /\  b.counter > 0 \* we start at ballot 1
             \* if the ballot is already aborted, don't vote to commit (using the primed version ensures we don't vote to commit and abort at the same time):
            /\  b \notin voteToAbort'[n] \cup acceptedAborted'[n]
            /\  IsPrepared(n, b)' \* the prime allows us to consider prepared something we accepted committed in this very step
        /\  voteToCommit' = [voteToCommit EXCEPT ![n] = @ \cup B]
        \* we vote to commit at most one value per ballot number:
        /\  \A b1,b2 \in voteToCommit'[n] : b1.counter = b2.counter => b1.value = b2.value
    /\  \E B \in SUBSET Ballot :
        /\  \A b \in B : \E Q \in Quorum :
                \A m \in Q \ byz : b \in acceptedCommitted[m]
        /\  externalized' = [externalized EXCEPT ![n] = @ \cup B]

ByzantineHavoc ==
    /\ \E x \in [byz -> SUBSET Ballot] :
        voteToAbort' = [n \in N |-> IF n \in byz THEN x[n] ELSE voteToAbort[n]]
    /\ \E x \in [byz -> SUBSET Ballot] :
        acceptedAborted' = [n \in N |-> IF n \in byz THEN x[n] ELSE acceptedAborted[n]]
    /\ \E x \in [byz -> SUBSET Ballot] :
        voteToCommit' = [n \in N |-> IF n \in byz THEN x[n] ELSE voteToCommit[n]]
    /\ \E x \in [byz -> SUBSET Ballot] :
        acceptedCommitted' = [n \in N |-> IF n \in byz THEN x[n] ELSE acceptedCommitted[n]]
    /\  UNCHANGED <<externalized, byz>>

Next ==
    \/ \E n \in N : Step(n)
    \/  ByzantineHavoc

vars == <<voteToAbort, acceptedAborted, voteToCommit, acceptedCommitted, externalized, byz>>

Spec == Init /\ [][Next]_vars

Safety ==
    \A n1,n2 \in N \ byz : \A b1,b2 \in Ballot :
        b1 \in externalized[n1] /\ b2 \in externalized[n2] => b1.value = b2.value

\* Inductive invariant proving safety:
Invariant ==
    /\  TypeOK
    /\  byz \in FailProneSet
    /\  \A n \in N \ byz :
        /\  \A b \in Ballot :
            /\  b \in voteToCommit[n] => b \notin voteToAbort[n] \/ b \in acceptedAborted[n]
            /\  b \in voteToCommit[n] \cup acceptedCommitted[n] \cup externalized[n] => b.counter > 0
            /\  \A b2 \in Ballot :
                    b \in voteToCommit[n] /\ b2 \in voteToCommit[n] /\ b # b2 => b.counter # b2.counter
            /\  b \in acceptedAborted[n] => \E Q \in Quorum :
                    \A m \in Q \ byz : b \in voteToAbort[m]
            /\  b \in acceptedCommitted[n] => \E Q \in Quorum :
                    \A m \in Q \ byz : b \in voteToCommit[m]
            /\  b \in externalized[n] => \E Q \in Quorum :
                    \A m \in Q \ byz : b \in acceptedCommitted[m]
            /\  b \in voteToCommit[n] =>
                \/  b.counter = 1
                \/  \A b2 \in Ballot : LessThanAndIncompatible(b2, b) =>
                        \E Q \in Quorum : \A m \in Q \ byz : b2 \in acceptedAborted[m]
                \/  \E cnt \in BallotNumber :
                    /\  cnt < b.counter
                    /\  [counter |-> cnt, value |-> b.value] \in acceptedCommitted[n]
            /\  b \in acceptedAborted[n] => \A Q \in Quorum : \E m \in Q \ byz : b \notin voteToCommit[m]
    /\  Safety

==============================================