------------- MODULE AbstractSCP -------------

(***************************************************************************************)
(* This is essentially a formalization of SCP's balloting protocol, as described       *)
(* in Section 3.5 of the IETF draft at                                                 *)
(* `^https://datatracker.ietf.org/doc/html/draft-mazieres-dinrg-scp-05\#section-3.5^'   *)
(***************************************************************************************)

EXTENDS Naturals, FiniteSets

CONSTANTS
    N \* nodes
,   V \* values (the goal of the protocol is to agree on a value)
,   BallotNumber \* the set of ballot numbers (i.e. the integers)
,   Quorum
,   FailProneSet
    \* Slices \* Slices[n] is the set of quorum slices of node n

\* Quorum == {Q \in SUBSET N :
    \* \A n \in Q : \E s \in Slices[n] : s \subseteq Q}
\* Quorums(n) == {Q \in Quorum : n \in Q}
\* BlockingSets(n) == {B \in SUBSET N :
    \* \A Q \in Quorum : n \in Q => Q \cap B # {}}
Quorums(n) == Quorum
BlockingSets(n) == {B \in SUBSET N :
    \A Q \in Quorum : Q \cap B # {}}

Ballot == [counter : BallotNumber, value : V]

\* LessThan predicate for comparing two ballots
\* @type: ({counter : Int, value : Int}, {counter : Int, value : Int}) => Bool;
LessThan(b1, b2) ==
    b1.counter < b2.counter \/ (b1.counter = b2.counter /\ b1.value < b2.value)
LowerAndIncompatible(b1, b2) ==
    LessThan(b1, b2) /\ b1.value # b2.value

VARIABLES
    voteToPrepare
,   acceptedPrepared
,   voteToCommit
,   acceptedCommitted
,   externalized
,   byz

TypeOK == \A n \in N : 
    /\  voteToPrepare[n] \in SUBSET Ballot
    /\  acceptedPrepared[n] \in SUBSET Ballot
    /\  voteToCommit[n] \in SUBSET Ballot
    /\  acceptedCommitted[n] \in SUBSET Ballot
    /\  externalized[n] \in SUBSET Ballot
    /\  byz \in SUBSET N

Init ==
    /\ voteToPrepare = [n \in N |-> {}]
    /\ acceptedPrepared = [n \in N |-> {}]
    /\ voteToCommit = [n \in N |-> {}]
    /\ acceptedCommitted = [n \in N |-> {}]
    /\ externalized = [n \in N |-> {}]
    /\ byz \in FailProneSet

\* Cast a vote to abort all lower incompatible ballots:
VoteToPrepare(n, b) ==
    \* we try to prepare only one value per ballot number:
    /\  \A v \in V : [counter |-> b.counter, value |-> v] \notin voteToPrepare[n]
    \* Restriction 1: cannot vote both commit(b) and abort(b):
    /\  \A b2 \in Ballot : LowerAndIncompatible(b2, b) => b2 \notin voteToCommit[n]
    /\  voteToPrepare' = [voteToPrepare EXCEPT ![n] = @ \cup {b}]
    /\  UNCHANGED <<acceptedPrepared, voteToCommit, acceptedCommitted, externalized, byz>>

AcceptPrepared(n, b) ==
    /\  \/ \E Q \in Quorums(n) : \A m \in Q : b \in voteToPrepare[m]
        \/ \E B \in BlockingSets(n) : \A m \in B : b \in acceptedPrepared[m]
    /\  acceptedPrepared' = [acceptedPrepared EXCEPT ![n] = @ \cup {b}]
    /\  UNCHANGED <<voteToPrepare, voteToCommit, acceptedCommitted, externalized, byz>>

CanVoteOrAcceptToCommit(n, b) ==
    \* Restriction 1: cannot vote both prepare(b) and commit(b):
    /\  \A b2 \in Ballot : LowerAndIncompatible(b, b2) => b2 \notin voteToPrepare[n]
    \* Restriction 2:
    /\  
        \* \/ b.counter = 0 \* TODO: is this a problem?
        \/ \E Q \in Quorums(n) : \A m \in Q : b \in acceptedPrepared[m]
        \/ \E cnt \in BallotNumber : cnt < b.counter /\ [counter |-> cnt, value |-> b.value] \in acceptedCommitted[n]

VoteToCommit(n, b) ==
    \* we try to commit only one value per ballot number:
    /\  \A v \in V : [counter |-> b.counter, value |-> v] \notin voteToCommit[n]
    /\  CanVoteOrAcceptToCommit(n, b)
    /\  voteToCommit' = [voteToCommit EXCEPT ![n] = @ \cup {b}]
    /\  UNCHANGED <<voteToPrepare, acceptedPrepared, acceptedCommitted, externalized, byz>>

AcceptCommitted(n, b) ==
    /\  CanVoteOrAcceptToCommit(n, b)
    /\  \/ \E Q \in Quorums(n) : \A m \in Q : b \in voteToCommit[m]
        \/ \E B \in BlockingSets(n) : \A m \in B : b \in acceptedCommitted[m]
    /\  acceptedCommitted' = [acceptedCommitted EXCEPT ![n] = @ \cup {b}]
    /\  UNCHANGED <<voteToPrepare, acceptedPrepared, voteToCommit, externalized, byz>>

Externalize(n, b) ==
    /\  \E Q \in Quorums(n) : \A m \in Q : b \in acceptedCommitted[m]
    /\  externalized' = [externalized EXCEPT ![n] = @ \cup {b}]
    /\  UNCHANGED <<voteToPrepare, acceptedPrepared, voteToCommit, acceptedCommitted, byz>>

ByzHavoc ==
    /\ \E x \in [byz -> SUBSET Ballot] :
        voteToPrepare' = [n \in N |-> IF n \in byz THEN x[n] ELSE voteToPrepare[n]]
    /\ \E x \in [byz -> SUBSET Ballot] :
        acceptedPrepared' = [n \in N |-> IF n \in byz THEN x[n] ELSE acceptedPrepared[n]]
    /\ \E x \in [byz -> SUBSET Ballot] :
        voteToCommit' = [n \in N |-> IF n \in byz THEN x[n] ELSE voteToCommit[n]]
    /\ \E x \in [byz -> SUBSET Ballot] :
        acceptedCommitted' = [n \in N |-> IF n \in byz THEN x[n] ELSE acceptedCommitted[n]]
    /\  UNCHANGED <<externalized, byz>>

Next ==
    \/ \E n \in N \ byz, b \in Ballot :
        \/ VoteToPrepare(n, b)
        \/ AcceptPrepared(n, b)
        \/ VoteToCommit(n, b)
        \/ AcceptCommitted(n, b)
        \/ Externalize(n, b)
    \/  ByzHavoc

vars == <<voteToPrepare, acceptedPrepared, voteToCommit, acceptedCommitted, externalized, byz>>

Spec == Init /\ [][Next]_vars

Safety ==
    \A n1,n2 \in N : \A b1,b2 \in Ballot :
        b1 \in externalized[n1] /\ b2 \in externalized[n2] => b1.value = b2.value

==============================================