------------- MODULE AbstractBalloting -------------

(**************************************************************************************)
(* This is a formalization of SCP's abstract balloting protocol described in          *)
(* Section 3.5 of the IETF draft at                                                   *)
(* `^https://datatracker.ietf.org/doc/html/draft-mazieres-dinrg-scp-05\#section-3.5^' *)
(*                                                                                    *)
(* We provide an inductive invariant showing that, by following the 2                 *)
(* ``restrictions on voting'' described in Section 3.5 of the above document,         *)
(* safety is guaranteed.                                                              *)
(**************************************************************************************)

EXTENDS Naturals, FiniteSets

CONSTANTS
    N \* nodes
,   V \* values (the goal of the protocol is to agree on a value)
,   BallotNumber \* the set of ballot numbers (i.e. the integers)
,   Quorum
,   FailProneSet

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

VoteToAbort(n, B) ==
    /\ B \subseteq Ballot
    \* Restriction 1: cannot vote both commit(b) and abort(b):
    /\  \A b \in B : \A b2 \in Ballot : LowerAndIncompatible(b2, b) => b2 \notin voteToCommit[n]
    /\  voteToAbort' = [voteToAbort EXCEPT ![n] = @ \cup B]
    /\  UNCHANGED <<acceptedAborted, voteToCommit, acceptedCommitted, externalized, byz>>

AcceptAborted(n, B) ==
    /\  \A b \in B :
        /\  \/ \E Q \in Quorums(n) : \A m \in Q : b \in voteToAbort[m] \cup acceptedAborted[m]
            \/ \E Bl \in BlockingSets(n) : \A m \in Bl : b \in acceptedAborted[m]
    /\  acceptedAborted' = [acceptedAborted EXCEPT ![n] = @ \cup B]
    /\  UNCHANGED <<voteToAbort, voteToCommit, acceptedCommitted, externalized, byz>>

CanVoteOrAcceptToCommit(n, b) ==
    \* Restriction 1: cannot vote both prepare(b) and commit(b):
    /\  \A b2 \in Ballot : LowerAndIncompatible(b, b2) => b2 \notin voteToAbort[n]
    \* Restriction 2:
    /\  
        \/ b.counter = 1 \* Initially, we can skip the prepare phase
        \/ \E Q \in Quorums(n) : \A m \in Q : b \in acceptedAborted[m]
        \/ \E cnt \in BallotNumber : cnt < b.counter /\ [counter |-> cnt, value |-> b.value] \in acceptedCommitted[n]

VoteToCommit(n, b) ==
    /\  b.counter > 0
    \* we vote to commit only one value per ballot number:
    /\  \A v \in V : [counter |-> b.counter, value |-> v] \notin voteToCommit[n]
    /\  CanVoteOrAcceptToCommit(n, b)
    /\  voteToCommit' = [voteToCommit EXCEPT ![n] = @ \cup {b}]
    /\  UNCHANGED <<voteToAbort, acceptedAborted, acceptedCommitted, externalized, byz>>

AcceptCommitted(n, b) ==
    /\  CanVoteOrAcceptToCommit(n, b)
    /\  \/ \E Q \in Quorums(n) : \A m \in Q : b \in voteToCommit[m] \cup acceptedCommitted[m]
        \/ \E B \in BlockingSets(n) : \A m \in B : b \in acceptedCommitted[m]
    /\  acceptedCommitted' = [acceptedCommitted EXCEPT ![n] = @ \cup {b}]
    /\  UNCHANGED <<voteToAbort, acceptedAborted, voteToCommit, externalized, byz>>

Externalize(n, b) ==
    /\  \E Q \in Quorums(n) : \A m \in Q : b \in acceptedCommitted[m]
    /\  externalized' = [externalized EXCEPT ![n] = @ \cup {b}]
    /\  UNCHANGED <<voteToAbort, acceptedAborted, voteToCommit, acceptedCommitted, byz>>

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
    \/ \E n \in N \ byz, b \in Ballot, B \in SUBSET Ballot :
        \/ VoteToAbort(n, B)
        \/ AcceptAborted(n, B)
        \/ VoteToCommit(n, b)
        \/ AcceptCommitted(n, b)
        \/ Externalize(n, b)
    \/  ByzantineHavoc

vars == <<voteToAbort, acceptedAborted, voteToCommit, acceptedCommitted, externalized, byz>>

Spec == Init /\ [][Next]_vars

Safety ==
    \A n1,n2 \in N \ byz : \A b1,b2 \in Ballot :
        b1 \in externalized[n1] /\ b2 \in externalized[n2] => b1.value = b2.value

\* A vote to prepare is a vote to abort all incompatible lower ballots:
VotedToAbort(n, b) ==
    \E b2 \in Ballot : b2 \in voteToAbort[n] /\ LowerAndIncompatible(b, b2)

\* Inductive invariant proving safety:
Invariant ==
    /\  TypeOK
    /\  byz \in FailProneSet
    /\  \A n \in N \ byz : \A b \in Ballot :
        /\  b \in voteToCommit[n] \cup acceptedCommitted[n] \cup externalized[n] => b.counter > 0
        /\  \A b2 \in Ballot :
                b \in voteToCommit[n] /\ b2 \in voteToCommit[n] /\ b # b2 => b.counter # b2.counter
        /\  \neg (VotedToAbort(n, b) /\ b \in voteToCommit[n])
        /\  b \in voteToCommit[n] =>
            \/  b.counter = 1
            \/  \E Q \in Quorum :
                \A m \in Q \ byz : b \in acceptedAborted[m]
            \/  \E cnt \in BallotNumber :
                /\  cnt < b.counter
                /\  [counter |-> cnt, value |-> b.value] \in acceptedCommitted[n]
        /\  b \in acceptedAborted[n] => \E Q \in Quorum :
                \A m \in Q \ byz : b \in voteToAbort[m]
        /\  b \in acceptedCommitted[n] => \E Q \in Quorum :
                \A m \in Q \ byz : b \in voteToCommit[m]
        /\  b \in externalized[n] => \E Q \in Quorum :
                \A m \in Q \ byz : b \in acceptedCommitted[m]
    /\  Safety

==============================================