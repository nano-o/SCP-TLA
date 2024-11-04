------------- MODULE AbstractBallotingWithPrepare -------------

EXTENDS DomainModel

VARIABLES
    ballot
,   h
,   voteToPrepare
,   acceptedPrepared
,   voteToCommit
,   acceptedCommitted
,   externalized
,   byz

TypeOK ==
    /\  ballot \in [N -> BallotOrNull]
    /\  h \in [N -> BallotOrNull]
    /\  voteToPrepare \in [N -> SUBSET Ballot]
    /\  acceptedPrepared \in [N -> SUBSET Ballot]
    /\  voteToCommit \in [N -> SUBSET Ballot]
    /\  acceptedCommitted \in [N -> SUBSET Ballot]
    /\  externalized \in [N -> SUBSET Ballot]
    /\  byz \in SUBSET N

Init ==
    /\ ballot = [n \in N |-> nullBallot]
    /\ h =  [n \in N |-> nullBallot]
    /\ voteToPrepare = [n \in N |-> {}]
    /\ acceptedPrepared = [n \in N |-> {}]
    /\ voteToCommit = [n \in N |-> {}]
    /\ acceptedCommitted = [n \in N |-> {}]
    /\ externalized = [n \in N |-> {}]
    /\ byz \in FailProneSet

IncreaseBallotCounter(n, c) ==
    /\  c > 0
    /\  c > ballot[n].counter
    /\  IF h[n] # nullBallot
        THEN ballot' = [ballot EXCEPT ![n] = [counter |-> c, value |-> h[n].value]]
        ELSE \E v \in V : ballot' = [ballot EXCEPT ![n] = [counter |-> c, value |-> v]]
    /\  voteToPrepare' = [voteToPrepare EXCEPT ![n] = @ \cup {ballot[n]'}]
    /\  UNCHANGED <<h, acceptedPrepared, voteToCommit, acceptedCommitted, externalized, byz>>

AcceptPrepared(n, b) ==
    /\  \/ \E Q \in Quorum : \A n2 \in Q \ byz : b \in voteToPrepare[n2] \cup acceptedPrepared[n2]
        \/ \E Bl \in BlockingSet : \A n2 \in Bl \ byz : b \in acceptedPrepared[n2]
    /\  acceptedPrepared' = [acceptedPrepared EXCEPT ![n] = @ \cup {b}]
    /\  UNCHANGED <<ballot, h, voteToPrepare, voteToCommit, acceptedCommitted, externalized, byz>>

ConfirmPrepared(n, b) ==
    /\  h[n] \prec b
    /\  \E Q \in Quorum : \A n2 \in Q \ byz : b \in acceptedPrepared[n2]
    /\  h' = [h EXCEPT ![n] = b]
    /\  UNCHANGED <<ballot, voteToPrepare, acceptedPrepared, voteToCommit, acceptedCommitted, externalized, byz>>

CanVoteToCommit(n, b) ==
    /\  b = ballot[n]
    /\  \A b2 \in Ballot : LessThanAndIncompatible(b, b2) => b2 \notin voteToPrepare[n] \cup acceptedPrepared[n]
    /\  \/ \E Q \in Quorum : \A n2 \in Q \ byz : b \in acceptedPrepared[n2]
        \/ \E cnt \in BallotNumber :
            /\  cnt < b.counter
            /\ [counter |-> cnt, value |-> b.value] \in acceptedCommitted[n]

VoteToCommit(n, b) ==
    /\  CanVoteToCommit(n, b)
    /\  voteToCommit' = [voteToCommit EXCEPT ![n] = @ \cup {b}]
    /\  IF h[n] \preceq b
        THEN h' = [h EXCEPT ![n] = b]
        ELSE UNCHANGED h
    /\  UNCHANGED <<ballot, voteToPrepare, acceptedPrepared, acceptedCommitted, externalized, byz>>

AcceptCommitted(n, b) ==
    /\  b = ballot[n]
    /\  \/  \E Q \in Quorum : \A n2 \in Q \ byz : b \in voteToCommit[n2]
        \/  \E Bl \in BlockingSet : \A n2 \in Bl \ byz : b \in acceptedCommitted[n2]
    /\  acceptedCommitted' = [acceptedCommitted EXCEPT ![n] = @ \cup {b}]
    /\  UNCHANGED <<ballot, h, voteToPrepare, acceptedPrepared, voteToCommit, externalized, byz>>

Externalize(n, b) == 
    /\  b = ballot[n]
    /\  \E Q \in Quorum : \A n2 \in Q \ byz : b \in acceptedCommitted[n2]
    /\  externalized' = [externalized EXCEPT ![n] = @ \cup {b}]
    /\  UNCHANGED <<ballot, h, voteToPrepare, acceptedPrepared, voteToCommit, acceptedCommitted, byz>>

ByzantineHavoc ==
    /\ \E x \in [byz -> SUBSET Ballot] :
        voteToPrepare' = [n \in N |-> IF n \in byz THEN x[n] ELSE voteToPrepare[n]]
    /\ \E x \in [byz -> SUBSET Ballot] :
        acceptedPrepared' = [n \in N |-> IF n \in byz THEN x[n] ELSE acceptedPrepared[n]]
    /\ \E x \in [byz -> SUBSET Ballot] :
        voteToCommit' = [n \in N |-> IF n \in byz THEN x[n] ELSE voteToCommit[n]]
    /\ \E x \in [byz -> SUBSET Ballot] :
        acceptedCommitted' = [n \in N |-> IF n \in byz THEN x[n] ELSE acceptedCommitted[n]]
    /\  UNCHANGED <<h, externalized, byz>>

Next == 
    \/  \E n \in N, c \in BallotNumber, v \in V :
        LET b == [counter |-> c, value |-> v] IN
            \/  IncreaseBallotCounter(n, c)
            \/  AcceptPrepared(n, b)
            \/  ConfirmPrepared(n, b)
            \/  VoteToCommit(n, b)
            \/  AcceptCommitted(n, b)
            \/  Externalize(n, b)
    \* \/  ByzantineHavoc

vars == <<ballot, h, voteToPrepare, acceptedPrepared, voteToCommit, acceptedCommitted, externalized, byz>>
Spec == Init /\ [][Next]_vars

Agreement ==
    \A n1,n2 \in N \ byz : \A b1,b2 \in Ballot :
        b1 \in externalized[n1] /\ b2 \in externalized[n2] => b1.value = b2.value

==============================================

