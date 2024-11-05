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
    /\ ballot = [n \in N |-> nullBallot] \* current ballot of each node
    /\ h =  [n \in N |-> nullBallot] \* current highest confirmed-prepared of each node
    /\ voteToPrepare = [n \in N |-> {}]
    /\ acceptedPrepared = [n \in N |-> {}]
    /\ voteToCommit = [n \in N |-> {}]
    /\ acceptedCommitted = [n \in N |-> {}]
    /\ externalized = [n \in N |-> {}]
    /\ byz \in FailProneSet \* the set of malicious nodes

IncreaseBallotCounter(n, c) ==
    /\  c > 0
    /\  c > ballot[n].counter
    /\  h[n].counter <= c
    /\  IF h[n] # nullBallot
        THEN ballot' = [ballot EXCEPT ![n] = bal(c, h[n].value)]
        ELSE \E v \in V : ballot' = [ballot EXCEPT ![n] = bal(c, v)]
    /\  voteToPrepare' = [voteToPrepare EXCEPT ![n] = @ \cup {ballot[n]'}]
    /\  UNCHANGED <<h, acceptedPrepared, voteToCommit, acceptedCommitted, externalized, byz>>

AcceptPrepared(n, b) ==
    /\  \/ \E Q \in Quorum : \A n2 \in Q \ byz : b \in voteToPrepare[n2] \cup acceptedPrepared[n2]
        \/ \E Bl \in BlockingSet : \A n2 \in Bl \ byz : b \in acceptedPrepared[n2]
    /\  acceptedPrepared' = [acceptedPrepared EXCEPT ![n] = @ \cup {b}]
    /\  UNCHANGED <<ballot, h, voteToPrepare, voteToCommit, acceptedCommitted, externalized, byz>>

ConfirmPrepared(n, b) ==
    /\  b.counter > -1
    /\  h[n] \prec b
    /\  \E Q \in Quorum : \A n2 \in Q \ byz : b \in acceptedPrepared[n2]
    /\  h' = [h EXCEPT ![n] = b]
    /\  UNCHANGED <<ballot, voteToPrepare, acceptedPrepared, voteToCommit, acceptedCommitted, externalized, byz>>

VoteToCommit(n, b) ==
    /\  b.counter > 0
    /\  b = ballot[n]
    /\  \A b2 \in Ballot : LessThanAndIncompatible(b, b2) =>
            b2 \notin voteToPrepare[n] \cup acceptedPrepared[n]
    /\  b \prec h[n] => b.value = h[n].value
    /\  \E Q \in Quorum : \A n2 \in Q \ byz : b \in acceptedPrepared[n2]
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

\* ByzantineHavoc ==
\*     /\ \E x \in [byz -> SUBSET Ballot] :
\*         voteToPrepare' = [n \in N |-> IF n \in byz THEN x[n] ELSE voteToPrepare[n]]
\*     /\ \E x \in [byz -> SUBSET Ballot] :
\*         acceptedPrepared' = [n \in N |-> IF n \in byz THEN x[n] ELSE acceptedPrepared[n]]
\*     /\ \E x \in [byz -> SUBSET Ballot] :
\*         voteToCommit' = [n \in N |-> IF n \in byz THEN x[n] ELSE voteToCommit[n]]
\*     /\ \E x \in [byz -> SUBSET Ballot] :
\*         acceptedCommitted' = [n \in N |-> IF n \in byz THEN x[n] ELSE acceptedCommitted[n]]
\*     /\  UNCHANGED <<h, externalized, byz>>

Next == 
    \/  \E n \in N \ byz, c \in BallotNumber, v \in V :
        LET b == bal(c, v) IN
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

InductiveInvariant ==
    \* First, the boring stuff:
    /\  TypeOK
    /\  byz \in FailProneSet
    /\  \A n \in N \ byz, c1,c2 \in BallotNumber, v1,v2 \in V :
        LET b1 == bal(c1,v1) b2 == bal(c2,v2) IN
        /\  ballot[n].counter > -1 => ballot[n].counter > 0
        /\  b1 \in voteToPrepare[n] \/ b1 \in voteToCommit[n] => b1.counter > 0 /\ b1.counter <= ballot[n].counter
        /\  b1 \in acceptedPrepared[n] => \E Q \in Quorum : \A n2 \in Q \ byz : b1 \in voteToPrepare[n2]
        /\  b1 \in acceptedCommitted[n] => \E Q \in Quorum : \A n2 \in Q \ byz : b1 \in voteToCommit[n2]
        /\  h[n].counter > 0 => \E Q \in Quorum : \A n2 \in Q \ byz : h[n] \in acceptedPrepared[n2]
        /\  b1 \in externalized[n] => \E Q \in Quorum : \A n2 \in Q \ byz : b1 \in acceptedCommitted[n2]
        /\  b1 \in voteToPrepare[n] \/ b1 \in voteToCommit[n] =>
            /\  b1.counter <= ballot[n].counter
            /\  b1.counter = ballot[n].counter => b1.value = ballot[n].value
        /\  bal(c1,v1) \in voteToPrepare[n] /\ bal(c1,v2) \in voteToPrepare[n] => v1 = v2
        /\  bal(c1,v1) \in voteToCommit[n] /\ bal(c1,v2) \in voteToCommit[n] => v1 = v2
        /\  b1 \in voteToCommit[n] =>
                /\  \E Q \in Quorum : \A n2 \in Q \ byz : b1 \in acceptedPrepared[n2]
                /\  b1 \preceq h[n]
        \* Next, the crux of the matter:
        \* (in short, a node only overrides "commit v" if it is sure that "commit v" cannot reach quorum threshold)
        /\  /\  b1 \in voteToCommit[n]
            /\  LessThanAndIncompatible(b1, b2)
            /\  b2 \in voteToPrepare[n]
            =>  \A Q \in Quorum : \E n2 \in Q \ byz :
                    b1 \notin voteToCommit[n2] /\ ballot[n2].counter > b1.counter
    \* Finally, our goal:
    /\  Agreement

==============================================