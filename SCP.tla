----------------------------- MODULE SCP -----------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS
    N, \* nodes
    V, \* values (the goal of the protocol is to agree on a value)
    BallotNumber, \* the set of ballot numbers (i.e. the integers)
    Slices(_) \* Slices(n) is the set of quorum slices of node n

Ballot == [counter : BallotNumber, value : V]
someValue == CHOOSE v \in V : TRUE
\* Nodes start with a ballot number of 1, and we use counter 0 as a default value
NoBallot == [counter |-> 0, value |-> someValue]

\* LessThan predicate for comparing two ballots
LessThan(b1, b2) ==
    b1.counter < b2.counter \/ (b1.counter = b2.counter /\ b1.value < b2.value)

Phase == {"PREPARE", "COMMIT", "EXTERNALIZE"}

SCPPrepare == [
    type : {"PREPARE"}
,   ballot : Ballot
,   prepared : Ballot
,   aCounter : BallotNumber
,   hCounter : BallotNumber
,   cCounter : BallotNumber]

SCPCommit == [
    type : {"COMMIT"}
,   ballot : Ballot
,   preparedCounter : BallotNumber
,   hCounter : BallotNumber
,   cCounter : BallotNumber]

SCPExternalize == [
    type : {"EXTERNALIZE"}
,   commit : Ballot
,   hCounter : BallotNumber]

Message ==
    SCPPrepare \cup SCPCommit \cup SCPExternalize

VARIABLES
    ballot \* ballot[n] is the current ballot being prepared or committed by node n
,   phase  \* phase[n] is the current phase of node n
,   prepared \* prepared[n] is the highest accepted-prepared ballot by node n
,   aCounter \* aCounter[n] is such that all lower ballots are accepted as aborted (TODO: why no value here?)
    \* depending on the phase, h and c track the highest and lowest confirmed-prepared (in PREPARE), accepted committed (in COMMIT), or confirmed committed (in EXTERNALIZE) ballot
    \* In phase PREPARE, h.value could be different from ballot.value, in which case c.counter is 0
,   h
,   c
,   sent \* sent[n] is the set of messages sent by node n

Init ==
    /\ ballot \in [N -> {1}\times V] \* each node starts with ballot counter 1 and an arbitrary value
    /\ phase = [n \in N |-> "PREPARE"]
    /\ prepared = [n \in N |-> <<0, someValue>>]
    /\ aCounter = [n \in N |-> 0]
    /\ h = [n \in N |-> <<0, someValue>>]
    /\ c = [n \in N |-> <<0, someValue>>]
    /\ sent = [n \in N |-> {}]

TypeOK ==
    /\ ballot \in [N -> Ballot]
    /\ phase \in [N -> Phase]
    /\ prepared \in [N -> Ballot]
    /\ aCounter \in [N -> BallotNumber]
    /\ h \in [N -> Ballot]
    /\ c \in [N -> Ballot]
    /\ sent \in [N -> SUBSET Message]
          
=============================================================================