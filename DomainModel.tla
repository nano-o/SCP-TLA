----------- MODULE DomainModel -----------


EXTENDS Integers, FiniteSets

CONSTANTS
    N \* nodes
,   V \* values (the goal of the protocol is to agree on a value)
,   BallotNumber \* the set of ballot numbers (i.e. the integers)
,   Quorum \* the set of quorums
,   FailProneSet \* set of sets of nodes; one of them must include all failed nodes

ASSUME \E max \in BallotNumber : \A n \in BallotNumber :
    0 <= n /\ n <= max

Max(x, y) == IF x > y THEN x ELSE y
Min(x, y) == IF x < y THEN x ELSE y

BlockingSet == {B \in SUBSET N :
    \A Q \in Quorum : Q \cap B # {}}

someValue == CHOOSE v \in V : TRUE \* NOTE there is a bug in Apalache that makes this non-determined

Ballot == [counter : BallotNumber, value : V]
bal(c,v) == [counter |-> c, value |-> v]
nullBallot == bal(-1, someValue)
BallotOrNull == [counter : BallotNumber\cup {-1}, value : V]

\* LessThan predicate for comparing two ballots
\* @type: ({counter : Int, value : Int}, {counter : Int, value : Int}) => Bool;
LessThan(b1, b2) ==
    b1.counter < b2.counter \/ (b1.counter = b2.counter /\ b1.value < b2.value)
b1 \prec b2 == LessThan(b1, b2)
\* @type: ({counter : Int, value : Int}, {counter : Int, value : Int}) => Bool;
LessThanOrEqual(b1, b2) ==
    b1.counter < b2.counter \/ (b1.counter = b2.counter /\ b1.value <= b2.value)
b1 \preceq b2 == LessThanOrEqual(b1, b2)

LessThanAndIncompatible(b1, b2) ==
    LessThan(b1, b2) /\ b1.value # b2.value

==========================================
