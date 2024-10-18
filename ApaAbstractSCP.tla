----------- MODULE ApaAbstractSCP ------------------

V == {0,1}
N == {"N1_OF_NODE", "N2_OF_NODE", "N3_OF_NODE"}
FailProneSet == {{"N1_OF_NODE"}, {"N3_OF_NODE"}}
Quorum  == {{"N1_OF_NODE", "N2_OF_NODE"}, {"N2_OF_NODE", "N3_OF_NODE"}}
BallotNumber == {0,1}

VARIABLES
    \* @typeAlias: ballot = {counter : Int, value : Int};
    \* @type: NODE -> Set($ballot);
    voteToPrepare,
    \* @type: NODE -> Set($ballot);
    acceptedPrepared,
    \* @type: NODE -> Set($ballot);
    voteToCommit,
    \* @type: NODE -> Set($ballot);
    acceptedCommitted,
    \* @type: NODE -> Set($ballot);
    externalized,
    \* @type: Set(NODE);
    byz

INSTANCE AbstractSCP

====================================================