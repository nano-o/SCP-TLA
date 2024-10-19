----------- MODULE ApaAbstractBalloting ------------------

V == {0,1,2}
N == {"N1_OF_NODE", "N2_OF_NODE", "N3_OF_NODE"}
FailProneSet == {{"N1_OF_NODE"}, {"N3_OF_NODE"}}
Quorum  == {{"N1_OF_NODE", "N2_OF_NODE"}, {"N2_OF_NODE", "N3_OF_NODE"}}
BallotNumber == {0,1,2,3}

VARIABLES
    \* @typeAlias: ballot = {counter : Int, value : Int};
    \* @type: NODE -> Set($ballot);
    voteToAbort,
    \* @type: NODE -> Set($ballot);
    acceptedAborted,
    \* @type: NODE -> Set($ballot);
    confirmedAborted,
    \* @type: NODE -> Set($ballot);
    voteToCommit,
    \* @type: NODE -> Set($ballot);
    acceptedCommitted,
    \* @type: NODE -> Set($ballot);
    externalized,
    \* @type: Set(NODE);
    byz

INSTANCE AbstractBalloting

====================================================