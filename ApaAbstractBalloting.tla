----------- MODULE ApaAbstractBalloting ------------------

V == {0,1}
N == {"N1_OF_NODE", "N2_OF_NODE", "N3_OF_NODE"}
\* N == {"N1_OF_NODE"}
FailProneSet == {{"N1_OF_NODE"}, {"N3_OF_NODE"}}
\* FailProneSet == {{}}
Quorum  == {{"N1_OF_NODE", "N2_OF_NODE"}, {"N2_OF_NODE", "N3_OF_NODE"}}
\* Quorum == {N}
BallotNumber == {0,1,2}

VARIABLES
    \* @typeAlias: ballot = {counter : Int, value : Int};
    \* @type: NODE -> $ballot -> Bool;
    voteToAbort,
    \* @type: NODE -> $ballot -> Bool;
    acceptedAborted,
    \* @type: NODE -> $ballot -> Bool;
    voteToCommit,
    \* @type: NODE -> $ballot -> Bool;
    acceptedCommitted,
    \* @type: NODE -> $ballot -> Bool;
    externalized,
    \* @type: Set(NODE);
    byz

INSTANCE AbstractBalloting

====================================================