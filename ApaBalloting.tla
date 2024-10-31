---------- MODULE ApaBalloting -----------

V == {0,1}
N == {"N1_OF_NODE", "N2_OF_NODE", "N3_OF_NODE"}
FailProneSet == {{"N1_OF_NODE"}, {"N3_OF_NODE"}}
\* FailProneSet == {{}}
Quorum  == {{"N1_OF_NODE", "N2_OF_NODE"}, {"N2_OF_NODE", "N3_OF_NODE"}}
BallotNumber == {0,1}

INSTANCE DomainModel

VARIABLES
    \* @type: NODE -> $ballot;
    ballot
,   \* @type: NODE -> Str;
    phase
,   \* @type: NODE -> $ballot;
    prepared
,   \* @type: NODE -> Int;
    aCounter
,   \* @type: NODE -> $ballot;
    h
,   \* @type: NODE -> $ballot;
    c
,   \* @type: NODE -> Set($message);
    sent
,   \* @type: Set(NODE);
    byz

INSTANCE Balloting

==========================================