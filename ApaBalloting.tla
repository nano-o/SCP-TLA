---------- MODULE ApaBalloting -----------

V == {0,1}
N == {"N1_OF_NODE", "N2_OF_NODE", "N3_OF_NODE"}
FailProneSet == {{"N1_OF_NODE"}, {"N3_OF_NODE"}}
\* FailProneSet == {{}}
Quorum  == {{"N1_OF_NODE", "N2_OF_NODE"}, {"N2_OF_NODE", "N3_OF_NODE"}}
BallotNumber == {0,1,2}

VARIABLES
    \* @type: NODE -> BALLOT;
    ballot
    \* @type: NODE -> Str;
,   phase
    \* @type: NODE -> BALLOT;
,   prepared
    \* @type: NODE -> Int;
,   aCounter
    \* @type: NODE -> BALLOT;
,   h
    \* @type: NODE -> BALLOT;
,   c
    \* @type: Set(MESSAGE);
,   sent
    \* @type: Set(NODE);
,   byz

INSTANCE Balloting

==========================================