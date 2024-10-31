---------- MODULE ApaBalloting -----------

EXTENDS Balloting

V == {0,1}
N == {"N1_OF_NODE", "N2_OF_NODE", "N3_OF_NODE"}
FailProneSet == {{"N1_OF_NODE"}, {"N3_OF_NODE"}}
\* FailProneSet == {{}}
Quorum  == {{"N1_OF_NODE", "N2_OF_NODE"}, {"N2_OF_NODE", "N3_OF_NODE"}}
BallotNumber == {0,1,2}

VARIABLES


==========================================