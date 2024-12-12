--------- MODULE TLCAbstractBallotingWithPrepare ---------


EXTENDS AbstractBallotingWithPrepare, TLC

CONSTANTS n1, n2, n3
N_MC == {n1, n2, n3}
Quorum_MC == {{n1,n2},{n2,n3}}
FailProneSet_MC == {{n1},{n3}}
\* Quorum_MC == {{n1,n2},{n2,n3}}
\* FailProneSet_MC == {{n1},{n3}}
\* FailProneSet_MC == {{}}

\* CONSTANTS n1, n2, n3
\* N_MC == {n1, n2, n3}
\* Quorum_MC == {{n1,n2,n3}}
\* FailProneSet_MC == {{n3}}

\* CONSTANTS n1, n2, n3, n4
\* N_MC == {n1, n2, n3, n4}
\* Quorum_MC == {{n1,n2,n4},{n1,n3,n4}}
\* FailProneSet_MC == {{n4}}

Canary1 == \neg (
    \E n \in N \ byz : externalized[n] # {}
)


==========================================================