------ MODULE TLCAbstractBalloting -----------

EXTENDS AbstractBalloting, TLC

Canary1 == \neg (
    \E n \in N : \E b \in Ballot :
        b \in externalized[n]
)
    
Canary2 == \neg (
    \E n \in N : \E b \in Ballot : b \in acceptedCommitted[n]
)

CONSTANTS n1, n2, n3
N_MC == {n1, n2, n3}
Quorum_MC == {{n1,n2},{n2,n3}}
\* FailProneSet_MC == {{n1},{n3}}
FailProneSet_MC == {{}}
Sym == Permutations({n1,n3})

========================================