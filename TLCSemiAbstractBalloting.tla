------ MODULE TLCSemiAbstractBalloting -----------

EXTENDS SemiAbstractBalloting, TLC

Canary1 == \neg (
    \E n \in N : \E b \in Ballot :
        b \in externalized[n]
)
    
Canary2 == \neg (
    \E Q \in Quorum : \E b \in Ballot : \A n \in Q :
        b \in acceptedCommitted[n]
)

CONSTANTS n1, n2, n3
N_MC == {n1, n2, n3}
Quorum_MC == {{n1,n2},{n2,n3}}
FailProneSet_MC == {{n1},{n3}}
Sym == Permutations({n1,n3})

========================================