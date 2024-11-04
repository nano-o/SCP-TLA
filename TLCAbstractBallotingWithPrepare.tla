--------- MODULE TLCAbstractBallotingWithPrepare ---------


EXTENDS AbstractBallotingWithPrepare, TLC

CONSTANTS n1, n2, n3
N_MC == {n1, n2, n3}
Quorum_MC == {{n1,n2},{n2,n3}}
FailProneSet_MC == {{n1},{n3}}
\* FailProneSet_MC == {{}}
\* Sym == Permutations({n1,n2,n3})

Canary1 == \neg (
    \E n \in N \ byz : externalized[n] # {}
)


==========================================================