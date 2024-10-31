------ MODULE TLCBalloting -----------

EXTENDS Balloting, TLC

CONSTANTS n1, n2, n3
N_MC == {n1, n2, n3}
Quorum_MC == {{n1,n2},{n2,n3},{n1,n3}}
\* FailProneSet_MC == {{n1},{n3}}
FailProneSet_MC == {{}}
Sym == Permutations({n1,n2,n3})

\* Debugging canaries:

Canary1 == \neg (
    \E n \in N \ byz : phase[n] = "COMMIT"
)
Canary2 == \neg (
    \E n \in N \ byz : \E msg \in sent[n] :
        /\  msg.type = "PREPARE"
        /\  msg.cCounter = 1
)
Canary3 == \neg (
    \E Q \in Quorum : \A n \in Q \ byz : c[n].counter = 1
)

========================================