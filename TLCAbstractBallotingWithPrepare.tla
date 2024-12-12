--------- MODULE TLCAbstractBallotingWithPrepare ---------


EXTENDS AbstractBallotingWithPrepare, TLC

CONSTANTS n1, n2, n3
N_MC == {n1, n2, n3}
Quorum_MC == {{n1,n2},{n2,n3}}
FailProneSet_MC == {{n1}}
(*****************************************************************************)
(* Below, we need S to range over concrete sets otherwise TLC's memory usage *)
(* explodes. This is why we restate the live spec here.                      *)
(*****************************************************************************)
ConcreteLiveSpec ==
    /\  Init
    /\  [][Next]_vars
    /\  \A n \in N : n \notin byz =>
        /\  \A c \in BallotNumber :
            /\  WF_vars( IncreaseBallotCounter(n, c) )
            /\   \A S \in {{n2},{n2,n3}}, v \in V : LET b == bal(c, v) IN
                /\  WF_vars( AcceptPrepared(n, b, S) )
                /\  WF_vars( ConfirmPrepared(n, b, S) )

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