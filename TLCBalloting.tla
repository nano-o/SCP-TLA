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

\* Interesting states to start from:
S1 ==
/\ phase = (n1 :> "PREPARE" @@ n2 :> "PREPARE" @@ n3 :> "PREPARE")
/\ byz = {}
/\ c = ( n1 :> [counter |-> -1, value |-> 0] @@
  n2 :> [counter |-> -1, value |-> 0] @@
  n3 :> [counter |-> -1, value |-> 0] )
/\ h = ( n1 :> [counter |-> -1, value |-> 0] @@
  n2 :> [counter |-> 1, value |-> 0] @@
  n3 :> [counter |-> -1, value |-> 0] )
/\ aCounter = (n1 :> 1 @@ n2 :> 1 @@ n3 :> 1)
/\ sent = ( n1 :>
      { [ type |-> "PREPARE",
          ballot |-> [counter |-> 1, value |-> 0],
          prepared |-> [counter |-> -1, value |-> 0],
          aCounter |-> 0,
          hCounter |-> 0,
          cCounter |-> 0 ],
        [ type |-> "PREPARE",
          ballot |-> [counter |-> 2, value |-> 1],
          prepared |-> [counter |-> 1, value |-> 0],
          aCounter |-> 0,
          hCounter |-> 0,
          cCounter |-> 0 ],
        [ type |-> "PREPARE",
          ballot |-> [counter |-> 2, value |-> 1],
          prepared |-> [counter |-> 1, value |-> 1],
          aCounter |-> 1,
          hCounter |-> 0,
          cCounter |-> 0 ] } @@
  n2 :>
      { [ type |-> "PREPARE",
          ballot |-> [counter |-> 1, value |-> 0],
          prepared |-> [counter |-> -1, value |-> 0],
          aCounter |-> 0,
          hCounter |-> 0,
          cCounter |-> 0 ],
        [ type |-> "PREPARE",
          ballot |-> [counter |-> 1, value |-> 0],
          prepared |-> [counter |-> 1, value |-> 0],
          aCounter |-> 0,
          hCounter |-> 1,
          cCounter |-> 1 ] } @@
  n3 :>
      { [ type |-> "PREPARE",
          ballot |-> [counter |-> 2, value |-> 1],
          prepared |-> [counter |-> 1, value |-> 0],
          aCounter |-> 0,
          hCounter |-> 0,
          cCounter |-> 0 ],
        [ type |-> "PREPARE",
          ballot |-> [counter |-> 2, value |-> 1],
          prepared |-> [counter |-> 1, value |-> 1],
          aCounter |-> 1,
          hCounter |-> 0,
          cCounter |-> 0 ] } )
/\ prepared = ( n1 :> [counter |-> 1, value |-> 1] @@
  n2 :> [counter |-> 2, value |-> 1] @@
  n3 :> [counter |-> 1, value |-> 1] )
/\ ballot = ( n1 :> [counter |-> 2, value |-> 1] @@
  n2 :> [counter |-> 1, value |-> 0] @@
  n3 :> [counter |-> 2, value |-> 1] )

========================================