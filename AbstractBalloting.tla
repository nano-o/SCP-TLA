------------- MODULE AbstractBalloting -------------

(**************************************************************************************)
(* This is a formalization of `^SCP^''s abstract balloting protocol described in      *)
(* Section 3.5 of the `^IETF^' draft at:                                              *)
(*                                                                                    *)
(* `^https://datatracker.ietf.org/doc/html/draft-mazieres-dinrg-scp-05\#section-3.5^' *)
(*                                                                                    *)
(* The goal if to then refine this specification to one that closely matches the      *)
(* concrete `^SCP^' protocol.                                                         *)
(*                                                                                    *)
(* We provide an inductive invariant showing that agreement is guaranteed.            *)
(*                                                                                    *)
(* Note that a node may vote to commit a ballot and later vote to abort the same      *)
(* ballot if it knows that commit cannot possibly reach quorum threshold. This can    *)
(* happen when a validator votes to commit a ballot, but then accepts to abort it.    *)
(* Moreover, it is necessary for liveness to allow this.                              *)
(*                                                                                    *)
(* Also note that we do not model Byzantine behavior explicitly. Instead, whenever    *)
(* a node checks that a set (a quorum or a blocking set) voted or accepted a          *)
(* statement, it only checks that the non-Byzantine members of the set did so.        *)
(* This soundly models what could happen under Byzantine behavior because             *)
(* Byzantine nodes, being unconstrained, could have voted or accepted whatever is     *)
(* needed to make the check pass.                                                     *)
(**************************************************************************************)

EXTENDS DomainModel

VARIABLES
    voteToAbort
,   acceptedAborted
,   voteToCommit
,   acceptedCommitted
,   externalized
,   byz

TypeOK ==
    /\  voteToAbort \in [N -> SUBSET Ballot]
    /\  acceptedAborted \in [N -> SUBSET Ballot]
    /\  voteToCommit \in [N -> SUBSET Ballot]
    /\  acceptedCommitted \in [N -> SUBSET Ballot]
    /\  externalized \in [N -> SUBSET Ballot]
    /\  byz \in SUBSET N

Init ==
    /\ voteToAbort = [n \in N |-> {}]
    /\ acceptedAborted = [n \in N |-> {}]
    /\ voteToCommit = [n \in N |-> {}]
    /\ acceptedCommitted = [n \in N |-> {}]
    /\ externalized = [n \in N |-> {}]
    /\ byz \in FailProneSet


(********************************************************************************)
(* The second disjunct allows voting to commit all higher ballot numbers once a *)
(* ballot is accepted committed (see meaning of COMMIT message in the `^IETF^'  *)
(* draft):                                                                      *)
(********************************************************************************)
IsPrepared(n, b1) ==
        \/  \A b2 \in Ballot : LessThanAndIncompatible(b2, b1) => 
                \E Q \in Quorum : \A n2 \in Q \ byz : b2 \in acceptedAborted[n2]
        \/ \E cnt \in BallotNumber : 
            /\ [counter |-> cnt, value |-> b1.value] \in acceptedCommitted[n]
            /\  cnt < b1.counter \* really necessary? yes

Step(n) ==
    /\  UNCHANGED <<byz>>
    \* NOTE for TLC, we must update acceptedAborted before voteToAbort,
    \* because updating voteToAbort depends on acceptedAborted':
    /\  \E B \in SUBSET Ballot :
        /\  \A b \in B :
            /\  \/ \E Q \in Quorum : \A n2 \in Q \ byz : b \in voteToAbort[n2] \cup acceptedAborted[n2]
                \/ \E Bl \in BlockingSet : \A n2 \in Bl \ byz : b \in acceptedAborted[n2]
        /\  acceptedAborted' = [acceptedAborted EXCEPT ![n] = @ \cup B]
    /\ \E B \in SUBSET Ballot :
        /\  \A b \in B : b \notin voteToCommit[n] \/ b \in acceptedAborted'[n]
        /\  voteToAbort' = [voteToAbort EXCEPT ![n] = @ \cup B]
    \* NOTE for TLC, we must update acceptedCommitted before voteToCommit,
    \* because updating voteToCommit depends on acceptedCommitted':
    /\  \E B \in SUBSET Ballot :
        /\  \A b \in B :
            /\  \/ \E Q \in Quorum : \A n2 \in Q \ byz : b \in voteToCommit[n2] \cup acceptedCommitted[n2]
                \/ \E Bl \in BlockingSet : \A n2 \in Bl \ byz : b \in acceptedCommitted[n2]
        /\  acceptedCommitted' = [acceptedCommitted EXCEPT ![n] = @ \cup B]
    /\  \E B \in SUBSET Ballot :
        /\  \A b \in B :
            /\  b.counter > 0 \* we start at ballot 1
             \* if the ballot is already aborted, don't vote to commit
             \* (using the primed version ensures we don't vote to commit and abort at the same time):
            /\  b \notin voteToAbort'[n] \cup acceptedAborted'[n]
             \* the prime allows us to consider prepared something we accepted committed in this very step:
            /\  IsPrepared(n, b)'
        /\  voteToCommit' = [voteToCommit EXCEPT ![n] = @ \cup B]
        \* we vote to commit at most one value per ballot number:
        /\  \A b1,b2 \in voteToCommit'[n] : b1.counter = b2.counter => b1.value = b2.value
    /\  \E B \in SUBSET Ballot :
        /\  \A b \in B : \E Q \in Quorum :
                \A n2 \in Q \ byz : b \in acceptedCommitted[n2]
        /\  externalized' = [externalized EXCEPT ![n] = @ \cup B]

Next ==
    \/ \E n \in N \ byz : Step(n)

vars == <<voteToAbort, acceptedAborted, voteToCommit, acceptedCommitted, externalized, byz>>

Spec == Init /\ [][Next]_vars

Agreement ==
    \A n1,n2 \in N \ byz : \A b1,b2 \in Ballot :
        b1 \in externalized[n1] /\ b2 \in externalized[n2] => b1.value = b2.value

\* Inductive invariant proving safety:
InductiveInvariant ==
    /\  TypeOK
    /\  byz \in FailProneSet
    /\  \A n \in N \ byz :
        /\  \A b \in Ballot :
            /\  b \in voteToCommit[n] => b \notin voteToAbort[n] \/ b \in acceptedAborted[n]
            /\  b \in voteToCommit[n] \cup acceptedCommitted[n] \cup externalized[n] => b.counter > 0
            /\  \A b2 \in Ballot :
                    b \in voteToCommit[n] /\ b2 \in voteToCommit[n] /\ b # b2 => b.counter # b2.counter
            /\  b \in acceptedAborted[n] => \E Q \in Quorum :
                    \A n2 \in Q \ byz : b \in voteToAbort[n2]
            /\  b \in acceptedCommitted[n] => \E Q \in Quorum :
                    \A n2 \in Q \ byz : b \in voteToCommit[n2]
            /\  b \in externalized[n] => \E Q \in Quorum :
                    \A n2 \in Q \ byz : b \in acceptedCommitted[n2]
            /\  b \in voteToCommit[n] =>
                \/  b.counter = 1
                \/  \A b2 \in Ballot : LessThanAndIncompatible(b2, b) =>
                        \E Q \in Quorum : \A n2 \in Q \ byz : b2 \in acceptedAborted[n2]
                \/  \E cnt \in BallotNumber :
                    /\  cnt < b.counter
                    /\  [counter |-> cnt, value |-> b.value] \in acceptedCommitted[n]
            /\  b \in acceptedAborted[n] => \A Q \in Quorum : \E n2 \in Q \ byz : b \notin voteToCommit[n2]
    /\  Agreement

==============================================