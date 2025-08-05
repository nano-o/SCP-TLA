------------- MODULE AbstractBallotingWithPrepare -------------

(**************************************************************************************)
(* This is a specification of SCP's balloting protocol. We work at a high level of    *)
(* abstraction where we do not explicitly model messages. Instead, we track what      *)
(* statements are voted/accepted prepared and committed by each node. What we do      *)
(* model explicitely is how each node n votes and accepts statements based on its     *)
(* current ballot ballot[n] and its highest confirmed-prepared ballot h[n].           *)
(*                                                                                    *)
(* We also do not model Byzantine behavior explicitly. Instead, whenever a node       *)
(* checks that a set (a quorum or a blocking set) voted or accepted a statement,      *)
(* it only checks that the non-Byzantine members of the set did so. This soundly      *)
(* models what could happen under Byzantine behavior because Byzantine nodes,         *)
(* being unconstrained, could have voted or accepted whatever is needed to make       *)
(* the check pass.                                                                    *)
(*                                                                                    *)
(* We provide an inductive invariant that implies the agreement property, and we      *)
(* check its inductiveness exhaustively for small instances of the domain model.      *)
(*                                                                                    *)
(* An informal specification of SCP can be found at:                                  *)
(* `^https://datatracker.ietf.org/doc/html/draft-mazieres-dinrg-scp-05\#section-3.5^' *)
(*                                                                                    *)
(* Finally, note that proving agreement is not very hard, but liveness relies on a    *)
(* trickier invariant (we prove that invariant, but not the full liveness             *)
(* property).                                                                         *)
(**************************************************************************************)

EXTENDS DomainModel

VARIABLES
    ballot
,   h
,   voteToPrepare
,   acceptedPrepared
,   voteToCommit
,   acceptedCommitted
,   externalized
,   byz \* the set of malicious nodes
,   syncBal \* a synchronous ballot

TypeOK ==
    /\  ballot \in [N -> BallotOrNull]
    /\  h \in [N -> BallotOrNull]
    /\  voteToPrepare \in [N -> SUBSET Ballot]
    /\  acceptedPrepared \in [N -> SUBSET Ballot]
    /\  voteToCommit \in [N -> SUBSET Ballot]
    /\  acceptedCommitted \in [N -> SUBSET Ballot]
    /\  externalized \in [N -> SUBSET Ballot]
    /\  byz \in SUBSET N
    /\  syncBal \in BallotNumber

Init ==
    /\ ballot = [n \in N |-> nullBallot] \* current ballot of each node
    /\ h =  [n \in N |-> nullBallot] \* current highest confirmed-prepared ballot of each node
    /\ voteToPrepare = [n \in N |-> {}]
    /\ acceptedPrepared = [n \in N |-> {}]
    /\ voteToCommit = [n \in N |-> {}]
    /\ acceptedCommitted = [n \in N |-> {}]
    /\ externalized = [n \in N |-> {}]
    /\ byz \in FailProneSet \* byz is initially set to an arbitrary fail-prone set
    /\ syncBal \in BallotNumber

(**************************************************************************************)
(* Node n enters a new ballot and votes to prepare it. Note that n votes to           *)
(* prepare its new ballot ballot'[n] regardless of whether it has previously voted    *)
(* to commit an incompatible ballot b. This is okay, as ballot'[n].value must be      *)
(* its highest confirmed prepared value.                                              *)
(**************************************************************************************)
IncreaseBallotCounter(n, c) ==
    /\  c > 0
    /\  c > ballot[n].counter
    /\  h[n].counter <= c
    /\  IF h[n] # nullBallot
        THEN ballot' = [ballot EXCEPT ![n] = bal(c, h[n].value)]
        ELSE \E v \in V : ballot' = [ballot EXCEPT ![n] = bal(c, v)]
    /\  voteToPrepare' = [voteToPrepare EXCEPT ![n] = @ \cup {ballot[n]'}]
    /\  UNCHANGED <<h, acceptedPrepared, voteToCommit, acceptedCommitted, externalized, byz, syncBal>>
    /\  syncBal # 0 => c <= syncBal

(***********************************************************************)
(* Next we describe when a node accepts and confirms ballots prepared. *)
(***********************************************************************)
AcceptPrepared(n, b, S) ==
    /\  \/ S \in Quorum /\ \A n2 \in S \ byz : b \in voteToPrepare[n2] \cup acceptedPrepared[n2]
        \/ S \in BlockingSet /\ \A n2 \in S \ byz : b \in acceptedPrepared[n2]
    \* For safety of intertwined but befouled validators (see the liveness invariant for why this does not hurt liveness):
    /\  \A b2 \in Ballot : LessThanAndIncompatible(b2, b) => b2 \notin acceptedCommitted[n]
    /\  acceptedPrepared' = [acceptedPrepared EXCEPT ![n] = @ \cup {b}]
    /\  UNCHANGED <<ballot, h, voteToPrepare, voteToCommit, acceptedCommitted, externalized, byz, syncBal>>

ConfirmPrepared(n, b, S) ==
    /\  b.counter > -1
    /\  h[n] \prec b
    /\  S \in Quorum /\ \A n2 \in S \ byz : b \in acceptedPrepared[n2]
    /\  h' = [h EXCEPT ![n] = b]
    /\  UNCHANGED <<ballot, voteToPrepare, acceptedPrepared, voteToCommit, acceptedCommitted, externalized, byz, syncBal>>

(**************************************************************************************)
(* When a node votes to commit a ballot, it must make sure it has confirmed it        *)
(* prepared. This is crucial to avoid externalizing two different values in two       *)
(* different ballots.                                                                 *)
(*                                                                                    *)
(* Note that b.counter is always larger or equal to the counter of any ballot         *)
(* voted, accepted, or confirmed, but it is still possible that something             *)
(* incompatible with b is accepted or confirmed with the same ballot counter.         *)
(**************************************************************************************)
VoteToCommit(n, S) == LET b == ballot[n] IN
    /\  b.counter > 0
    /\  b \preceq h[n] /\ b.value = h[n].value \* must have confirmed prepared
    /\  voteToCommit' = [voteToCommit EXCEPT ![n] = @ \cup {b}]
    /\  UNCHANGED <<ballot, h, voteToPrepare, acceptedPrepared, acceptedCommitted, externalized, byz, syncBal>>

(********************************************************************************)
(* Next we describe when a node accepts and confirms ballots committed. Nothing *)
(* surprising here.                                                             *)
(********************************************************************************)

AcceptCommitted(n, S) == LET b == ballot[n] IN
    /\  \/  S \in Quorum /\ \A n2 \in S \ byz : b \in voteToCommit[n2]
        \/  S \in BlockingSet /\ \A n2 \in S \ byz : b \in acceptedCommitted[n2]
    \* next two lines to ensure safety to intertwined but befouled validators:
    /\  b \preceq h[n] /\ h[n].value = b.value
    /\  \A b2 \in Ballot : LessThanAndIncompatible(b, b2) => b2 \notin acceptedPrepared[n]
    /\  acceptedCommitted' = [acceptedCommitted EXCEPT ![n] = @ \cup {b}]
    /\  UNCHANGED <<ballot, h, voteToPrepare, acceptedPrepared, voteToCommit, externalized, byz, syncBal>>

Externalize(n, S) == LET b == ballot[n] IN
    /\  S \in Quorum /\ \A n2 \in S \ byz : b \in acceptedCommitted[n2]
    /\  externalized' = [externalized EXCEPT ![n] = @ \cup {b}]
    /\  UNCHANGED <<ballot, h, voteToPrepare, acceptedPrepared, voteToCommit, acceptedCommitted, byz, syncBal>>

DropMessage(n, b) == \* TODO for use in liveness checking
    /\  \/  /\  \neg b = MaxBal({b2 \in Ballot : b2 \in voteToPrepare[n]})
            /\  voteToPrepare' = [voteToPrepare EXCEPT ![n] = voteToPrepare[n] \ {b}]
            /\  UNCHANGED <<acceptedPrepared, voteToCommit, acceptedCommitted>>
        \/  /\  \neg b = MaxBal({b2 \in Ballot : b2 \in acceptedPrepared[n]})
            /\  acceptedPrepared' = [acceptedPrepared EXCEPT ![n] = acceptedPrepared[n] \ {b}]
            /\  UNCHANGED <<voteToPrepare, voteToCommit, acceptedCommitted>>
        \/  /\  voteToCommit' = [voteToCommit EXCEPT ![n] = voteToCommit[n] \ {b}]
            /\  UNCHANGED <<voteToPrepare, acceptedPrepared, acceptedCommitted>>
        \/  /\  acceptedCommitted' = [acceptedCommitted EXCEPT ![n] = acceptedCommitted[n] \ {b}]
            /\  UNCHANGED <<voteToPrepare, acceptedPrepared, voteToCommit>>
    /\  UNCHANGED <<ballot, h, externalized, byz, syncBal>>

(***************************************)
(* Finally we put everything together: *)
(***************************************)
Next ==
    \/ \E n \in N \ byz, S \in SUBSET N :
        \/  VoteToCommit(n, S)
        \/  AcceptCommitted(n, S)
        \/  Externalize(n, S)
        \/  \E c \in BallotNumber, v \in V :
            LET b == bal(c, v) IN
                \* \/  DropMessage(n, b)
                \/  IncreaseBallotCounter(n, c)
                \/  AcceptPrepared(n, b, S)
                \/  ConfirmPrepared(n, b, S)

vars == <<ballot, h, voteToPrepare, acceptedPrepared, voteToCommit, acceptedCommitted, externalized, byz, syncBal>>

Spec == Init /\ [][Next]_vars

(***********************************************************************************)
(* The following blows up TLC because of the quantification over S, so we state it *)
(* in terms of concrete sets in the model-checking configuration spec.             *)
(***********************************************************************************)
LiveSpec ==
    /\  Init
    /\  [][Next]_vars
    \* this seems to blow up very bad because of the quantified set S:
    /\  \A n \in N : n \notin byz => \A S \in SUBSET N : S \cap byz = {} /\ S # {} =>
        /\  WF_vars( VoteToCommit(n, S) )
        /\  WF_vars( AcceptCommitted(n, S) )
        /\  WF_vars( Externalize(n, S) )
        /\  \A c \in BallotNumber :
            /\  WF_vars( IncreaseBallotCounter(n, c) )
            /\  \A v \in V : LET b == bal(c, v) IN
                /\  WF_vars( AcceptPrepared(n, b, S) )
                /\  WF_vars( ConfirmPrepared(n, b, S) )

(**********************************************************************************)
(* TODO: to find an exec in which dropping accept-prepare breaks liveness we need *)
(* to disable re-accepting prepared                                               *)
(**********************************************************************************)

Agreement ==
    \A n1,n2 \in N \ byz : \A b1,b2 \in Ballot :
        b1 \in externalized[n1] /\ b2 \in externalized[n2] => b1.value = b2.value

Liveness1 == syncBal # 0 => [](
    (\E n \in N : n \notin byz /\ h[n].counter > 0)
        => \E b \in Ballot : b.counter > 0 /\
                <>( \A n \in N : n \notin byz => h[n] = b ))

Liveness2 ==
    \A n \in N : syncBal # 0 /\ n \notin byz => <>(externalized[n] # {})

(**************************************************************************************)
(* Inductive invariant that implies agreement. TODO: there is a much simpler one.     *)
(* The "crux" property is useful but for liveness.                                    *)
(**************************************************************************************)

ConfirmedPrepared(b) ==
    \E Q \in Quorum : \A n \in Q \ byz : b \in acceptedPrepared[n]
AcceptedPrepared(b) ==
    \E Q \in Quorum : \A n \in Q \ byz : b \in voteToPrepare[n]
ConfirmedCommitted(b) ==
    \E Q \in Quorum : \A n \in Q \ byz : b \in acceptedCommitted[n]
AcceptedCommitted(b) ==
    \E Q \in Quorum : \A n \in Q \ byz : b \in voteToCommit[n]

AgreementInductiveInvariant ==
    /\  TypeOK
    /\  byz \in FailProneSet
    /\  \A n \in N \ byz, c1,c2 \in BallotNumber, v1,v2 \in V :
        LET b1 == bal(c1,v1) b2 == bal(c2,v2) IN
        /\  ballot[n].counter > -1 => ballot[n].counter > 0
        /\  b1 \in voteToPrepare[n] \/ b1 \in voteToCommit[n] =>
                /\  b1.counter > 0
                /\  b1.counter <= ballot[n].counter
                /\  b1.counter = ballot[n].counter => b1.value = ballot[n].value
        /\  h[n].counter > 0 => ConfirmedPrepared(h[n])
        /\  b1 \in externalized[n] => ConfirmedCommitted(b1)
        /\  bal(c1,v1) \in voteToPrepare[n] /\ bal(c1,v2) \in voteToPrepare[n] => v1 = v2
        /\  bal(c1,v1) \in voteToCommit[n] /\ bal(c1,v2) \in voteToCommit[n] => v1 = v2
        /\  b1 \in acceptedCommitted[n] => \E c3 \in BallotNumber : b1.counter <= c3 /\ ConfirmedPrepared(bal(c3, b1.value))
        /\  b2 \in acceptedPrepared[n] /\ LessThanAndIncompatible(b1,b2) => \neg b1 \in acceptedCommitted[n]
    \* Finally, our goal:
    /\  Agreement

(**************************************************************************************)
(* For liveness, the crux is that, in a synchronous Byzantine-free ballot, all        *)
(* well-behaved nodes end up setting h to the highest ballot that has been            *)
(* confirmed prepared by the system. This works because nodes are never prevented     *)
(* to accept something prepared by an incompatible ballot that is accepted            *)
(* committed, which we show here. In fact we show a stronger property: if a ballot    *)
(* is accepted prepare (i.e. voted prepared by a quorum), then no lower and           *)
(* incompatible ballot has been accepted committed.                                   *)
(**************************************************************************************)
LivenessInductiveInvariant ==
    \* First, the boring stuff:
    /\  TypeOK
    /\  byz \in FailProneSet
    /\  \A n \in N \ byz, c1,c2 \in BallotNumber, v1,v2 \in V :
        LET b1 == bal(c1,v1) b2 == bal(c2,v2) IN
        /\  ballot[n].counter > -1 => ballot[n].counter > 0
        /\  b1 \in voteToPrepare[n] \/ b1 \in voteToCommit[n] =>
                /\  b1.counter > 0
                /\  b1.counter <= ballot[n].counter
                /\  b1.counter = ballot[n].counter => b1.value = ballot[n].value
        /\  b1 \in acceptedPrepared[n] => AcceptedPrepared(b1)
        /\  b1 \in acceptedCommitted[n] => AcceptedCommitted(b1)
        /\  h[n].counter > 0 => ConfirmedPrepared(h[n])
        /\  b1 \in externalized[n] => ConfirmedCommitted(b1)
        /\  bal(c1,v1) \in voteToPrepare[n] /\ bal(c1,v2) \in voteToPrepare[n] => v1 = v2
        /\  bal(c1,v1) \in voteToCommit[n] /\ bal(c1,v2) \in voteToCommit[n] => v1 = v2
        \* Next, the two main invariants
        \* 1) votes to commit have been prepared:
        /\  b1 \in voteToCommit[n] =>
                /\  b1 \preceq h[n] \* important, because this means a higher incompatible prepare must be the result of having aborted b1 (because h[n] must have been updated)
                /\  \E c3 \in BallotNumber :
                        /\  b1.counter <= c3 \* TODO: why do we need <=?
                        /\  AcceptedPrepared(bal(c3, b1.value))
        \* 2) a node overrides "commit v" only if it is sure that "commit v" cannot reach quorum threshold:
        /\  /\  b1 \in voteToCommit[n]
            /\  LessThanAndIncompatible(b1, b2)
            /\  b2 \in voteToPrepare[n]
            =>  \A Q \in Quorum : \E n2 \in Q \ byz :
                    b1 \notin voteToCommit[n2] /\ ballot[n2].counter > b1.counter
        \* Finally, our goal:
        /\  /\  AcceptedPrepared(b2)
            /\  AcceptedCommitted(b1)
            /\  b1 \prec b2
            =>  b1.value = b2.value

==============================================
