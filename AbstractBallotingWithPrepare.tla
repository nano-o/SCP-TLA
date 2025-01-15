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
(* Next step would be to model how nodes summarize what they have accepted            *)
(* prepared. Can we also model the fact that nodes only keep the latest message of    *)
(* each other node? Maybe this could be done by non-deterministically erasing past    *)
(* statements.                                                                        *)
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
    \* /\ syncBal = 0

(***********************************************************************************)
(* Node n enters a new ballot and votes to prepare it. Note that n votes to        *)
(* prepare its new ballot ballot'[n] regardless of whether it has previously voted *)
(* to commit an incompatible ballot b. The main subtlety of the protocol is that   *)
(* this is okay because:                                                           *)
(*                                                                                 *)
(*     1) We must have b \prec h[n] because, when n votes to commit b (see         *)
(*     VoteToCommit), it sets h[n] = b if h[n] \prec b, and subsequently h[n] can  *)
(*     only grow, and                                                              *)
(*                                                                                 *)
(*     2) therefore, if h[n].value # b.value, then n confirmed h[n] as prepared    *)
(*     (by definition of how h[n] is updated) and thus we know that, even though n *)
(*     voted to commit b, b can never gather a quorum of votes to commit.          *)
(*                                                                                 *)
(* Note how this reasoning appears in the inductive invariant below.               *)
(***********************************************************************************)

IncreaseBallotCounter(n, c) ==
    /\  c > 0
    /\  syncBal # 0 => c <= syncBal
    /\  c > ballot[n].counter
    /\  h[n].counter <= c
    /\  IF h[n] # nullBallot
        THEN ballot' = [ballot EXCEPT ![n] = bal(c, h[n].value)]
        ELSE \E v \in V : ballot' = [ballot EXCEPT ![n] = bal(c, v)]
    /\  voteToPrepare' = [voteToPrepare EXCEPT ![n] = @ \cup {ballot[n]'}]
    /\  UNCHANGED <<h, acceptedPrepared, voteToCommit, acceptedCommitted, externalized, byz, syncBal>>

(***********************************************************************)
(* Next we describe when a node accepts and confirms ballots prepared. *)
(***********************************************************************)
AcceptPrepared(n, b, S) ==
    /\  \/ S \in Quorum /\ \A n2 \in S \ byz : b \in voteToPrepare[n2] \cup acceptedPrepared[n2]
        \/ S \in BlockingSet /\ \A n2 \in S \ byz : b \in acceptedPrepared[n2]
    \* For safety of intertwined but befouled validators (see LivenessInv1 for why this does not hurt liveness):
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
    /\  S \in Quorum /\ \A n2 \in S \ byz : b \in acceptedPrepared[n2] \* TODO should be redundant, but fails without it.
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
    /\  b \in acceptedPrepared[n] \* TODO: shouldn't this be confirmed prepared?
    /\  \A b2 \in Ballot : LessThanAndIncompatible(b, b2) => b2 \notin acceptedPrepared[n]
    /\  acceptedCommitted' = [acceptedCommitted EXCEPT ![n] = @ \cup {b}]
    /\  UNCHANGED <<ballot, h, voteToPrepare, acceptedPrepared, voteToCommit, externalized, byz, syncBal>>

Externalize(n, S) == LET b == ballot[n] IN
    /\  S \in Quorum /\ \A n2 \in S \ byz : b \in acceptedCommitted[n2]
    /\  externalized' = [externalized EXCEPT ![n] = @ \cup {b}]
    /\  UNCHANGED <<ballot, h, voteToPrepare, acceptedPrepared, voteToCommit, acceptedCommitted, byz, syncBal>>

DropMessage(n, b) ==
    /\  \/  /\  voteToPrepare' = [voteToPrepare EXCEPT ![n] = voteToPrepare[n] \ {b}]
            /\  UNCHANGED <<acceptedPrepared, voteToCommit, acceptedCommitted>>
        \* never drop the latest message:
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
    \* \/ ByzantineHavoc
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
InductiveInvariant ==
    \* First, the boring stuff:
    /\  TypeOK
    /\  byz \in FailProneSet
    /\  \A n \in N \ byz, c1,c2 \in BallotNumber, v1,v2 \in V :
        LET b1 == bal(c1,v1) b2 == bal(c2,v2) IN
        /\  ballot[n].counter > -1 => ballot[n].counter > 0
        /\  b1 \in voteToPrepare[n] \/ b1 \in voteToCommit[n] => b1.counter > 0 /\ b1.counter <= ballot[n].counter
        /\  b1 \in acceptedPrepared[n] => \E Q \in Quorum : \A n2 \in Q \ byz : b1 \in voteToPrepare[n2]
        /\  b1 \in acceptedCommitted[n] => \E Q \in Quorum : \A n2 \in Q \ byz : b1 \in voteToCommit[n2]
        /\  h[n].counter > 0 => \E Q \in Quorum : \A n2 \in Q \ byz : h[n] \in acceptedPrepared[n2]
        /\  b1 \in externalized[n] => \E Q \in Quorum : \A n2 \in Q \ byz : b1 \in acceptedCommitted[n2]
        /\  b1 \in voteToPrepare[n] \/ b1 \in voteToCommit[n] =>
            /\  b1.counter <= ballot[n].counter
            /\  b1.counter = ballot[n].counter => b1.value = ballot[n].value
        /\  bal(c1,v1) \in voteToPrepare[n] /\ bal(c1,v2) \in voteToPrepare[n] => v1 = v2
        /\  bal(c1,v1) \in voteToCommit[n] /\ bal(c1,v2) \in voteToCommit[n] => v1 = v2
        /\  b1 \in voteToCommit[n] =>
                /\  \E Q \in Quorum : \A n2 \in Q \ byz : b1 \in acceptedPrepared[n2]
                /\  b1 \preceq h[n] \* note this is important
        \* Next, the crux of the matter:
        \* (in short, a node overrides "commit v" only if it is sure that "commit v" cannot reach quorum threshold)
        /\  /\  b1 \in voteToCommit[n]
            /\  LessThanAndIncompatible(b1, b2)
            /\  b2 \in voteToPrepare[n]
            =>  \A Q \in Quorum : \E n2 \in Q \ byz :
                    b1 \notin voteToCommit[n2] /\ ballot[n2].counter > b1.counter
    \* Finally, our goal:
    /\  Agreement

Inv ==
    \* /\  byz \in FailProneSet
    /\  \A n \in N \ byz, c1,c2 \in BallotNumber, v1,v2 \in V :
        LET b1 == bal(c1,v1) b2 == bal(c2,v2) IN
    \*     /\  ballot[n].counter > -1 => ballot[n].counter > 0
    \*     /\  b1 \in voteToPrepare[n] \/ b1 \in voteToCommit[n] => b1.counter > 0 /\ b1.counter <= ballot[n].counter
    \*     /\  b1 \in acceptedPrepared[n] => \E Q \in Quorum : \A n2 \in Q \ byz : b1 \in voteToPrepare[n2]
    \*     /\  b1 \in acceptedCommitted[n] => \E Q \in Quorum : \A n2 \in Q \ byz : b1 \in voteToCommit[n2]
    \*     /\  h[n].counter > 0 => \E Q \in Quorum : \A n2 \in Q \ byz : h[n] \in acceptedPrepared[n2]
    \*     /\  b1 \in externalized[n] => \E Q \in Quorum : \A n2 \in Q \ byz : b1 \in acceptedCommitted[n2]
    \*     /\  b1 \in voteToPrepare[n] \/ b1 \in voteToCommit[n] =>
    \*         /\  b1.counter <= ballot[n].counter
    \*         /\  b1.counter = ballot[n].counter => b1.value = ballot[n].value
    \*     /\  bal(c1,v1) \in voteToPrepare[n] /\ bal(c1,v2) \in voteToPrepare[n] => v1 = v2
    \*     /\  bal(c1,v1) \in voteToCommit[n] /\ bal(c1,v2) \in voteToCommit[n] => v1 = v2
        \* /\  b1 \in voteToCommit[n] =>
        \*         /\  \E Q \in Quorum : \A n2 \in Q \ byz : b1 \in acceptedPrepared[n2]
        \*         /\  b1 \preceq h[n] \* note this is important
        \* Next, the crux of the matter:
        \* (in short, a node overrides "commit v" only if it is sure that "commit v" cannot reach quorum threshold)
        /\  /\  b1 \in voteToCommit[n]
            /\  LessThanAndIncompatible(b1, b2)
            /\  b2 \in voteToPrepare[n]
            =>  \A Q \in Quorum : \E n2 \in Q \ byz :
                    b1 \notin voteToCommit[n2] /\ ballot[n2].counter > b1.counter
Inv_pre ==
    /\  TypeOK
    /\  byz \in FailProneSet
    /\  \A n \in N \ byz, c1,c2 \in BallotNumber, v1,v2 \in V :
        LET b1 == bal(c1,v1) b2 == bal(c2,v2) IN
        /\  ballot[n].counter > -1 => ballot[n].counter > 0
        /\  b1 \in voteToPrepare[n] \/ b1 \in voteToCommit[n] => b1.counter > 0 /\ b1.counter <= ballot[n].counter
        /\  b1 \in acceptedPrepared[n] => \E Q \in Quorum : \A n2 \in Q \ byz : b1 \in voteToPrepare[n2]
        /\  b1 \in acceptedCommitted[n] => \E Q \in Quorum : \A n2 \in Q \ byz : b1 \in voteToCommit[n2]
        /\  h[n].counter > 0 => \E Q \in Quorum : \A n2 \in Q \ byz : h[n] \in acceptedPrepared[n2]
        /\  b1 \in externalized[n] => \E Q \in Quorum : \A n2 \in Q \ byz : b1 \in acceptedCommitted[n2]
        /\  b1 \in voteToPrepare[n] \/ b1 \in voteToCommit[n] =>
            /\  b1.counter <= ballot[n].counter
            /\  b1.counter = ballot[n].counter => b1.value = ballot[n].value
        /\  bal(c1,v1) \in voteToPrepare[n] /\ bal(c1,v2) \in voteToPrepare[n] => v1 = v2
        /\  bal(c1,v1) \in voteToCommit[n] /\ bal(c1,v2) \in voteToCommit[n] => v1 = v2
        /\  b1 \in voteToCommit[n] =>
                /\  \E Q \in Quorum : \A n2 \in Q \ byz : b1 \in acceptedPrepared[n2]
                /\  b1 \preceq h[n] \* note this is important
        \* Next, the crux of the matter:
        \* (in short, a node overrides "commit v" only if it is sure that "commit v" cannot reach quorum threshold)
        /\  /\  b1 \in voteToCommit[n]
            /\  LessThanAndIncompatible(b1, b2)
            /\  b2 \in voteToPrepare[n]
            =>  \A Q \in Quorum : \E n2 \in Q \ byz :
                    b1 \notin voteToCommit[n2] /\ ballot[n2].counter > b1.counter

(***********************************************************************)
(* LivenessInv1 shows that AcceptPrepared is never blocked by a lower, *)
(* incompatible ballot that is accepted committed.                     *)
(***********************************************************************)
LivenessInv1 == \A b1,b2 \in Ballot, n1 \in N \ byz :
    /\  \E Q \in Quorum : \A n2 \in Q \ byz : b2 \in voteToPrepare[n2]
    /\  b1 \in acceptedCommitted[n1]
    /\  b1 \prec b2
    =>  b1.value = b2.value

==============================================
