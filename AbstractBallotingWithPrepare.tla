------------- MODULE AbstractBallotingWithPrepare -------------

(**************************************************************************************)
(* This is a specification of SCP's balloting protocol. We work at a high level of    *)
(* abstraction where we do not explicitely model messages. Instead, we track what     *)
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

TypeOK ==
    /\  ballot \in [N -> BallotOrNull]
    /\  h \in [N -> BallotOrNull]
    /\  voteToPrepare \in [N -> SUBSET Ballot]
    /\  acceptedPrepared \in [N -> SUBSET Ballot]
    /\  voteToCommit \in [N -> SUBSET Ballot]
    /\  acceptedCommitted \in [N -> SUBSET Ballot]
    /\  externalized \in [N -> SUBSET Ballot]
    /\  byz \in SUBSET N

Init ==
    /\ ballot = [n \in N |-> nullBallot] \* current ballot of each node
    /\ h =  [n \in N |-> nullBallot] \* current highest confirmed-prepared ballot of each node
    /\ voteToPrepare = [n \in N |-> {}]
    /\ acceptedPrepared = [n \in N |-> {}]
    /\ voteToCommit = [n \in N |-> {}]
    /\ acceptedCommitted = [n \in N |-> {}]
    /\ externalized = [n \in N |-> {}]
    /\ byz \in FailProneSet \* byz is initially set to an arbitrary fail-prone set

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
    /\  c > ballot[n].counter
    /\  h[n].counter <= c
    /\  IF h[n] # nullBallot
        THEN ballot' = [ballot EXCEPT ![n] = bal(c, h[n].value)]
        ELSE \E v \in V : ballot' = [ballot EXCEPT ![n] = bal(c, v)]
    /\  voteToPrepare' = [voteToPrepare EXCEPT ![n] = @ \cup {ballot[n]'}]
    /\  UNCHANGED <<h, acceptedPrepared, voteToCommit, acceptedCommitted, externalized, byz>>

(**********************************************************************************)
(* Next we describe when a node accepts and confirms ballots prepared. Nothing    *)
(* surprising here.                                                               *)
(*                                                                                *)
(* Note that we could check that nothing less-and-incompatible is accepted        *)
(* committed. That would simplify the agreement proof but complicate the liveness *)
(* proof. In any case, it is an invariant that nothing less-and-incompatible is   *)
(* accepted committed at this point (see AcceptNeverContradictory).               *)
(**********************************************************************************)
AcceptPrepared(n, b) ==
    /\  \/ \E Q \in Quorum : \A n2 \in Q \ byz : b \in voteToPrepare[n2] \cup acceptedPrepared[n2]
        \/ \E Bl \in BlockingSet : \A n2 \in Bl \ byz : b \in acceptedPrepared[n2]
    /\  acceptedPrepared' = [acceptedPrepared EXCEPT ![n] = @ \cup {b}]
    /\  UNCHANGED <<ballot, h, voteToPrepare, voteToCommit, acceptedCommitted, externalized, byz>>

ConfirmPrepared(n, b) ==
    /\  b.counter > -1
    /\  h[n] \prec b
    /\  \E Q \in Quorum : \A n2 \in Q \ byz : b \in acceptedPrepared[n2]
    /\  h' = [h EXCEPT ![n] = b]
    /\  UNCHANGED <<ballot, voteToPrepare, acceptedPrepared, voteToCommit, acceptedCommitted, externalized, byz>>

(*******************************************************************************)
(* When a node votes to commit a ballot, it must check that it has not already *)
(* voted or accepted to abort it. This is crucial to avoid externalizing two   *)
(* different values in two different ballots. We also update h[n] if needed to *)
(* reflect the new highest-confirmed prepared ballot.                          *)
(*******************************************************************************)
VoteToCommit(n) == LET b == ballot[n] IN
    /\  b.counter > 0
    /\  \A b2 \in Ballot : LessThanAndIncompatible(b, b2) =>
            b2 \notin voteToPrepare[n] \cup acceptedPrepared[n]
    /\  b \prec h[n] => b.value = h[n].value
    /\  \E Q \in Quorum : \A n2 \in Q \ byz : b \in acceptedPrepared[n2]
    /\  voteToCommit' = [voteToCommit EXCEPT ![n] = @ \cup {b}]
    /\  IF h[n] \preceq b
        THEN h' = [h EXCEPT ![n] = b]
        ELSE UNCHANGED h
    /\  UNCHANGED <<ballot, voteToPrepare, acceptedPrepared, acceptedCommitted, externalized, byz>>

(********************************************************************************)
(* Next we describe when a node accepts and confirms ballots committed. Nothing *)
(* surprising here.                                                             *)
(********************************************************************************)

AcceptCommitted(n) == LET b == ballot[n] IN
    /\  \/  \E Q \in Quorum : \A n2 \in Q \ byz : b \in voteToCommit[n2]
        \/  \E Bl \in BlockingSet : \A n2 \in Bl \ byz : b \in acceptedCommitted[n2]
    /\  acceptedCommitted' = [acceptedCommitted EXCEPT ![n] = @ \cup {b}]
    /\  UNCHANGED <<ballot, h, voteToPrepare, acceptedPrepared, voteToCommit, externalized, byz>>

Externalize(n) == LET b == ballot[n] IN
    /\  \E Q \in Quorum : \A n2 \in Q \ byz : b \in acceptedCommitted[n2]
    /\  externalized' = [externalized EXCEPT ![n] = @ \cup {b}]
    /\  UNCHANGED <<ballot, h, voteToPrepare, acceptedPrepared, voteToCommit, acceptedCommitted, byz>>

(***************************************)
(* Finally we put everything together: *)
(***************************************)
Next == \E n \in N \ byz :
    \/  VoteToCommit(n)
    \/  AcceptCommitted(n)
    \/  Externalize(n)
    \/  \E c \in BallotNumber, v \in V :
        LET b == bal(c, v) IN
            \/  IncreaseBallotCounter(n, c)
            \/  AcceptPrepared(n, b)
            \/  ConfirmPrepared(n, b)

vars == <<ballot, h, voteToPrepare, acceptedPrepared, voteToCommit, acceptedCommitted, externalized, byz>>

Spec == Init /\ [][Next]_vars

Agreement ==
    \A n1,n2 \in N \ byz : \A b1,b2 \in Ballot :
        b1 \in externalized[n1] /\ b2 \in externalized[n2] => b1.value = b2.value

(**********************************************************)
(* Here is an inductive invariant that implies agreement: *)
(**********************************************************)
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

\* An additional property implies by the inductive invariant:
AcceptNeverContradictory == \A b1,b2 \in Ballot, n1,n2 \in N \ byz :
    /\  b1 \in acceptedCommitted[n1]
    /\  b2 \in acceptedPrepared[n2]
    /\  b1 \prec b2
    =>  b1.value = b2.value

==============================================