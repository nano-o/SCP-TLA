----------------------------- MODULE Balloting -----------------------------

(**************************************************)
(* Specification of SCP following the IETF draft. *)
(**************************************************)

\* TODO: should we use refinement from a more abstract spec that follows the Ivy one? Probably yes.

EXTENDS Integers, FiniteSets

CONSTANTS
    N \* nodes
,   V \* values (the goal of the protocol is to agree on a value)
,   BallotNumber \* the set of ballot numbers (i.e. the integers)
,   Quorum
,   FailProneSet

\* ASSUME \E n \in Nat : BallotNumber = 0..n

Quorums(n) == Quorum
BlockingSets(n) == {B \in SUBSET N :
    \A Q \in Quorum : Q \cap B # {}}
someValue == CHOOSE v \in V : TRUE
Ballot == [counter : BallotNumber, value : V]
BallotOrNull == [counter : BallotNumber\cup {-1}, value : V]
Max(x, y) == IF x > y THEN x ELSE y

\* LessThan predicate for comparing two ballots
\* @type: ({counter : Int, value : Int}, {counter : Int, value : Int}) => Bool;
LessThan(b1, b2) ==
    b1.counter < b2.counter \/ (b1.counter = b2.counter /\ b1.value < b2.value)
LowerAndIncompatible(b1, b2) ==
    LessThan(b1, b2) /\ b1.value # b2.value

Phase == {"PREPARE", "COMMIT", "EXTERNALIZE"}

SCPPrepare == [
    type : {"PREPARE"}
,   ballot : Ballot
,   prepared : BallotOrNull
,   aCounter : BallotNumber
,   hCounter : BallotNumber
,   cCounter : BallotNumber]

SCPCommit == [
    type : {"COMMIT"}
,   ballot : Ballot
,   preparedCounter : BallotNumber
,   hCounter : BallotNumber
,   cCounter : BallotNumber]

SCPExternalize == [
    type : {"EXTERNALIZE"}
,   commit : Ballot
,   hCounter : BallotNumber]

Message ==
    SCPPrepare \cup SCPCommit \cup SCPExternalize

VARIABLES
    ballot \* ballot[n] is the current ballot being prepared or committed by node n
,   phase  \* phase[n] is the current phase of node n
,   prepared \* prepared[n] is the highest accepted-prepared ballot by node n
,   aCounter \* aCounter[n] is such that all lower ballots are accepted as aborted (TODO: why no value here?)
    \* depending on the phase, h and c track the highest and lowest confirmed-prepared (in PREPARE), accepted committed (in COMMIT), or confirmed committed (in EXTERNALIZE) ballot
    \* In phase PREPARE, h.value could be different from ballot.value
,   h
,   c
,   sent \* sent[n] is the set of messages sent by node n
,   byz \* the set of Byzantine nodes

Init ==
    /\ ballot = [n \in N |-> [counter |-> -1, value |-> someValue]]
    /\ phase = [n \in N |-> "PREPARE"]
    /\ prepared = [n \in N |-> [counter |-> -1, value |-> someValue]]
    /\ aCounter = [n \in N |-> 0]
    /\ h = [n \in N |-> [counter |-> -1, value |-> someValue]]
    /\ c = [n \in N |-> [counter |-> -1, value |-> someValue]]
    /\ sent = [n \in N |-> {}]
    /\ byz \in FailProneSet

TypeOK ==
    /\ ballot \in [N -> BallotOrNull]
    /\ phase \in [N -> Phase]
    /\ prepared \in [N -> BallotOrNull]
    /\ aCounter \in [N -> BallotNumber]
    /\ h \in [N -> BallotOrNull]
    /\ c \in [N -> BallotOrNull]
    /\ sent \in [N -> SUBSET Message]
    /\ byz \in SUBSET N

ByzStep == \E msgs \in [byz -> SUBSET Message] :
    /\  sent' = [n \in N |-> IF n \notin byz THEN sent[n] ELSE msgs[n]]
    /\  UNCHANGED <<ballot, phase, prepared, aCounter, h, c, byz>>

\* TODO: is it sufficient to consider the latest message from each node? Likely yes.

(*******************************************************************************)
(* At any point in time, we may increase the ballot counter and set the ballot *)
(* value to the value of the highest confirmed prepared ballot, if any, or, if *)
(* none, arbitrarily.                                                          *)
(*******************************************************************************)
IncreaseBallotCounter(n, b) ==
    /\  b > ballot[n].counter
    /\  IF h[n].counter > 0 THEN
            ballot' = [ballot EXCEPT ![n] = [counter |-> b, value |-> h[n].value]]
        ELSE
            \E v \in V : ballot' = [ballot EXCEPT ![n] = [counter |-> b, value |-> v]]
    /\ UNCHANGED <<phase, prepared, aCounter, h, c, sent, byz>>

VotesToPrepare(b, m) ==
    /\  m.type = "PREPARE"
    /\  \/  /\  b.counter <= m.ballot.counter
            /\  b.value = m.ballot.value
        \/  /\  b.counter <= m.prepared.counter
            /\  b.value = m.prepared.value
        \/  b.counter < m.aCounter

AcceptsPrepared(b, m) ==
    /\  m.type = "PREPARE"
    /\  \/  /\  b.counter <= m.prepared.counter
            /\  b.value = m.prepared.value
        \/  b.counter < m.aCounter

AcceptPrepared(n, b) ==
    /\  LessThan(b, ballot[n])
    /\  LessThan(prepared[n], b)
    /\  \/ \E Q \in Quorums(n) : \A m \in Q : \E msg \in sent[m] : VotesToPrepare(b, msg)
        \/ \E B \in BlockingSets(n) : \A m \in B : \E msg \in sent[m] : AcceptsPrepared(b, msg)
    /\  prepared' = [prepared EXCEPT ![n] = b]
    /\  LET m == [
            type |-> "PREPARE"
        ,   ballot |-> ballot[n]
        ,   prepared |-> prepared'[n]
        ,   aCounter |-> aCounter[n]
        ,   hCounter |-> Max(h[n].counter,0)
        ,   cCounter |-> Max(c[n].counter,0)]
        IN
            sent' = [sent EXCEPT ![n] = sent[n] \cup {m}]
    /\  UNCHANGED <<ballot, phase, aCounter, h, c, byz>>

(***************************************************************)
(* We go to phase COMMIT when we accept a ballot as committed. *)
(***************************************************************)
PhaseCommit(n, b) ==
    TRUE

SendPrepare(n) ==
    /\  ballot[n].counter > 0
    /\  phase[n] = "PREPARE"
    /\  LET msg == [
            type |-> "PREPARE"
        ,   ballot |-> ballot[n]
        ,   prepared |-> prepared[n]
        ,   aCounter |-> aCounter[n]
        ,   hCounter |-> Max(h[n].counter,0)
        ,   cCounter |-> Max(c[n].counter,0)]
        IN 
            sent' = [sent EXCEPT ![n] = sent[n] \cup {msg}]
    /\  UNCHANGED <<ballot, phase, prepared, aCounter, h, c, byz>>
    
SendCommit(n) ==
    /\  phase[n] = "COMMIT"
    /\  LET msg == [
            type |-> "COMMIT"
        ,   ballot |-> ballot[n]
        ,   preparedCounter |-> prepared[n].counter
        ,   hCounter |-> h[n].counter
        ,   cCounter |-> c[n].counter]
        IN
            sent' = [sent EXCEPT ![n] = sent[n] \cup {msg}]
    /\  UNCHANGED <<ballot, phase, prepared, aCounter, h, c, byz>>

SendExternalize(n) ==
    /\  phase[n] = "EXTERNALIZE"
    /\  LET msg == [
            type |-> "EXTERNALIZE"
        ,   commit |-> ballot[n]
        ,   hCounter |-> h[n].counter]
        IN
            sent' = [sent EXCEPT ![n] = sent[n] \cup {msg}]
    /\  UNCHANGED <<ballot, phase, prepared, aCounter, h, c, byz>>

Next == 
    \/ ByzStep
    \/ \E n \in N \ byz :
        \/ \E cnt \in BallotNumber : IncreaseBallotCounter(n, cnt)
        \/ SendPrepare(n)
        \/ \E b \in Ballot : AcceptPrepared(n, b)
        \* \/ SendCommit(n)
        \* \/ SendExternalize(n)

vars == <<ballot, phase, prepared, aCounter, h, c, sent, byz>>

Spec ==
    Init /\ [][Next]_vars

\* Next we instantiate the AbstractBalloting specification

VoteToAbort(n) == {b \in Ballot :
    LessThan(b, ballot[n])}

AcceptedAborted(n) == {b \in Ballot : \E m \in sent[n] :
    /\  m.type = "PREPARE"
    /\  LessThan(b, m.prepared)}

voteToAbort == [n \in N |-> VoteToAbort(n)]
acceptedAborted == [n \in N |-> {}]
voteToCommit == [n \in N |-> {}]
acceptedCommitted == [n \in N |-> {}]
externalized == [n \in N |-> {}]

AB == INSTANCE AbstractBalloting

\* We have a correct refinement:
THEOREM Spec => AB!Spec

\* To check the refinement with TLC:
InitRefinement ==
    Init => AB!Init
NextRefinement ==
    [][Next => AB!Next]_vars

=============================================================================