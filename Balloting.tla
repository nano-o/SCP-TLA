----------------------------- MODULE Balloting -----------------------------

(**************************************************)
(* Specification of SCP following the IETF draft. *)
(**************************************************)

EXTENDS DomainModel

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

MessageInvariant(m) ==
    /\  m.type = "PREPARE" =>
        /\  m.ballot.counter > 0
        /\  m.prepared.counter > -1 =>
            /\  m.prepared \preceq m.ballot
            /\  m.aCounter <= m.prepared.counter
        /\  m.prepared.counter = -1 => m.aCounter = 0
        /\  m.cCounter <= m.hCounter
        \* /\  m.hCounter <= m.ballot.counter \* TODO: why this (note it's explicitely mentioned on Page 13)? I guess the sender should have increased its ballot counter before sending the message, but it's not a safety problem.
    /\  m.type = "COMMIT" =>
        /\  m.cCounter > 0
        /\  m.cCounter <= m.ballot.counter
        /\  m.cCounter <= m.hCounter

\* Meaning of the messages in terms of logical, federated-voting messages:
LogicalMessages(m) ==
    CASE m.type = "PREPARE" -> [
            voteToAbort |-> {b \in Ballot :
                LessThanAndIncompatible(b, m.ballot)},
            acceptedAborted |-> {b \in Ballot :
                \/ LessThanAndIncompatible(b, m.prepared)
                \/ b.counter < m.aCounter},
            confirmedAborted |->
                IF m.hCounter = 0 THEN {}
                ELSE {b \in Ballot :
                    LET h == [counter |-> m.hCounter, value |-> m.ballot.value]
                    IN  LessThanAndIncompatible(b, h)},
            voteToCommit |-> IF m.cCounter = 0 THEN {}
                ELSE {b \in Ballot :
                    /\ m.cCounter <= b.counter /\ b.counter <= m.hCounter
                    /\ b.value = m.ballot.value},
            acceptedCommitted |-> {}]
    []  m.type = "COMMIT" -> [
            voteToAbort |-> {b \in Ballot : b.value # m.ballot.value},
            acceptedAborted |-> 
                LET maxPrepared == [counter |-> m.preparedCounter, value |-> m.ballot.value]
                IN {b \in Ballot : LessThanAndIncompatible(b, maxPrepared)},
            confirmedAborted |->
                LET maxPrepared == [counter |-> m.hCounter, value |-> m.ballot.value]
                IN  {b \in Ballot : LessThanAndIncompatible(b, maxPrepared)},
            voteToCommit |-> {b \in Ballot :
                m.cCoutner <= b.counter /\ b.value = m.ballot.value},
            acceptedCommitted |-> {b \in Ballot :
                /\ m.cCoutner <= b.counter \/ b.counter <= m.hCounter
                /\ b.value = m.ballot.value}]

VARIABLES
    ballot \* ballot[n] is the current ballot being prepared or committed by node n
,   phase  \* phase[n] is the current phase of node n
,   prepared \* prepared[n] is the highest accepted-prepared ballot by node n
,   aCounter \* aCounter[n] is such that all lower ballots are accepted as aborted
    \* depending on the phase, h and c track the highest and lowest confirmed-prepared (in PREPARE), accepted committed (in COMMIT), or confirmed committed (in EXTERNALIZE) ballot
    \* In phase PREPARE, h.value could be different from ballot.value
,   h
,   c
,   sent \* sent[n] is the set of messages sent by node n
,   byz \* the set of Byzantine nodes

Init ==
    /\ ballot = [n \in N |-> NullBallot]
    /\ phase = [n \in N |-> "PREPARE"]
    /\ prepared = [n \in N |-> NullBallot]
    /\ aCounter = [n \in N |-> 0]
    /\ h = [n \in N |-> NullBallot]
    /\ c = [n \in N |-> NullBallot]
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

(*******************************************************************************)
(* At any point in time, we may increase the ballot counter and set the ballot *)
(* value to the value of the highest confirmed prepared ballot, if any, or, if *)
(* none, arbitrarily.                                                          *)
(*******************************************************************************)
IncreaseBallotCounter(n, b) ==
    /\  b > 0
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

\* whether b is aborted given aCounter and prepared:
Aborted(b, a, p) ==
    \/  b.counter < a
    \/  LessThanAndIncompatible(b, p)

\* update prepared, aCounter, and c given a new accepted-prepared ballot
\* assumes prepared[n] \preceq b
UpdatePrepared(n, b) ==
    /\  prepared' = [prepared EXCEPT ![n] = b]
    /\  IF prepared[n].counter > -1 /\ prepared[n].value # b.value
        THEN aCounter' = [aCounter EXCEPT ![n] =
            IF prepared[n].value < b.value
            THEN prepared[n].counter
            ELSE prepared[n].counter+1]  
        ELSE UNCHANGED aCounter
    /\  IF c[n].counter > -1 /\ Aborted(c[n], aCounter'[n], prepared'[n])
        THEN c' = [c EXCEPT ![n] = NullBallot]
        ELSE UNCHANGED c
    
\* Update what is accepted as prepared:
AcceptPrepared(n, b) ==
    /\  phase = "PREPARE"
    /\  prepared[n] \prec b
    /\  \/ \E Q \in Quorum : \A m \in Q : \E msg \in sent[m] : VotesToPrepare(b, msg)
        \/ \E B \in BlockingSet : \A m \in B : \E msg \in sent[m] : AcceptsPrepared(b, msg)
    /\  UpdatePrepared(n, b)
    /\  UNCHANGED <<ballot, phase, h, sent, byz>>

\* Update what is confirmed as prepared:
ConfirmPrepared(n, b) ==
    /\  phase = "PREPARE"
    /\  h[n] \prec b
    /\  \E Q \in Quorum : \A m \in Q : \E msg \in sent[m] : AcceptsPrepared(b, msg)
    /\  h' = [h EXCEPT ![n] = b]
    /\  IF prepared[n] \prec b \* confirmed prepared implies accepted prepared
        THEN UpdatePrepared(n, b)
        ELSE UNCHANGED <<prepared, aCounter, c>>
(***************************************************************)
(* We go to phase COMMIT when we accept a ballot as committed. *)
(***************************************************************)
PhaseCommit(n, b) ==
    "TODO"

\* Summarize what has been prepared, under the constraint that prepared is less than or equal to ballot:
SummarizePrepared(n) ==
    IF prepared[n] \preceq ballot[n]
    THEN [prepared |-> prepared[n], aCounter |-> aCounter[n]]
    ELSE
        IF ballot[n].value > prepared[n].value \/ aCounter[n] > ballot[n].counter
        THEN [
            prepared |-> [counter |-> ballot[n].counter, value |-> prepared[n].value],
            aCounter |-> Min(aCounter[n], ballot[n].counter)]
        ELSE [
            prepared |-> [counter |-> ballot[n].counter-1, value |-> prepared[n].value],
            aCounter |-> Min(aCounter[n], ballot[n].counter-1)]

SendPrepare(n) ==
    /\  ballot[n].counter > 0
    /\  phase[n] = "PREPARE"
    /\  LET msg == [
            type |-> "PREPARE"
        ,   ballot |-> ballot[n]
        ,   prepared |-> SummarizePrepared(n).prepared
        ,   aCounter |-> SummarizePrepared(n).aCounter
        ,   hCounter |->
                IF h[n].counter > -1 /\ h[n].value = ballot[n].value
                THEN h[n].counter
                ELSE 0
        ,   cCounter |-> Max(c[n].counter, 0)]
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
        \/ \E b \in Ballot :
            \/  AcceptPrepared(n, b)
            \/  ConfirmPrepared(n, b)
        \* \/ SendCommit(n)
        \* \/ SendExternalize(n)

vars == <<ballot, phase, prepared, aCounter, h, c, sent, byz>>

Spec ==
    Init /\ [][Next]_vars

Invariant ==
    /\  TypeOK
    /\  \A n \in N \ byz :
        /\  \A m \in sent[n] : MessageInvariant(m)
        /\  ballot[n].counter = -1 \/ ballot[n].counter > 0
        /\  prepared[n].counter > -1 => aCounter[n] <= prepared[n].counter
        /\  prepared[n].counter = -1 => aCounter[n] = 0
        /\  h[n] \preceq prepared[n]
        /\  c[n].counter = -1 \/ c[n].counter > 0
        /\  c[n].counter <= h[n].counter
        /\  c[n].counter <= ballot[n].counter
        /\  c[n].counter > 0 =>
                /\  c[n].value = h[n].value
                /\  c[n].value = prepared[n].value
                /\  c[n].value = ballot[n].value
        /\  h[n] \preceq prepared[n]

\* Next we instantiate the AbstractBalloting specification

voteToAbort == [n \in N |-> UNION {LogicalMessages(m).voteToAbort : m \in sent[n]}]
acceptedAborted == [n \in N |-> UNION {LogicalMessages(m).acceptedAborted : m \in sent[n]}]
confirmedAborted == [n \in N |-> UNION {LogicalMessages(m).confirmedAborted : m \in sent[n]}]
voteToCommit == [n \in N |-> UNION {LogicalMessages(m).voteToCommit : m \in sent[n]}]
acceptedCommitted == [n \in N |-> UNION {LogicalMessages(m).acceptedCommitted : m \in sent[n]}]
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