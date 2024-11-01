----------------------------- MODULE Balloting -----------------------------

(**************************************************************************************)
(* Specification of SCP's balloting protocol following the `^IETF^' draft at:         *)
(*                                                                                    *)
(* `^https://datatracker.ietf.org/doc/html/draft-mazieres-dinrg-scp-05\#section-3.5^' *)
(*                                                                                    *)
(* This specification abstracts over some aspects of the protocol (e.g. increasing    *)
(* the ballot counter), but it does explicitely represent balloting messages.         *)
(* There are also some differences compared to the `^IETF^' draft, due to I suspect   *)
(* are omissions in the `^IETF^' draft.                                               *)
(*                                                                                    *)
(* Currently this specification covers only the `^PREPARE^' and `^COMMIT^' phases.    *)
(**************************************************************************************)

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

\* Some well-formedness conditions on messages:
MessageInvariant(m) ==
    /\  m.type = "PREPARE" =>
        /\  m.ballot.counter > 0
        /\  m.prepared.counter > -1 =>
            /\  m.prepared \preceq m.ballot
            /\  m.aCounter <= m.prepared.counter
        /\  m.prepared.counter = -1 => m.aCounter = 0
        /\  m.cCounter <= m.hCounter
    /\  m.type = "COMMIT" =>
        /\  m.cCounter > 0
        /\  m.cCounter <= m.ballot.counter
        /\  m.cCounter <= m.hCounter
\* TODO: Page 13 mentions that we should have m.hCounter <= m.ballot.counter in a PREPARE message
\* This seems superfluous.
\* I guess the sender should have increased its ballot counter before sending the message, but it's not a safety problem.

\* Meaning of the messages in terms of logical, federated-voting messages.
\* We will use this to show that this specification refines the AbstractBalloting specification.
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
                m.cCounter <= b.counter /\ b.value = m.ballot.value},
            acceptedCommitted |-> {b \in Ballot :
                /\ m.cCounter <= b.counter /\ b.counter <= m.hCounter
                /\ b.value = m.ballot.value}]

VARIABLES
    ballot \* ballot[n] is the current ballot being prepared or committed by node n
,   phase  \* phase[n] is the current phase of node n
,   prepared \* prepared[n] is the highest accepted-prepared ballot by node n
,   aCounter \* aCounter[n] is such that all lower ballots are accepted as aborted
    \* h and c track:
    \* in the PREPARE phase, the highest and lowest confirmed-prepared ballot
    \* in the COMMIT phase, the highest and lowest accepted committed ballot
    \* in the EXTERNALIZE phase, the highest and lowest confirmed committed ballot
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

\* faulty nodes can send any message they want
ByzStep == \E msgs \in [byz -> SUBSET Message] :
    /\  sent' = [n \in N |-> IF n \notin byz THEN sent[n] ELSE msgs[n]]
    /\  UNCHANGED <<ballot, phase, prepared, aCounter, h, c, byz>>

(******************************************************************************)
(* We start by specifying how a node updates its local state depending on the *)
(* messages it receives.                                                      *)
(******************************************************************************)

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
    \* TODO: optimization
    \* /\  IF b = 1
    \*     THEN c' = [c EXCEPT ![n] = ballot'[n]]
    \*     ELSE UNCHANGED c
    /\ UNCHANGED <<phase, prepared, aCounter, h, c, sent, byz>>

VotesToPrepare(b, m) ==
    \/  /\  m.type = "PREPARE"
        /\  \/  /\  b.counter <= m.ballot.counter
                /\  b.value = m.ballot.value
            \/  /\  b.counter <= m.prepared.counter
                /\  b.value = m.prepared.value
            \/  b.counter < m.aCounter
    \/  /\  m.type = "COMMIT"
        /\  b.value = m.ballot.value

AcceptsPrepared(b, m) ==
    \/  /\  m.type = "PREPARE"
        /\  \/  /\  b.counter <= m.prepared.counter
                /\  b.value = m.prepared.value
            \/  b.counter < m.aCounter
    \/  /\  m.type = "COMMIT"
        /\  b.counter <= m.preparedCounter
        /\  b.value = m.ballot.value

\* whether b is aborted given aCounter and prepared:
Aborted(b, a, p) ==
    \/  b.counter < a
    \/  LessThanAndIncompatible(b, p)

\* update prepared and aCounter given a new accepted-prepared ballot
UpdatePrepared(n, b) ==
    \* TODO: what's commented out might be needed for liveness:
    \* IF prepared[n] \prec b
    \* THEN
        /\  prepared' = [prepared EXCEPT ![n] = b]
        /\  IF prepared[n].counter > -1 /\ prepared[n].value # b.value
            THEN aCounter' = [aCounter EXCEPT ![n] =
                IF prepared[n].value < b.value
                THEN prepared[n].counter
                ELSE prepared[n].counter+1]
            ELSE UNCHANGED aCounter
    \* ELSE
    \*     IF b.value # prepared[n].value /\ b.counter >= aCounter[n]
    \*     THEN aCounter' = [aCounter EXCEPT ![n] =
    \*         IF prepared[n].value < b.value
    \*         THEN prepared[n].counter
    \*         ELSE prepared[n].counter+1]
    \*     ELSE
    \*         ELSE UNCHANGED aCounter
    
\* Update what is accepted as prepared:
AcceptPrepared(n, b) ==
    /\  prepared[n] \prec b
    /\  \/ \E Q \in Quorum : \A m \in Q : \E msg \in sent[m] : VotesToPrepare(b, msg)
        \/ \E B \in BlockingSet : \A m \in B : \E msg \in sent[m] : AcceptsPrepared(b, msg)
    /\  UpdatePrepared(n, b)
    \* Reset c to NullBallot if it has been aborted:
    /\  IF c[n].counter > -1 /\ Aborted(c[n], aCounter'[n], prepared'[n])
        THEN c' = [c EXCEPT ![n] = NullBallot]
        ELSE UNCHANGED c
    /\  UNCHANGED <<ballot, phase, h, sent, byz>>

\* Update what is confirmed as prepared:
ConfirmPrepared(n, b) ==
    /\  h[n] \prec b
    /\  \E Q \in Quorum : \A m \in Q : \E msg \in sent[m] : AcceptsPrepared(b, msg)
    /\  h' = [h EXCEPT ![n] = b]
    \* TODO what if we confirm prepared something that's lower and incompatible with prepared?
    \* Should we update aCounter? (see commented-out part of UpdatePrepared)
    /\  IF prepared[n] \prec b \* confirmed prepared implies accepted prepared
        THEN UpdatePrepared(n, b)
        ELSE UNCHANGED <<prepared, aCounter>>
    \* Update c (either reset to NullBallot, if it has been aborted, or set it to b):
    /\  IF  /\  c[n].counter > -1
            /\  \/  Aborted(c[n], aCounter'[n], prepared'[n])
                \/  LessThanAndIncompatible(c[n], b)
        THEN c' = [c EXCEPT ![n] = NullBallot]
        ELSE
            IF  /\  c[n].counter = -1
                /\  b = ballot[n]
                /\  \neg Aborted(b, aCounter'[n], prepared'[n])
            THEN c' = [c EXCEPT ![n] = b]
            ELSE UNCHANGED c
    /\  IF b.counter > 0 /\ ballot[n].counter < b.counter
        THEN ballot' = [ballot EXCEPT ![n] = b] \* not strictly necessary, but might help curb the statespace
        ELSE UNCHANGED ballot
    /\  UNCHANGED <<phase, sent, byz>>

\* NOTE this should be consistent with LogicalMessages
VotesToCommit(b, m) ==
    \/  /\  m.type = "PREPARE"
        /\  m.cCounter > 0
        /\  m.cCounter <= b.counter
        /\  b.counter <= m.hCounter
        /\  b.value = m.ballot.value
    \/  /\  m.type = "COMMIT"
        /\  m.cCounter <= b.counter
        /\  b.value = m.ballot.value

\* NOTE this should be consistent with LogicalMessages
AcceptsCommitted(b, m) ==
    /\  m.type = "COMMIT"
    /\  b.value = m.ballot.value
    /\  m.cCounter <= b.counter
    /\  b.counter <= m.hCounter

AcceptCommitted(n, b) ==
    /\  b = ballot[n] \* TODO okay?
    /\  IF phase[n] = "PREPARE"
        THEN phase' = [phase EXCEPT ![n] = "COMMIT"] /\ c' = [c EXCEPT ![n] = b]
        ELSE UNCHANGED <<phase, c>>
    /\  phase[n] = "COMMIT" => h[n] \prec b
    /\  \/ \E Q \in Quorum : \A m \in Q : \E msg \in sent[m] : VotesToCommit(b, msg)
        \/ \E B \in BlockingSet : \A m \in B : \E msg \in sent[m] : AcceptsCommitted(b, msg)
    /\  h' = [h EXCEPT ![n] = b]
    /\  IF prepared[n] \prec b \* accepted committed implies accepted prepared
        THEN UpdatePrepared(n, b)
        ELSE UNCHANGED <<prepared, aCounter>>
    /\  UNCHANGED <<ballot, sent, byz>>

(******************************************************)
(* Now we specify what messages can be sent by a node *)
(******************************************************)

\* Summarize what has been prepared, under the constraint that prepared is less than or equal to ballot:
SummarizePrepared(n) ==
    IF prepared[n] \preceq ballot[n]
    THEN [prepared |-> prepared[n], aCounter |-> aCounter[n]]
    ELSE
        IF ballot[n].value > prepared[n].value \/ aCounter[n] > ballot[n].counter
        THEN [
            prepared |-> [counter |-> ballot[n].counter, value |-> prepared[n].value],
            aCounter |-> Min(aCounter[n], ballot[n].counter)]
        ELSE 
            IF aCounter[n] = ballot[n].counter
            \* TODO okay?
            THEN [
                prepared |-> [counter |-> ballot[n].counter, value |-> ballot[n].value],
                aCounter |-> aCounter[n]]
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

(******************************************)
(* We can now give the full specification *)
(******************************************)

Next ==
    \/ ByzStep
    \/ \E n \in N \ byz :
        \/ \E cnt \in BallotNumber : IncreaseBallotCounter(n, cnt)
        \/ \E b \in Ballot :
            \/  AcceptPrepared(n, b)
            \/  ConfirmPrepared(n, b)
            \/  AcceptCommitted(n, b)
        \/ SendPrepare(n)
        \/ SendCommit(n)
        \* \/ SendExternalize(n)

vars == <<ballot, phase, prepared, aCounter, h, c, sent, byz>>

Spec ==
    Init /\ [][Next]_vars

(*****************************************)
(* We now turn to correctness properties *)
(*****************************************)

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
    AB!Init
NextRefinement ==
    [][AB!Next]_vars

=============================================================================