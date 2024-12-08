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

Phase == {"PREPARE", "COMMIT"}

\* @typeAlias: prepareMessage = {ballot : $ballot, prepared : $ballot, aCounter : Int, hCounter : Int, cCounter : Int};
\* @typeAlias: commitMessage = {ballot : $ballot, preparedCounter : Int, hCounter : Int, cCounter : Int};

SCPPrepare == [
    ballot : Ballot
,   prepared : BallotOrNull
,   aCounter : BallotNumber
,   hCounter : BallotNumber \cup {-1}
,   cCounter : BallotNumber \cup {-1}]

SCPCommit == [
    ballot : Ballot
,   preparedCounter : BallotNumber
,   hCounter : BallotNumber \cup {-1}
,   cCounter : BallotNumber \cup {-1}]

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
,   sentPrepare \* sentPrepare[n] is the set of prepare messages sent by node n
,   sentCommit \* sentCommit[n] is the set of commit messages sent by node n
,   byz \* the set of Byzantine nodes

Init ==
    /\ ballot = [n \in N |-> NullBallot]
    /\ phase = [n \in N |-> "PREPARE"]
    /\ prepared = [n \in N |-> NullBallot]
    /\ aCounter = [n \in N |-> 0]
    /\ h = [n \in N |-> NullBallot]
    /\ c = [n \in N |-> NullBallot]
    /\ sentPrepare = [n \in N |-> {}]
    /\ sentCommit = [n \in N |-> {}]
    /\ byz \in FailProneSet

TypeOK ==
    /\ ballot \in [N -> BallotOrNull]
    /\ phase \in [N -> Phase]
    /\ prepared \in [N -> BallotOrNull]
    /\ aCounter \in [N -> BallotNumber]
    /\ h \in [N -> BallotOrNull]
    /\ c \in [N -> BallotOrNull]
    /\ sentPrepare \in [N -> SUBSET SCPPrepare]
    /\ sentCommit \in [N -> SUBSET SCPCommit]
    /\ byz \in SUBSET N

\* faulty nodes can send any message they want
ByzStep ==
        \E prepareMsgs \in [byz -> SUBSET SCPPrepare] :
        \E commitMsgs \in [byz -> SUBSET SCPCommit] :
            /\  sentPrepare' = [n \in N |-> IF n \notin byz THEN sentPrepare[n] ELSE prepareMsgs[n]]
            /\  sentCommit' = [n \in N |-> IF n \notin byz THEN sentCommit[n] ELSE commitMsgs[n]]
            /\  UNCHANGED <<ballot, phase, prepared, aCounter, h, c, byz>>

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
                ballot |-> ballot[n]
            ,   prepared |-> SummarizePrepared(n).prepared
            ,   aCounter |-> SummarizePrepared(n).aCounter
            ,   hCounter |->
                    IF h[n].counter > -1 /\ h[n].value = ballot[n].value
                    THEN h[n].counter
                    ELSE -1 \* TODO okay?
            ,   cCounter |-> Max(c[n].counter, 0)]
        IN
            sentPrepare' = [sentPrepare EXCEPT ![n] = sentPrepare[n] \cup {msg}]
    /\  UNCHANGED <<ballot, phase, prepared, aCounter, h, c, sentCommit, byz>>

SendCommit(n) ==
    /\  phase[n] = "COMMIT"
    /\  LET msg == [
                ballot |-> ballot[n]
            ,   preparedCounter |-> prepared[n].counter
            ,   hCounter |-> h[n].counter
            ,   cCounter |-> c[n].counter]
        IN
            sentCommit' = [sentCommit EXCEPT ![n] = sentCommit[n] \cup {msg}]
    /\  UNCHANGED <<ballot, phase, prepared, aCounter, h, c, sentPrepare, byz>>

(*******************************************************************************)
(* At any point in time, we may increase the ballot counter and set the ballot *)
(* value to the value of the highest confirmed prepared ballot, if any, or, if *)
(* none, arbitrarily. In practice, this happens when according to a timer.     *)
(*******************************************************************************)
IncreaseBallotCounter(n, b) ==
    /\  b > 0
    /\  b > ballot[n].counter
    /\  IF h[n].counter > 0 THEN
            ballot' = [ballot EXCEPT ![n] = [counter |-> b, value |-> h[n].value]]
        ELSE
            \E v \in V : ballot' = [ballot EXCEPT ![n] = [counter |-> b, value |-> v]]
    /\ UNCHANGED <<phase, prepared, aCounter, h, c, sentPrepare, sentCommit, byz>>

(**********************************************************************************)
(* We now specify how a node updates its local state depending on the messages it *)
(* receives.                                                                      *)
(**********************************************************************************)

\* @type: ($ballot, $prepareMessage) => Bool;
PrepareMessageVotesToPrepare(b, m) ==
    /\  \/  /\  b.counter <= m.ballot.counter
            /\  b.value = m.ballot.value
        \/  /\  b.counter <= m.prepared.counter
            /\  b.value = m.prepared.value
        \/  b.counter < m.aCounter

\* @type: ($ballot, $commitMessage) => Bool;
CommitMessageVotesToPrepare(b, m) == b.value = m.ballot.value

VotesToPrepare(n, b) ==
    \/  \E m \in sentPrepare[n] : PrepareMessageVotesToPrepare(b, m)
    \/  \E m \in sentCommit[n] : CommitMessageVotesToPrepare(b, m)

\* @type: ($ballot, $prepareMessage) => Bool;
PrepareMessageAcceptsPrepared(b, m) ==
    \/  /\  b.counter <= m.prepared.counter
        /\  b.value = m.prepared.value
    \/  b.counter < m.aCounter

\* @type: ($ballot, $commitMessage) => Bool;
CommitMessageAcceptsPrepared(b, m) ==
    /\  b.counter <= m.preparedCounter
    /\  b.value = m.ballot.value

AcceptsPrepared(n, b) ==
    \/  \E m \in sentPrepare[n] : PrepareMessageAcceptsPrepared(b, m)
    \/  \E m \in sentCommit[n] : CommitMessageAcceptsPrepared(b, m)

\* @type: ($ballot, $prepareMessage) => Bool;
PrepareMessageVotesToCommit(b, m) ==
    /\  m.cCounter > 0
    /\  m.cCounter <= b.counter
    /\  b.counter <= m.hCounter
    /\  b.value = m.ballot.value

\* @type: ($ballot, $commitMessage) => Bool;
CommitMessageVotesToCommit(b, m) ==
    /\  m.cCounter <= b.counter
    /\  b.value = m.ballot.value

\* @type: (NODE, $ballot) => Bool;
VotesToCommit(n, b) ==
    \/  \E m \in sentPrepare[n] : PrepareMessageVotesToCommit(b, m)
    \/  \E m \in sentCommit[n] : CommitMessageVotesToCommit(b, m)

\* @type: (NODE, $ballot) => Bool;
AcceptsCommitted(n, b) ==
    \E m \in sentCommit[n] :
        /\  b.value = m.ballot.value
        /\  m.cCounter <= b.counter
        /\  b.counter <= m.hCounter

\* whether b is aborted given aCounter and prepared:
\* @type: ($ballot, Int, $ballot) => Bool;
Aborted(b, a, p) ==
    \/  b.counter < a
    \/  LessThanAndIncompatible(b, p)

UpdatePrepared(n, b) ==
    /\  prepared' = [prepared EXCEPT ![n] = b]
    /\  IF prepared[n].counter > -1 /\ prepared[n].value # b.value
        THEN aCounter' = [aCounter EXCEPT ![n] =
            IF prepared[n].value < b.value
            THEN prepared[n].counter
            ELSE prepared[n].counter+1]
        ELSE UNCHANGED aCounter

AcceptPrepared(n, b) ==
    /\  prepared[n] \prec b
    /\  \/ \E Q \in Quorum : \A n2 \in Q : VotesToCommit(n2, b)
        \/ \E B \in BlockingSet : \A n2 \in B : AcceptsPrepared(n2, b)
    /\  UpdatePrepared(n, b)
    \* Reset c to NullBallot if it has been aborted:
    /\  IF c[n].counter > -1 /\ Aborted(c[n], aCounter'[n], prepared'[n])
        THEN c' = [c EXCEPT ![n] = NullBallot]
        ELSE UNCHANGED c
    /\  UNCHANGED <<ballot, phase, h, sentPrepare, sentCommit, byz>>

ConfirmPrepared(n, b) ==
    /\  h[n] \prec b
    /\  \E Q \in Quorum : \A n2 \in Q : AcceptsPrepared(n2, b)
    /\  h' = [h EXCEPT ![n] = b]
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
    /\  UNCHANGED <<phase, sentPrepare, sentCommit, byz>>

AcceptCommitted(n, b) ==
    /\  b.counter > 0 \* TODO remove
    /\  b = ballot[n] \* TODO okay?
    /\  IF phase[n] = "PREPARE"
        THEN phase' = [phase EXCEPT ![n] = "COMMIT"] /\ c' = [c EXCEPT ![n] = b]
        ELSE UNCHANGED <<phase, c>>
    /\  phase[n] = "COMMIT" => h[n] \prec b
    /\  \/ \E Q \in Quorum : \A n2 \in Q : VotesToCommit(n2, b)
        \/ \E B \in BlockingSet : \A n2 \in B : AcceptsCommitted(n2, b)
    /\  h' = [h EXCEPT ![n] = b]
    /\  IF prepared[n] \prec b \* accepted committed implies accepted prepared
        THEN UpdatePrepared(n, b)
        ELSE UNCHANGED <<prepared, aCounter>>
    /\  UNCHANGED <<ballot, sentPrepare, sentCommit, byz>>

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

vars == <<ballot, phase, prepared, aCounter, h, c, sentPrepare, sentCommit, byz>>

Spec ==
    Init /\ [][Next]_vars

Inv1 ==
    /\  TypeOK
    /\  \A n \in N \ byz : phase[n] = "COMMIT"
            => ballot[n].counter > 0 /\ prepared[n].counter >= 0

Inv2_pre ==
    /\  TypeOK
    /\  byz \in FailProneSet
Inv2 == byz \in FailProneSet

=============================================================================
