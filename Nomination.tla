----------------------------- MODULE Nomination -----------------------------

(***************************************************************************)
(* This is a high-level specification of SCP focusing on the nomination    *)
(* protocol.                                                               *)
(*                                                                         *)
(* Currently, as implemented, before voting for a txset hash, nodes wait   *)
(* to obtain its preimage.  Delaying the point at which we wait for the    *)
(* pre-image would leave more room for disseminating the txset in parallel *)
(* to nomination.  However this has to be done carefully to maintain the   *)
(* main property of nomination: assuming that there is a nomination round  *)
(* with a good leader and during which the network is fast engough, at     *)
(* least a Tier-1 quorum must eventually enter balloting.                  *)
(*                                                                         *)
(*                                                                         *)
(* In the version specified in this document, we do not wait on the        *)
(* pre-image to vote for a txset hash, but we do wait for the pre-image    *)
(* before accepting it.                                                    *)
(*                                                                         *)
(* In the previous version of this document, we even accepted without a    *)
(* pre-image.  There is a problem with this: it could create a situation   *)
(* in which not enough nodes can start balloting (i.e.  not a full quorum) *)
(* and the whole system is stuck.                                          *)
(*                                                                         *)
(* The problem stems from the fact that, in the nomination protocol, nodes *)
(* that confirm a candidate then stop voting for new values (otherwise     *)
(* nomination is not guaranteed to converge).  So if a blocking set B      *)
(* confirms a candidate but somehow other nodes cannot get the pre-images  *)
(* they need to do so, more nomination rounds will not help because the    *)
(* members of B have stopped voting, which blocks the progress of any new  *)
(* candidate.  Depending on how pre-images are disseminated, this can      *)
(* potentially be exploited by an attacker to halt the system.             *)
(*                                                                         *)
(* So accepting without a pre-image is only workable if there is some way  *)
(* to guarantee that, once a Tier-1 blocking set has a pre-image, then     *)
(* everybody in Tier-1 eventually gets it.                                 *)
(*                                                                         *)
(* Another problem is that we want it to be likely that a quorum starts    *)
(* balloting already in agreement and roughly at the same time.  If we     *)
(* delay checking pre-images to the confirm stage, an attacker could first *)
(* send the pre-image to a set A of nodes, which then enter balloting at   *)
(* time T_A, but not send the pre-image to another set B of nodes, which   *)
(* then enter balloting at time T_B>>T_A because they need to get the      *)
(* pre-image from A before starting balloting.  For example, if it takes   *)
(* 500ms for members of B to get the pre-image from members of A, then     *)
(* T_B=T_A+500ms.  This can cause the first ballot to end without a        *)
(* decision.  Members of B could also start a new nomination round before  *)
(* T_B and then enter balloting not only late but also with a different    *)
(* value than members of A.                                                *)
(***************************************************************************)

EXTENDS Naturals, FiniteSets

CONSTANTS
    V, \* validators
    TxSet, \* blocks
    Bot, \* default value
    Quorum(_), \* Quorum(v) is the set of quorums of validator v
    Blocking(_), \* Blocking(v) is the set of blocking sets of validator v
    Combine(_), \* the functions that combines candidates to produce a txset for balloting
    H, \* domain of hashes
    Hash(_) \* hash function

VARIABLES txSetForBalloting, voted, accepted, round, candidates,
          preImage, leader

vars == << txSetForBalloting, voted, accepted, round, candidates,
           preImage, leader >>

Init ==
    /\ txSetForBalloting = [v \in V |-> Bot]
    /\ voted = [v \in V |-> {}]
    /\ accepted = [v \in V |-> {}]
    /\ round = [v \in V |-> 0]
    /\ candidates = [v \in V |-> {}]
    /\ preImage = [v \in V |-> [h \in H |-> Bot]]
    /\ leader = [v \in V |-> Bot]

StartRound(v) ==
    /\ round' = [round EXCEPT ![v] = round[v] + 1]
    /\ \E l \in V :
        /\ leader' = [leader EXCEPT ![v] = l]
        /\ IF l = v
              THEN /\ \E txs \in TxSet:
                        /\ preImage' = [preImage EXCEPT ![v][Hash(txs)] = txs]
                        /\ voted' = [voted EXCEPT ![v] = voted[v] \union {Hash(txs)}]
              ELSE UNCHANGED << voted, preImage>>
   /\ UNCHANGED <<txSetForBalloting, accepted, candidates>>

Vote(v) ==
    /\ IF candidates[v] = {}
         THEN /\ leader[v] # Bot
              /\ LET hs == voted[leader[v]] IN
                   /\ hs # {}
                   /\ voted' = [voted EXCEPT ![v] = voted[v] \union hs]
         ELSE UNCHANGED voted
    /\ UNCHANGED <<txSetForBalloting, accepted, round, candidates, preImage, leader>>

VotedHashes == UNION {voted[v] : v \in V}

GetTxSet(v, txs) ==
    /\ Hash(txs) \in VotedHashes
    /\ preImage' = [preImage EXCEPT ![v][Hash(txs)] = txs]
    /\ UNCHANGED <<txSetForBalloting, voted, accepted, round, candidates, leader>>

Accept(v, h) ==
    /\ preImage[v][h] # Bot
    /\ \/ \E Q \in Quorum(v) : \A w \in Q : h \in voted[w] \/ h \in accepted[w]
       \/ \E Bl \in Blocking(v) : \A w \in Bl : h \in accepted[w]
    /\ accepted' = [accepted EXCEPT ![v] = accepted[v] \union {h}]
    /\ UNCHANGED <<txSetForBalloting, voted, round, candidates, preImage, leader>>

Confirm(v, h) == \E Q \in Quorum(v):
    /\ preImage[v][h] # Bot
    /\ \A w \in Q : h \in accepted[w]
    /\ candidates' = [candidates EXCEPT ![v] = candidates[v] \union {preImage[v][h]}]
    /\ txSetForBalloting' = [txSetForBalloting EXCEPT ![v] = Combine(candidates'[v])]
    /\ UNCHANGED <<voted, accepted, round, preImage, leader>>

Next == \E v \in V, txs \in TxSet, h \in H :
    \/ StartRound(v)
    \/ Vote(v)
    \/ GetTxSet(v, txs)
    \/ Accept(v, h)
    \/ Confirm(v, h)

\* Here we assume that all agree on a leader in round 3 and stay in round 3 forever (for liveness)
LeaderAgreement ==
    /\ \E l \in V : \A v \in V : round[v] = 3 => leader[v] = l
    /\ \A v \in V : round[v] <= 3

Spec ==
    /\ Init
    /\ [][Next /\ LeaderAgreement']_vars
    /\ \A v \in V, txs \in TxSet, h \in H :
        /\ WF_vars(StartRound(v) /\ round[v] <= 2)
        /\ WF_vars(GetTxSet(v, txs))
        /\ WF_vars(Vote(v))
        /\ WF_vars(Accept(v, h))
        /\ WF_vars(Confirm(v, h))

(***************************************************************************)
(* The type-safety invariant:                                              *)
(***************************************************************************)

TypeOkay ==
    /\ txSetForBalloting \in [V -> TxSet \cup {Bot}]
    /\ voted \in [V -> SUBSET H]
    /\ accepted \in [V -> SUBSET H]
    /\ round \in [V -> Nat]
    /\ candidates \in [V -> SUBSET TxSet]
    /\ preImage \in [V -> [H -> TxSet \cup {Bot}]]
    /\ leader \in [V -> V \cup {Bot}]

(***************************************************************************)
(* Liveness: if a validator enters balloting, then eventually all do.      *)
(***************************************************************************)

Liveness ==
    \A v \in V : [](txSetForBalloting[v] # Bot 
        => \E t \in TxSet : <>(\A w \in V : txSetForBalloting[w] = t))

(***************************************************************************)
(* Liveness: eventually, all converge on a txset for balloting.            *)
(***************************************************************************)
Liveness2 ==
    \E t \in TxSet : <>(\A v \in V : txSetForBalloting[v] = t)

(***************************************************************************)
(* Definition for model-checking:                                          *)
(***************************************************************************)

\* Concrete hashing for the model-checker:
TestH == 1..Cardinality(TxSet)
TestHash(b) ==
    LET f == CHOOSE f \in [TxSet -> H] : \A txs1,txs2 \in TxSet : txs1 # txs2 => f[txs1] # f[txs2]
    IN f[b]

\* Debugging canaries:
Canary2 == \A v \in V : Cardinality(candidates[v]) <= 1
Canary3 == \A v \in V : txSetForBalloting[v] = Bot

TestQuorums == {Q \in SUBSET V : 2*Cardinality(Q)>Cardinality(V)}
TestBlocking == {Bl \in SUBSET V : Cardinality(Bl) > 1}



=============================================================================
\* Modification History
\* Last modified Fri Mar 31 11:17:40 PDT 2023 by nano
\* Created Fri Jan 13 09:09:00 PST 2023 by nano
