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
(***************************************************************************)

EXTENDS Naturals, FiniteSets

CONSTANTS
    V, \* validators
    B, \* blocks
    Bot, \* default value
    Quorum(_), \* Quorum(v) is the set of quorums of validator v
    Blocking(_), \* Blocking(v) is the set of blocking sets of validator v
    Combine(_), \* the functions that combines candidates to produce a block for balloting
    H, \* domain of hashes
    Hash(_) \* hash function
    
(*
--algorithm SCP {
    variables \* global variables (e.g. representing messages or cross-component variables like ballotingBlock):
        ballotingBlock = [v \in V |-> Bot]; \* for each validator, the nominated block for balloting
        decision = [v \in V |-> Bot];  \* for each validator, the balloting decision
        voted = [v \in V |-> {}]; \* X in the whitepaper (nomination Section)
        accepted = [v \in V |-> {}]; \* Y in the whitepaper (nomination Section)
    process (nomination \in V)
        variables \* local variables:
            round = 0; \* nothing happens in round 0; the protocol start at round 1
            candidates = {}; \* Z in the whitepaper (nomination Section)
            preImage = [h \in H |-> Bot]; \* a map from hash to corresponding block
            leader = Bot; \* leader for the current round
    {
ln1:    while (TRUE)
        either { \* timeout and go to next round (this also starts round 1)
ln2:        round := round + 1;
            with (l \in V) { \* pick a leader
                leader := l;
                if (l = self) \* if the leader is the current node, pick a block hash and vote for it
                    with (h \in H)
                    voted[self] := voted[self] \union {h}
            }
        }
        or { \* vote for what the leader voted for, unless we have a candidate already
ln3:        when candidates = {};
            when leader # Bot;
            with (hs = voted[leader]) { 
                await hs # {}; \* wait to hear from the leader 
                voted[self] := voted[self] \union hs \* vote for what the leader has voted for
            }
        } 
        or 
ln4:    with (Q \in Quorum(self), h \in H) { \* accept when voted or accepted by a quorum and we have the pre-image
            when preImage[h] # Bot; \* we must have received the block
            when \A w \in Q : h \in voted[w] \/ h \in accepted[w]; \* a quorum has voted or accepted h:
            accepted[self] := accepted[self] \union {h}; \* accept h
        }
        or 
ln5:    with (Bl \in Blocking(self), h \in H) { \* accept when accepted by a blocking set and we have the pre-image
            when preImage[h] # Bot; \* we must have received the block
            when \A w \in Bl : h \in accepted[w];
            accepted[self] := accepted[self] \union {h}; \* accept h
        }
        or 
ln6:    with (b \in B) { \* receive a block
            preImage[Hash(b)] := b;
        }
        or 
ln7:    with (Q \in Quorum(self), h \in H) { \* confirm b as candidate
            when preImage[h] # Bot; \* we must have received the block
            when \A w \in Q : h \in accepted[w]; \* a quorum has accepted h:
            candidates := candidates \union {preImage[h]}; \* add h to the confirmed candidates
            \* update the block used in balloting:
            ballotingBlock[self] := Combine(candidates); \* this starts the balloting protocol (see below)
        }
    } 
    \* as a first approximation, balloting just decide on one of the balloting blocks:
    \* note we cannot reuse the process ID identifiers used in nomination, so we add the "balloting" tag
    process (balloting \in {<<v, "balloting">> : v \in V}) { 
lb1:    await ballotingBlock[self[1]] # Bot; \* wait for a confirmed candidate from nomination
lb2:    with (b \in {ballotingBlock[v] : v \in V} \ {Bot}) {
            when \A w \in V : decision[w] # Bot => b = decision[w];
            decision[self[1]] := b;
        }
    }
}
*)

\* BEGIN TRANSLATION (chksum(pcal) = "ddd27a0a" /\ chksum(tla) = "30345eff")
VARIABLES ballotingBlock, decision, voted, accepted, pc, round, candidates, 
          preImage, leader

vars == << ballotingBlock, decision, voted, accepted, pc, round, candidates, 
           preImage, leader >>

ProcSet == (V) \cup ({<<v, "balloting">> : v \in V})

Init == (* Global variables *)
        /\ ballotingBlock = [v \in V |-> Bot]
        /\ decision = [v \in V |-> Bot]
        /\ voted = [v \in V |-> {}]
        /\ accepted = [v \in V |-> {}]
        (* Process nomination *)
        /\ round = [self \in V |-> 0]
        /\ candidates = [self \in V |-> {}]
        /\ preImage = [self \in V |-> [h \in H |-> Bot]]
        /\ leader = [self \in V |-> Bot]
        /\ pc = [self \in ProcSet |-> CASE self \in V -> "ln1"
                                        [] self \in {<<v, "balloting">> : v \in V} -> "lb1"]

ln1(self) == /\ pc[self] = "ln1"
             /\ \/ /\ pc' = [pc EXCEPT ![self] = "ln2"]
                \/ /\ pc' = [pc EXCEPT ![self] = "ln3"]
                \/ /\ pc' = [pc EXCEPT ![self] = "ln4"]
                \/ /\ pc' = [pc EXCEPT ![self] = "ln5"]
                \/ /\ pc' = [pc EXCEPT ![self] = "ln6"]
                \/ /\ pc' = [pc EXCEPT ![self] = "ln7"]
             /\ UNCHANGED << ballotingBlock, decision, voted, accepted, round, 
                             candidates, preImage, leader >>

ln2(self) == /\ pc[self] = "ln2"
             /\ round' = [round EXCEPT ![self] = round[self] + 1]
             /\ \E l \in V:
                  /\ leader' = [leader EXCEPT ![self] = l]
                  /\ IF l = self
                        THEN /\ \E h \in H:
                                  voted' = [voted EXCEPT ![self] = voted[self] \union {h}]
                        ELSE /\ TRUE
                             /\ voted' = voted
             /\ pc' = [pc EXCEPT ![self] = "ln1"]
             /\ UNCHANGED << ballotingBlock, decision, accepted, candidates, 
                             preImage >>

ln3(self) == /\ pc[self] = "ln3"
             /\ candidates[self] = {}
             /\ leader[self] # Bot
             /\ LET hs == voted[leader[self]] IN
                  /\ hs # {}
                  /\ voted' = [voted EXCEPT ![self] = voted[self] \union hs]
             /\ pc' = [pc EXCEPT ![self] = "ln1"]
             /\ UNCHANGED << ballotingBlock, decision, accepted, round, 
                             candidates, preImage, leader >>

ln4(self) == /\ pc[self] = "ln4"
             /\ \E Q \in Quorum(self):
                  \E h \in H:
                    /\ preImage[self][h] # Bot
                    /\ \A w \in Q : h \in voted[w] \/ h \in accepted[w]
                    /\ accepted' = [accepted EXCEPT ![self] = accepted[self] \union {h}]
             /\ pc' = [pc EXCEPT ![self] = "ln1"]
             /\ UNCHANGED << ballotingBlock, decision, voted, round, 
                             candidates, preImage, leader >>

ln5(self) == /\ pc[self] = "ln5"
             /\ \E Bl \in Blocking(self):
                  \E h \in H:
                    /\ preImage[self][h] # Bot
                    /\ \A w \in Bl : h \in accepted[w]
                    /\ accepted' = [accepted EXCEPT ![self] = accepted[self] \union {h}]
             /\ pc' = [pc EXCEPT ![self] = "ln1"]
             /\ UNCHANGED << ballotingBlock, decision, voted, round, 
                             candidates, preImage, leader >>

ln6(self) == /\ pc[self] = "ln6"
             /\ \E b \in B:
                  preImage' = [preImage EXCEPT ![self][Hash(b)] = b]
             /\ pc' = [pc EXCEPT ![self] = "ln1"]
             /\ UNCHANGED << ballotingBlock, decision, voted, accepted, round, 
                             candidates, leader >>

ln7(self) == /\ pc[self] = "ln7"
             /\ \E Q \in Quorum(self):
                  \E h \in H:
                    /\ preImage[self][h] # Bot
                    /\ \A w \in Q : h \in accepted[w]
                    /\ candidates' = [candidates EXCEPT ![self] = candidates[self] \union {preImage[self][h]}]
                    /\ ballotingBlock' = [ballotingBlock EXCEPT ![self] = Combine(candidates'[self])]
             /\ pc' = [pc EXCEPT ![self] = "ln1"]
             /\ UNCHANGED << decision, voted, accepted, round, preImage, 
                             leader >>

nomination(self) == ln1(self) \/ ln2(self) \/ ln3(self) \/ ln4(self)
                       \/ ln5(self) \/ ln6(self) \/ ln7(self)

lb1(self) == /\ pc[self] = "lb1"
             /\ ballotingBlock[self[1]] # Bot
             /\ pc' = [pc EXCEPT ![self] = "lb2"]
             /\ UNCHANGED << ballotingBlock, decision, voted, accepted, round, 
                             candidates, preImage, leader >>

lb2(self) == /\ pc[self] = "lb2"
             /\ \E b \in {ballotingBlock[v] : v \in V} \ {Bot}:
                  /\ \A w \in V : decision[w] # Bot => b = decision[w]
                  /\ decision' = [decision EXCEPT ![self[1]] = b]
             /\ pc' = [pc EXCEPT ![self] = "Done"]
             /\ UNCHANGED << ballotingBlock, voted, accepted, round, 
                             candidates, preImage, leader >>

balloting(self) == lb1(self) \/ lb2(self)

Next == (\E self \in V: nomination(self))
           \/ (\E self \in {<<v, "balloting">> : v \in V}: balloting(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 
    
\* Concrete hashing for the model-checker:
TestH == 1..Cardinality(B)
TestHash(b) == 
    LET f == CHOOSE f \in [B -> H] : \A b1,b2 \in B : b1 # b2 => f[b1] # f[b2]
    IN f[b]

\* Debugging canaries:
Canary1 == \A v \in V : decision[v] = Bot
Canary2 == \A v \in V : Cardinality(candidates[v]) <= 1
Canary3 == \A v \in V : ballotingBlock[v] = Bot

TestQuorums == {Q \in SUBSET V : 2*Cardinality(Q)>Cardinality(V)}
TestBlocking == {Bl \in SUBSET V : Cardinality(Bl) > 1}

(***************************************************************************)
(* The type-safety invariant:                                              *)
(***************************************************************************)

TypeOkay ==
    /\ ballotingBlock \in [V -> B \cup {Bot}]
    /\ decision \in [V -> B \cup {Bot}]
    /\ voted \in [V -> SUBSET H]
    /\ accepted \in [V -> SUBSET H]
    /\ round \in [V -> Nat]
    /\ candidates \in [V -> SUBSET B]
    /\ preImage \in [V -> [H -> B \cup {Bot}]]
    /\ leader \in [V -> V \cup {Bot}]
    
(***************************************************************************)
(* Next we specify a liveness property that we can easily check with the   *)
(* TLC model-checker.                                                      *)
(*                                                                         *)
(* This property is that, if a validator v enters balloting, then          *)
(* eventually all validators enter balloting.  This will hold in simple    *)
(* configurations where the whole network is top tier.                     *)
(*                                                                         *)
(* For the property to hold, we also need to add fairness assumptions      *)
(* (e.g.  if a node can vote for a value, it will eventually do so)        *)
(***************************************************************************)

NominationLiveness ==
    \A v,w \in V : [](ballotingBlock[v] # Bot => <>(ballotingBlock[w] # Bot))
    
Fairness == WF_vars(TRUE)

\* Spec with fairness assumptions:


    
=============================================================================
\* Modification History
\* Last modified Mon Jan 23 14:19:47 PST 2023 by nano
\* Created Fri Jan 13 09:09:00 PST 2023 by nano
