------------- MODULE ChainConsensus -------------

(**************************************************************************************)
(* TODO: model passing blocks through the interface                                   *)
(**************************************************************************************)

EXTENDS Sequences, Naturals, TLC

CONSTANTS
    N \* the set of nodes
,   Block \* blocks of transactions
,   Chain \* sequences of blocks
,   DB \* database states
,   InitDB \* the initial database state
,   Apply(_, _) \* apply a block to a given DB state; may fail.
,   FAILED \* value of Apply indicating failure

(**************************************************************************************)
(* Partial order on chains                                                            *)
(**************************************************************************************)
c1 \preceq c2 == \* chain c1 is a prefix of chain c2
    /\  Len(c1) <= Len(c2)
    /\  \A i \in 1..Len(c1) : c1[i] = c2[i]
c1 \prec c2 == c1 # c2 /\ \preceq(c1, c2) \* strict prefix

(**************************************************************************************)
(* Two chains are compatible when one is a prefix of the other                        *)
(**************************************************************************************)
Compatible(c1, c2) == c1 \preceq c2 \/ c2 \preceq c1

(**************************************************************************************)
(* Applying a block to a database results in a new database state or fails            *)
(**************************************************************************************)
ASSUME FAILED \notin DB
ASSUME \A db \in DB, block \in Block :
    Apply(db, block) \in DB \cup {FAILED}

(**************************************************************************************)
(* A chain is a sequence of blocks. We can apply a blockchain to a database state     *)
(* by applying all the blocks one by one in order from the first block in the         *)
(* sequence to the last:                                                              *)
(**************************************************************************************)
RECURSIVE ApplyChain(_, _)
ApplyChain(db, chain) ==
    IF chain = <<>> THEN db
    ELSE LET db2 == Apply(db, Head(chain)) IN
        IF db2 = FAILED
        THEN FAILED
        ELSE ApplyChain(db2, Tail(chain))

(**************************************************************************************)
(* A chain is valid if applying it from the initial database state does not fail:     *)
(**************************************************************************************)
Valid(chain) == ApplyChain(InitDB, chain) # FAILED

(**************************************************************************************)
(* Variables for the behavioral specification:                                        *)
(**************************************************************************************)
VARIABLES
    proposalInterface \* interface variable for communicating proposals
,   validateInterface \* interface variable for validation
,   externalizeInterface \* interface variable for externalizing blocks
,   dbState \* local database state
,   proposedChains

TypeOK == \* the type invariant
    /\  proposalInterface \in
            [N -> {<<"NULL">>}
                \cup ({"PROPOSAL REQUEST"} \times Chain)
                \cup ({"PROPOSAL"} \times Chain)]
    /\  validateInterface \in
            [N -> {<<"NULL">>}
                \cup ({"VALIDATION REQUEST"} \times Chain)
                \cup {<<"VALID">>, <<"INVALID">>}]
    /\  externalizeInterface \in [N -> Chain]
    /\  dbState \in [N -> DB]
    /\  proposedChains \in SUBSET Chain

Init ==
    /\  proposalInterface = [n \in N |-> <<"NULL">>]
    /\  validateInterface = [n \in N |-> <<"NULL">>]
    /\  externalizeInterface = [n \in N |-> <<>>]
    /\  dbState = [n \in N |-> InitDB]
    /\  proposedChains = {}

(**************************************************************************************)
(* Consensus asks the application at node n for a new block. The new block must be    *)
(* valid when appended to the provided tip:                                           *)
(**************************************************************************************)
RequestProposal(n, tip) ==
    /\  externalizeInterface[n] \preceq tip
    /\  proposalInterface' = [proposalInterface EXCEPT ![n] = <<"PROPOSAL REQUEST", tip>>]
    /\  UNCHANGED <<validateInterface, externalizeInterface, dbState, proposedChains>>

(**************************************************************************************)
(* The application at node n proposes a new block to consensus:                       *)
(**************************************************************************************)
Propose(n, b) ==
    /\  proposalInterface[n][1] = "PROPOSAL REQUEST"
    /\  LET tip == proposalInterface[n][2]
            proposal == Append(tip, b)
        IN  /\  Valid(proposal)
            /\  proposalInterface' = [proposalInterface EXCEPT ![n] = <<"PROPOSAL", proposal>>]
            /\  proposedChains' = proposedChains \cup {proposal}
    /\  UNCHANGED <<validateInterface, externalizeInterface, dbState>>

(**************************************************************************************)
(* Consensus asks the application at node n to validate chain c:                      *)
(**************************************************************************************)
Validate(n, c) ==
    /\  validateInterface' = [validateInterface EXCEPT ![n] = <<"VALIDATION REQUEST", c>>]
    /\  UNCHANGED <<proposalInterface, externalizeInterface, dbState, proposedChains>>

(**************************************************************************************)
(* The application at node n responds to a validation request:                        *)
(**************************************************************************************)
Validated(n) ==
    /\  validateInterface[n][1] = "VALIDATION REQUEST"
    /\  LET valid == Valid(validateInterface[n][2])
        IN  validateInterface' = [validateInterface EXCEPT ![n] =
            IF valid THEN <<"VALID">> ELSE <<"INVALID">>]
    /\  UNCHANGED <<proposalInterface, externalizeInterface, dbState, proposedChains>>

(**************************************************************************************)
(* Consensus externalizes a new chain at node n                                       *)
(**************************************************************************************)
Externalize(n, c) ==
    /\  c \in proposedChains /\ Valid(c) \* c is a valid proposed chain
    /\  externalizeInterface[n] \prec c \* c extends the last externalized chain
    /\  \A n2 \in N : Compatible(externalizeInterface[n2], c) \* c is compatible with all externalized chains
    /\  externalizeInterface' = [externalizeInterface EXCEPT ![n] = c]
    /\  UNCHANGED <<proposalInterface, validateInterface, dbState, proposedChains>>

(**************************************************************************************)
(* The application at node n applies the latest externalizeInterface chain to its     *)
(* database                                                                           *)
(**************************************************************************************)
ApplyToDB(n) ==
    /\  dbState' = [dbState EXCEPT ![n] = ApplyChain(InitDB, externalizeInterface[n])]
    /\  UNCHANGED <<proposalInterface, validateInterface, externalizeInterface, proposedChains>>

(**************************************************************************************)
(* Final specification                                                                *)
(**************************************************************************************)

vars == <<proposalInterface, validateInterface, externalizeInterface, dbState, proposedChains>>

Next == \E n \in N, c \in Chain, b \in Block :
    \/  RequestProposal(n, c)
    \/  Propose(n, b)
    \/  Validate(n, c)
    \/  Validated(n)
    \/  Externalize(n, c)
    \/  ApplyToDB(n)

Spec == Init /\ [][Next]_vars

=====================================================================
