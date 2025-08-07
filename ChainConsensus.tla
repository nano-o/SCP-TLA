------------- MODULE ChainConsensus -------------

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
(* An operator to extract missing suffixes:                                           *)
(**************************************************************************************)
MissingSuffix(c1, c2) ==
    IF c1 \prec c2
    THEN [i \in 1..(Len(c2)-Len(c1)) |-> c2[Len(c1)+i]]
    ELSE <<>>

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
,   validChains
,   lastApplied \* last chain a node applied

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
    /\  validChains \in SUBSET Chain
    /\  lastApplied \in [N -> Chain]

Init ==
    /\  proposalInterface = [n \in N |-> <<"NULL">>]
    /\  validateInterface = [n \in N |-> <<"NULL">>]
    /\  externalizeInterface = [n \in N |-> <<>>]
    /\  dbState = [n \in N |-> InitDB]
    /\  validChains = {}
    /\  lastApplied = [n \in N |-> <<>>]

(**************************************************************************************)
(* Consensus asks the application at node n for a new block. The new block must be    *)
(* valid when appended to the provided tip:                                           *)
(**************************************************************************************)
RequestProposal(n, tip) ==
    /\  externalizeInterface[n] \preceq tip
    /\  tip \in validChains
    /\  proposalInterface' = [proposalInterface EXCEPT ![n] = <<"PROPOSAL REQUEST", tip>>]
    /\  UNCHANGED <<validateInterface, externalizeInterface, dbState, validChains, lastApplied>>

(**************************************************************************************)
(* The application at node n proposes a new block to consensus:                       *)
(**************************************************************************************)
Propose(n, b) ==
    /\  proposalInterface[n][1] = "PROPOSAL REQUEST"
    /\  LET tip == proposalInterface[n][2]
            proposal == Append(tip, b)
        IN  /\  Valid(proposal)
            /\  proposalInterface' = [proposalInterface EXCEPT ![n] = <<"PROPOSAL", proposal>>]
            /\  validChains' = validChains \cup {proposal}
    /\  UNCHANGED <<validateInterface, externalizeInterface, dbState, lastApplied>>

(**************************************************************************************)
(* Consensus asks the application at node n to validate chain c:                      *)
(**************************************************************************************)
Validate(n, c) ==
    /\  validateInterface' = [validateInterface EXCEPT ![n] = <<"VALIDATION REQUEST", c>>]
    /\  UNCHANGED <<proposalInterface, externalizeInterface, dbState, validChains, lastApplied>>

(**************************************************************************************)
(* The application at node n responds to a validation request:                        *)
(**************************************************************************************)
Validated(n) ==
    /\  validateInterface[n][1] = "VALIDATION REQUEST"
    /\  LET chain == validateInterface[n][2]
            valid == Valid(chain)
        IN  IF valid
            THEN    /\  validateInterface' = [validateInterface EXCEPT ![n] = <<"VALID">>]
                    /\  validChains' = validChains \cup {chain}
            ELSE    /\  validateInterface' = [validateInterface EXCEPT ![n] = <<"INVALID">>]
                    /\  UNCHANGED validChains
    /\  UNCHANGED <<proposalInterface, externalizeInterface, dbState, lastApplied>>

(**************************************************************************************)
(* Consensus externalizes a new chain at node n                                       *)
(**************************************************************************************)
Externalize(n, c) ==
    /\  c \in validChains
    /\  externalizeInterface[n] \prec c \* c extends the last chain externalized at node n
    /\  \A n2 \in N : Compatible(externalizeInterface[n2], c) \* c is compatible with all externalized chains
    /\  externalizeInterface' = [externalizeInterface EXCEPT ![n] = c]
    /\  UNCHANGED <<proposalInterface, validateInterface, dbState, validChains, lastApplied>>

(**************************************************************************************)
(* The application at node n applies the latest externalizeInterface chain to its     *)
(* database. In a more detailed specification, the application would need to query    *)
(* the consensus layer for missing blocks.                                            *)
(**************************************************************************************)
ApplyToDB(n) ==
    LET c == externalizeInterface[n]
        missing == MissingSuffix(lastApplied[n], c)
    IN  /\  dbState' = [dbState EXCEPT ![n] = ApplyChain(dbState[n], missing)]
        /\  lastApplied' = [lastApplied EXCEPT ![n] = c]
        /\  UNCHANGED <<proposalInterface, validateInterface, externalizeInterface, validChains>>

(**************************************************************************************)
(* Final specification                                                                *)
(**************************************************************************************)

vars == <<proposalInterface, validateInterface, externalizeInterface, dbState, validChains>>

Next == \E n \in N, c \in Chain, b \in Block :
    \/  RequestProposal(n, c)
    \/  Propose(n, b)
    \/  Validate(n, c)
    \/  Validated(n)
    \/  Externalize(n, c)
    \/  ApplyToDB(n)

Spec == Init /\ [][Next]_vars

=====================================================================
