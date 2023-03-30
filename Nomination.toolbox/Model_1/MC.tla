---- MODULE MC ----
EXTENDS Nomination, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2, v3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
txs1, txs2
----

\* MV CONSTANT definitions V
const_168014664997089000 == 
{v1, v2, v3}
----

\* MV CONSTANT definitions TxSet
const_168014664997090000 == 
{txs1, txs2}
----

\* SYMMETRY definition
symm_168014664997091000 == 
Permutations(const_168014664997089000) \union Permutations(const_168014664997090000)
----

\* CONSTANT definitions @modelParameterConstants:2Combine(C)
const_168014664997092000(C) == 
CHOOSE c \in C : TRUE
----

\* CONSTANT definitions @modelParameterConstants:3Hash(b)
const_168014664997093000(b) == 
TestHash(b)
----

\* CONSTANT definitions @modelParameterConstants:4H
const_168014664997094000 == 
TestH
----

\* CONSTANT definitions @modelParameterConstants:5Quorum(v)
const_168014664997095000(v) == 
{V}
----

\* CONSTANT definitions @modelParameterConstants:7Blocking(v)
const_168014664997096000(v) == 
{V}
----

\* ACTION_CONSTRAINT definition @modelParameterActionConstraint:0
action_constr_168014664997097000 ==
/\ \A v \in V : round[v]' <= 2
/\ \A v \in V : pc[<<v, "balloting">>] = "lb1"
----
=============================================================================
\* Modification History
\* Created Wed Mar 29 20:24:09 PDT 2023 by nano
