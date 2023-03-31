---- MODULE MC ----
EXTENDS Nomination, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
txs1, txs2
----

\* MV CONSTANT definitions V
const_1680237127911458000 == 
{v1, v2}
----

\* MV CONSTANT definitions TxSet
const_1680237127911459000 == 
{txs1, txs2}
----

\* SYMMETRY definition
symm_1680237127911460000 == 
Permutations(const_1680237127911458000) \union Permutations(const_1680237127911459000)
----

\* CONSTANT definitions @modelParameterConstants:2Combine(C)
const_1680237127911461000(C) == 
CHOOSE c \in C : TRUE
----

\* CONSTANT definitions @modelParameterConstants:3Hash(b)
const_1680237127911462000(b) == 
TestHash(b)
----

\* CONSTANT definitions @modelParameterConstants:4H
const_1680237127911463000 == 
TestH
----

\* CONSTANT definitions @modelParameterConstants:5Quorum(v)
const_1680237127911464000(v) == 
{V}
----

\* CONSTANT definitions @modelParameterConstants:7Blocking(v)
const_1680237127911465000(v) == 
{Bl \in SUBSET V : Cardinality(Bl) = 1}
----

\* ACTION_CONSTRAINT definition @modelParameterActionConstraint:0
action_constr_1680237127911466000 ==
\A v \in V : round[v] <=3
----
=============================================================================
\* Modification History
\* Created Thu Mar 30 21:32:07 PDT 2023 by nano
