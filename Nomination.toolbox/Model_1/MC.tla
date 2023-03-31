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
const_16802866180332000 == 
{v1, v2}
----

\* MV CONSTANT definitions TxSet
const_16802866180333000 == 
{txs1, txs2}
----

\* SYMMETRY definition
symm_16802866180334000 == 
Permutations(const_16802866180332000) \union Permutations(const_16802866180333000)
----

\* CONSTANT definitions @modelParameterConstants:2Combine(C)
const_16802866180335000(C) == 
CHOOSE c \in C : TRUE
----

\* CONSTANT definitions @modelParameterConstants:3Hash(b)
const_16802866180336000(b) == 
TestHash(b)
----

\* CONSTANT definitions @modelParameterConstants:4H
const_16802866180337000 == 
TestH
----

\* CONSTANT definitions @modelParameterConstants:5Quorum(v)
const_16802866180338000(v) == 
{V}
----

\* CONSTANT definitions @modelParameterConstants:7Blocking(v)
const_16802866180339000(v) == 
{Bl \in SUBSET V : Cardinality(Bl) = 1}
----

\* ACTION_CONSTRAINT definition @modelParameterActionConstraint:0
action_constr_168028661803310000 ==
\A v \in V : round[v] <=3
----
=============================================================================
\* Modification History
\* Created Fri Mar 31 11:16:58 PDT 2023 by nano
