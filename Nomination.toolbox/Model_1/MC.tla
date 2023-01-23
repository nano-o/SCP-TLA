---- MODULE MC ----
EXTENDS Nomination, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
b1, b2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2, v3
----

\* MV CONSTANT definitions B
const_1674491516657190000 == 
{b1, b2}
----

\* MV CONSTANT definitions V
const_1674491516657191000 == 
{v1, v2, v3}
----

\* SYMMETRY definition
symm_1674491516657192000 == 
Permutations(const_1674491516657190000) \union Permutations(const_1674491516657191000)
----

\* CONSTANT definitions @modelParameterConstants:3Combine(C)
const_1674491516657193000(C) == 
CHOOSE c \in C : TRUE
----

\* CONSTANT definitions @modelParameterConstants:4Hash(b)
const_1674491516657194000(b) == 
TestHash(b)
----

\* CONSTANT definitions @modelParameterConstants:5H
const_1674491516657195000 == 
TestH
----

\* CONSTANT definitions @modelParameterConstants:6Quorum(v)
const_1674491516657196000(v) == 
TestQuorums
----

\* CONSTANT definitions @modelParameterConstants:7Blocking(v)
const_1674491516657197000(v) == 
TestBlocking
----

\* ACTION_CONSTRAINT definition @modelParameterActionConstraint:0
action_constr_1674491516657198000 ==
\A v \in V : round[v]' <= 2
----
=============================================================================
\* Modification History
\* Created Mon Jan 23 08:31:56 PST 2023 by nano
