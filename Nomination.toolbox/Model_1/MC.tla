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
const_167450102626212000 == 
{b1, b2}
----

\* MV CONSTANT definitions V
const_167450102626213000 == 
{v1, v2, v3}
----

\* SYMMETRY definition
symm_167450102626214000 == 
Permutations(const_167450102626212000) \union Permutations(const_167450102626213000)
----

\* CONSTANT definitions @modelParameterConstants:3Combine(C)
const_167450102626215000(C) == 
CHOOSE c \in C : TRUE
----

\* CONSTANT definitions @modelParameterConstants:4Hash(b)
const_167450102626216000(b) == 
TestHash(b)
----

\* CONSTANT definitions @modelParameterConstants:5H
const_167450102626217000 == 
TestH
----

\* CONSTANT definitions @modelParameterConstants:6Quorum(v)
const_167450102626218000(v) == 
TestQuorums
----

\* CONSTANT definitions @modelParameterConstants:7Blocking(v)
const_167450102626219000(v) == 
TestBlocking
----

\* ACTION_CONSTRAINT definition @modelParameterActionConstraint:0
action_constr_167450102626220000 ==
\A v \in V : round[v]' <= 2
----
=============================================================================
\* Modification History
\* Created Mon Jan 23 11:10:26 PST 2023 by nano
