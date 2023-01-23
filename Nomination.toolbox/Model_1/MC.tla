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
const_1674512395499224000 == 
{b1, b2}
----

\* MV CONSTANT definitions V
const_1674512395499225000 == 
{v1, v2, v3}
----

\* SYMMETRY definition
symm_1674512395499226000 == 
Permutations(const_1674512395499224000) \union Permutations(const_1674512395499225000)
----

\* CONSTANT definitions @modelParameterConstants:3Combine(C)
const_1674512395499227000(C) == 
CHOOSE c \in C : TRUE
----

\* CONSTANT definitions @modelParameterConstants:4Hash(b)
const_1674512395499228000(b) == 
TestHash(b)
----

\* CONSTANT definitions @modelParameterConstants:5H
const_1674512395499229000 == 
TestH
----

\* CONSTANT definitions @modelParameterConstants:6Quorum(v)
const_1674512395499230000(v) == 
{V}
----

\* CONSTANT definitions @modelParameterConstants:7Blocking(v)
const_1674512395499231000(v) == 
{Bl \in SUBSET V : Cardinality(Bl) = 1}
----

\* ACTION_CONSTRAINT definition @modelParameterActionConstraint:0
action_constr_1674512395499232000 ==
/\ \A v \in V : round[v]' <= 2
/\ \A v \in V : pc[<<v, "balloting">>] = "lb1"
----
=============================================================================
\* Modification History
\* Created Mon Jan 23 14:19:55 PST 2023 by nano
