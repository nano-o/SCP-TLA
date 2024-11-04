---- MODULE MC ----
EXTENDS AbstractBallotingWithPrepare, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
n1, n2, n3
----

\* MV CONSTANT definitions N
const_17307472103018000 == 
{n1, n2, n3}
----

\* SYMMETRY definition
symm_17307472103019000 == 
Permutations(const_17307472103018000)
----

\* CONSTANT definitions @modelParameterConstants:0BallotNumber
const_173074721030110000 == 
{0,1,2}
----

\* CONSTANT definitions @modelParameterConstants:1FailProneSet
const_173074721030111000 == 
{{n1},{n3}}
----

\* CONSTANT definitions @modelParameterConstants:3V
const_173074721030112000 == 
{0,1}
----

\* CONSTANT definitions @modelParameterConstants:4Quorum
const_173074721030113000 == 
{{n1,n2},{n2,n3}}
----

=============================================================================
\* Modification History
\* Created Mon Nov 04 11:06:50 PST 2024 by nano
