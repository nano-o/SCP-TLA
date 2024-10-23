---- MODULE MC ----
EXTENDS Balloting, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
n1, n2, n3
----

\* MV CONSTANT definitions N
const_172960534740389000 == 
{n1, n2, n3}
----

\* SYMMETRY definition
symm_172960534740390000 == 
Permutations(const_172960534740389000)
----

\* CONSTANT definitions @modelParameterConstants:1V
const_172960534740391000 == 
{0,1}
----

\* CONSTANT definitions @modelParameterConstants:2BallotNumber
const_172960534740392000 == 
{0,1,2}
----

\* CONSTANT definitions @modelParameterConstants:3Quorum
const_172960534740393000 == 
{{n1,n2},{n2,n3},{n3,n1}}
----

\* CONSTANT definitions @modelParameterConstants:4FailProneSet
const_172960534740394000 == 
{{}}
----

=============================================================================
\* Modification History
\* Created Tue Oct 22 06:55:47 PDT 2024 by nano
