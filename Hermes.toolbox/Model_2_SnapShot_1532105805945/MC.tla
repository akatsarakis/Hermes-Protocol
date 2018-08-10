---- MODULE MC ----
EXTENDS Hermes, TLC

\* CONSTANT definitions @modelParameterConstants:0MAX_VERSION
const_153210331958032000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:1NODES
const_153210331958033000 == 
{1, 2, 3}
----

\* INIT definition @modelBehaviorInit:0
init_153210331958034000 ==
HInit
----
\* NEXT definition @modelBehaviorNext:0
next_153210331958035000 ==
HNext
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_153210331958036000 ==
HTypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_153210331958037000 ==
HConsistent
----
=============================================================================
\* Modification History
\* Created Fri Jul 20 17:15:19 BST 2018 by akatsarakis
