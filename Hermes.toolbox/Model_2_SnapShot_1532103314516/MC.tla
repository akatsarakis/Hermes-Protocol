---- MODULE MC ----
EXTENDS Hermes, TLC

\* CONSTANT definitions @modelParameterConstants:0MAX_VERSION
const_153210312592120000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:1NODES
const_153210312592121000 == 
{1, 2, 3}
----

\* INIT definition @modelBehaviorInit:0
init_153210312592122000 ==
HInit
----
\* NEXT definition @modelBehaviorNext:0
next_153210312592123000 ==
HNext
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_153210312592124000 ==
HTypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_153210312592125000 ==
HConsistent
----
=============================================================================
\* Modification History
\* Created Fri Jul 20 17:12:05 BST 2018 by akatsarakis
