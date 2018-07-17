---- MODULE MC ----
EXTENDS Hermes, TLC

\* CONSTANT definitions @modelParameterConstants:0MAX_VERSION
const_1531325685626110000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:1NODES
const_1531325685626111000 == 
{1, 2, 3}
----

\* INIT definition @modelBehaviorInit:0
init_1531325685626112000 ==
HInit
----
\* NEXT definition @modelBehaviorNext:0
next_1531325685626113000 ==
HNext
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1531325685626114000 ==
HTypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1531325685626115000 ==
HConsistent
----
=============================================================================
\* Modification History
\* Created Wed Jul 11 17:14:45 BST 2018 by akatsarakis
