---- MODULE MC ----
EXTENDS Hermes, TLC

\* CONSTANT definitions @modelParameterConstants:0MAX_VERSION
const_1531325623801104000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:1NODES
const_1531325623801105000 == 
{1, 2, 3}
----

\* INIT definition @modelBehaviorInit:0
init_1531325623801106000 ==
HInit
----
\* NEXT definition @modelBehaviorNext:0
next_1531325623801107000 ==
HNext
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1531325623801108000 ==
HTypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1531325623801109000 ==
HConsistent
----
=============================================================================
\* Modification History
\* Created Wed Jul 11 17:13:43 BST 2018 by akatsarakis
