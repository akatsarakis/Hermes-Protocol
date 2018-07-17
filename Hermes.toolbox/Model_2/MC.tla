---- MODULE MC ----
EXTENDS Hermes, TLC

\* CONSTANT definitions @modelParameterConstants:0MAX_VERSION
const_1531411874533122000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:1NODES
const_1531411874533123000 == 
{1, 2, 3}
----

\* INIT definition @modelBehaviorInit:0
init_1531411874533124000 ==
HInit
----
\* NEXT definition @modelBehaviorNext:0
next_1531411874533125000 ==
HNext
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1531411874533126000 ==
HTypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1531411874533127000 ==
HConsistent
----
=============================================================================
\* Modification History
\* Created Thu Jul 12 17:11:14 BST 2018 by akatsarakis
