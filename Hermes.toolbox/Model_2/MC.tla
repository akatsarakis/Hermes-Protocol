---- MODULE MC ----
EXTENDS Hermes, TLC

\* CONSTANT definitions @modelParameterConstants:0MAX_VERSION
const_15469636376222000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:1NODES
const_15469636376223000 == 
{1, 2, 3}
----

\* INIT definition @modelBehaviorInit:0
init_15469636376224000 ==
HInit
----
\* NEXT definition @modelBehaviorNext:0
next_15469636376225000 ==
HNext
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_15469636376226000 ==
HTypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_15469636376227000 ==
HConsistent
----
=============================================================================
\* Modification History
\* Created Tue Jan 08 16:07:17 GMT 2019 by akatsarakis
