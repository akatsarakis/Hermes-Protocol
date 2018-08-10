---- MODULE MC ----
EXTENDS Hermes, TLC

\* CONSTANT definitions @modelParameterConstants:0MAX_VERSION
const_15321027168232000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:1NODES
const_15321027168233000 == 
{1, 2, 3}
----

\* INIT definition @modelBehaviorInit:0
init_15321027168244000 ==
HInit
----
\* NEXT definition @modelBehaviorNext:0
next_15321027168245000 ==
HNext
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_15321027168246000 ==
HTypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_15321027168247000 ==
HConsistent
----
=============================================================================
\* Modification History
\* Created Fri Jul 20 17:05:16 BST 2018 by akatsarakis
