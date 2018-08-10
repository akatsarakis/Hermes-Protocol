---- MODULE MC ----
EXTENDS Hermes, TLC

\* CONSTANT definitions @modelParameterConstants:0MAX_VERSION
const_15321030086588000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:1NODES
const_15321030086599000 == 
{1, 2, 3}
----

\* INIT definition @modelBehaviorInit:0
init_153210300865910000 ==
HInit
----
\* NEXT definition @modelBehaviorNext:0
next_153210300865911000 ==
HNext
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_153210300865912000 ==
HTypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_153210300865913000 ==
HConsistent
----
=============================================================================
\* Modification History
\* Created Fri Jul 20 17:10:08 BST 2018 by akatsarakis
