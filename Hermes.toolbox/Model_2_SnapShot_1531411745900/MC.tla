---- MODULE MC ----
EXTENDS Hermes, TLC

\* CONSTANT definitions @modelParameterConstants:0MAX_VERSION
const_1531411743868116000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:1NODES
const_1531411743868117000 == 
{1, 2, 3}
----

\* INIT definition @modelBehaviorInit:0
init_1531411743868118000 ==
HInit
----
\* NEXT definition @modelBehaviorNext:0
next_1531411743868119000 ==
HNext
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1531411743871120000 ==
HTypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1531411743871121000 ==
HConsistent
----
=============================================================================
\* Modification History
\* Created Thu Jul 12 17:09:03 BST 2018 by akatsarakis
