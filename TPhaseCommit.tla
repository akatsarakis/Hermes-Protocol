---------------------------- MODULE TPhaseCommit ----------------------------
CONSTANT RM \* the set of all RMs
VARIABLE rmState

TCTypeSafety == rmState \in [RM -> {"working", "prepared", "commited", "aborted"}]

TCInit == rmState = [r \in RM |-> "working"]

Prepare(r) ==   /\ rmState[r] = "working"
                /\ rmState'   = [rmState EXCEPT ![r] = "prepared"]
                
Decide(r) ==  \/    /\ rmState[r] = "prepared"
                    /\ \A s \in RM: rmState[s] \in {"prepared", "commited"}
                    /\ rmState'   = [rmState EXCEPT ![r] = "commited"]
              \/    /\ rmState[r] \in {"prepared", "working"}
                    /\ \A s \in RM: rmState[s] /= "commited"
                    /\ rmState'   = [rmState EXCEPT ![r] = "aborted"]
                    
TCNext == \E r \in RM: Prepare(r) \/ Decide(r)

TCConsistent == \A r1,r2 \in RM: ~ /\ rmState[r1] = "commited" 
                                   /\ rmState[r2] = "aborted"

=============================================================================
\* Modification History
\* Last modified Sun Jul 08 10:21:56 BST 2018 by akatsarakis
\* Created Sun Jul 08 09:58:06 BST 2018 by akatsarakis
