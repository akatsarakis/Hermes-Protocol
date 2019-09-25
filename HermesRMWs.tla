------------------------------- MODULE HermesRMWs -------------------------------
EXTENDS     Hermes
            
VARIABLES   Rmsgs,
            nodeFlagRMW,
            committedRMWs,
            committedWrites
                                 
HRMessage ==  \* Invalidation msgs exchanged by the Hermes Protocol w/ RMWs  
    [type: {"RINV"},       flagRMW   : {0,1}, \* RMW change
                           epochID   : 0..(Cardinality(H_NODES) - 1),
                           sender    : H_NODES,
                           version   : 0..H_MAX_VERSION,
                           tieBreaker: H_NODES] 

HRts == [version: 0..H_MAX_VERSION,
         tieBreaker: H_NODES]

HRTypeOK ==  \* The type correctness invariant
    /\  HTypeOK
    /\  Rmsgs           \subseteq HRMessage
    /\  nodeFlagRMW     \in [H_NODES -> {0,1}]
    /\  committedRMWs   \subseteq HRts
    /\  committedWrites \subseteq HRts
    
HRSemanticsRMW ==  \* The invariant that an we cannot have two operations committed 
                   \* with same versions (i.e., that read the same value unless they are both writes)
    /\ \A x \in committedRMWs:
        \A y \in committedWrites: /\ x.version /= y.version
                                  /\ x.version /= y.version - 1
    /\ \A x,y \in committedRMWs: \/ x.version /= y.version
                                 \/ x.tieBreaker = y.tieBreaker
HRInit == \* The initial predicate
    /\  HInit
    /\  Rmsgs       = {}
    /\  committedRMWs   = {}
    /\  committedWrites = {}
    /\  nodeFlagRMW = [n \in H_NODES |-> 0]  \* RMW change
    
    
-------------------------------------------------------------------------------------

\* A buffer maintaining all Invalidation  messages. Messages are only appended to this variable (not 
\* removed once delivered) intentionally to check protocols tolerance in dublicates and reorderings 
HRsend(m) == Rmsgs' = Rmsgs \union {m}  

smallerTS(v1,tb1,v2,tb2) == 
    /\ ~equalTS(v1,tb1,v2,tb2)
    /\ ~greaterTS(v1,tb1,v2,tb2)   

hr_upd_nothing ==
    /\ UNCHANGED <<nodeFlagRMW, Rmsgs, committedRMWs, committedWrites>>

hr_completeWrite(ver, tieB) ==
    /\ committedWrites' = committedWrites \union {[version |-> ver, tieBreaker |-> tieB]} 
    /\ UNCHANGED <<Rmsgs, nodeFlagRMW, committedRMWs>>

hr_completeRMW(ver, tieB) ==
    /\ committedRMWs' = committedRMWs \union {[version |-> ver, tieBreaker |-> tieB]} 
    /\ UNCHANGED <<Rmsgs, nodeFlagRMW, committedWrites>>


-------------------------------------------------------------------------------------
\* Helper functions 
hr_upd_state(n, newVersion, newTieBreaker, newState, newAcks, flagRMW) == 
    /\  nodeFlagRMW'      = [nodeFlagRMW     EXCEPT ![n] = flagRMW] \* RMW change
    /\  h_upd_state(n, newVersion, newTieBreaker, newState, newAcks)

hr_send_inv(n, newVersion, newTieBreaker, flagRMW) ==  
    /\  HRsend([type        |-> "RINV",
                epochID     |-> epochID, \* we always use the latest epochID
                flagRMW     |-> flagRMW, \* RMW change
                sender      |-> n,
                version     |-> newVersion, 
                tieBreaker  |-> newTieBreaker])              

hr_upd_actions(n, newVersion, newTieBreaker, newState, newAcks, flagRMW) == \* Execute a write
    /\  hr_upd_state(n, newVersion, newTieBreaker, newState, newAcks, flagRMW)
    /\  hr_send_inv(n, newVersion, newTieBreaker, flagRMW)
    /\  UNCHANGED <<aliveNodes, epochID, msgs, committedRMWs, committedWrites>>
 

hr_upd_replay_actions(n, acks) == \* Apply a write-replay using same TS (version, Tie Breaker) 
                                \* and either reset acks or keep already gathered acks
    /\  hr_upd_actions(n, nodeTS[n].version, nodeTS[n].tieBreaker, "replay", acks, nodeFlagRMW[n])
 
 
-------------------------------------------------------------------------------------
\* Coordinator functions 

HRWrite(n) == \* Execute a write
\*    /\  nodeState[n]      \in {"valid", "invalid"}
    \* writes in invalid state are also supported as an optimization
    /\  nodeState[n]            = "valid"
    /\  nodeTS[n].version + 2 <= H_MAX_VERSION \* condition to bound execution
    /\  hr_upd_actions(n, nodeTS[n].version + 2, n, "write", {}, 0)
   
HRRMW(n) == \* Execute an RMW
    /\  nodeState[n]            = "valid"
    /\  nodeTS[n].version + 1 <= H_MAX_VERSION \* condition to bound execution
    /\  hr_upd_actions(n, nodeTS[n].version + 1, n, "write", {}, 1)
               
HRWriteReplay(n) == \* Execute a write-replay
    /\  nodeState[n] \in {"write", "replay"}
    /\  nodeWriteEpochID[n] < epochID
    /\  ~receivedAllAcks(n) \* optimization to not replay when we have gathered acks from all alive
    /\  nodeFlagRMW[n] = 0
    /\  hr_upd_replay_actions(n, nodeRcvedAcks[n])

HRRMWReplay(n) == \* Execute an RMW-replay
    /\  nodeState[n] \in {"write", "replay"}
    /\  nodeWriteEpochID[n] < epochID
    /\  ~receivedAllAcks(n) \* optimization to not replay when we have gathered acks from all alive
    /\  nodeFlagRMW[n] = 1
    /\  hr_upd_replay_actions(n, {})

\* Keep the HRead, HRcvAck and HSendVals the same as Hermes w/o RMWs
HRRead(n) == 
    /\ HRead(n)
    /\ hr_upd_nothing 
    
HRRcvAck(n) == 
    /\ HRcvAck(n)
    /\ hr_upd_nothing 
    
HRSendValsRMW(n) == 
    /\ nodeFlagRMW[n] = 1
    /\ HSendVals(n)
    /\ hr_completeRMW(nodeTS[n].version, nodeTS[n].tieBreaker)
HRSendValsWrite(n) == 
    /\ nodeFlagRMW[n] = 0
    /\ HSendVals(n)
    /\ hr_completeWrite(nodeTS[n].version, nodeTS[n].tieBreaker)

HRSendVals(n) == 
    \/ HRSendValsRMW(n)
    \/ HRSendValsWrite(n)
      
HRCoordinatorActions(n) ==   \* Actions of a read/write/RMW coordinator 
    \/ HRRead(n)          
    \/ HRRMWReplay(n)
    \/ HRWriteReplay(n) 
    \/ HRWrite(n)      
    \/ HRRMW(n)      
    \/ HRRcvAck(n)
    \/ HRSendVals(n) 
    
    
-------------------------------------------------------------------------------------               
\* Follower functions 

HRRcvWriteInv(n) ==  \* Process a received invalidation for a write
    \E m \in Rmsgs: 
        /\ m.type = "RINV"
        /\ m.epochID  = epochID
        /\ m.sender /= n
        /\ m.flagRMW = 0 \* RMW change
        \* always acknowledge a received invalidation (irrelevant to the timestamp)
        /\ h_send_inv_or_ack(n, m.version, m.tieBreaker, "ACK") 
        /\ \/ /\ greaterTS(m.version,
                            m.tieBreaker,
                            nodeTS[n].version, 
                            nodeTS[n].tieBreaker)
              /\ nodeFlagRMW' = [nodeFlagRMW EXCEPT ![n] = m.flagRMW] \* RMW change            
              /\ nodeLastWriter' = [nodeLastWriter EXCEPT ![n] = m.sender]
              /\ nodeTS' = [nodeTS EXCEPT ![n].version    = m.version,
                                          ![n].tieBreaker = m.tieBreaker]
              /\ \/ /\ nodeState[n] \in {"valid", "invalid", "replay"}
                    /\ nodeState' = [nodeState EXCEPT ![n] = "invalid"]
                 \/ /\ nodeState[n] \in {"write", "invalid_write"} 
                    /\ nodeFlagRMW[n] = 0      \* RMW change
                    /\ nodeState' = [nodeState EXCEPT ![n] = "invalid_write"] 
                 \/ /\ nodeState[n]= "write"   \* RMW change
                    /\ nodeFlagRMW[n] = 1      \* RMW change
                    /\ nodeState' = [nodeState EXCEPT ![n] = "invalid"]    \* RMW change
           \/ /\ ~greaterTS(m.version, m.tieBreaker,
                            nodeTS[n].version, nodeTS[n].tieBreaker)
              /\ UNCHANGED <<nodeState, nodeTS, nodeLastWriter, nodeFlagRMW>>
        /\ UNCHANGED <<nodeLastWriteTS, aliveNodes, nodeRcvedAcks, Rmsgs, 
                       epochID, nodeWriteEpochID, committedRMWs, committedWrites>>
 
HRRcvRMWInv(n) ==  \* Process a received invalidation for a write
    \E m \in Rmsgs: 
        /\ m.type = "RINV"
        /\ m.epochID  = epochID
        /\ m.sender /= n
        /\ m.flagRMW = 1        
        /\ \/ /\ greaterTS(m.version,
                           m.tieBreaker,
                           nodeTS[n].version, 
                           nodeTS[n].tieBreaker)
              /\ nodeFlagRMW' = [nodeFlagRMW EXCEPT ![n] = m.flagRMW] \* RMW change            
              /\ nodeLastWriter' = [nodeLastWriter EXCEPT ![n] = m.sender]
              /\ nodeTS' = [nodeTS EXCEPT ![n].version    = m.version,
                                          ![n].tieBreaker = m.tieBreaker]
              \* acknowledge a received invalidation (w/ greater timestamp)
              /\ h_send_inv_or_ack(n, m.version, m.tieBreaker, "ACK") 
              /\ \/ /\ nodeState[n] \in {"valid", "invalid", "replay"}
                    /\ nodeState' = [nodeState EXCEPT ![n] = "invalid"]
                 \/ /\ nodeState[n] \in {"write", "invalid_write"} 
                    /\ nodeFlagRMW[n] = 0      \* RMW change
                    /\ nodeState' = [nodeState EXCEPT ![n] = "invalid_write"] 
                 \/ /\ nodeState[n]= "write"   \* RMW change
                    /\ nodeFlagRMW[n] = 1      \* RMW change
                    /\ nodeState' = [nodeState EXCEPT ![n] = "invalid"]    \* RMW change
             /\ UNCHANGED <<Rmsgs>>
          \/ /\ equalTS(m.version, m.tieBreaker,
                         nodeTS[n].version, nodeTS[n].tieBreaker)
             \* acknowledge a received invalidation (w/ equal timestamp)
             /\ h_send_inv_or_ack(n, m.version, m.tieBreaker, "ACK") 
             /\ UNCHANGED <<nodeState, nodeTS, nodeLastWriter, nodeFlagRMW, Rmsgs>>
          \/ /\ smallerTS(m.version, m.tieBreaker,
                          nodeTS[n].version, nodeTS[n].tieBreaker)
             /\ hr_send_inv(n, nodeTS[n].version, nodeTS[n].tieBreaker, nodeFlagRMW[n])
             /\ UNCHANGED <<nodeState, nodeTS, nodeLastWriter, nodeFlagRMW, msgs>>
        /\ UNCHANGED <<nodeLastWriteTS, aliveNodes, nodeRcvedAcks, epochID, 
                       nodeWriteEpochID, committedRMWs, committedWrites>> 
 
         
\* Keep the HRcvVals the same as Hermes w/o RMWs
HRRcvVal(n) == 
    /\ HRcvVal(n)
    /\ hr_upd_nothing
    
    
HRFollowerWriteReplay(n) == \* Execute a write-replay when coordinator failed
    /\  nodeState[n] = "invalid"
    /\  ~isAlive(nodeLastWriter[n])
    /\  hr_upd_replay_actions(n, {})
                           

HRFollowerActions(n) ==  \* Actions of a write follower
    \/ HRFollowerWriteReplay(n)
    \/ HRRcvWriteInv(n)
    \/ HRRcvRMWInv(n)
    \/ HRRcvVal(n) 
-------------------------------------------------------------------------------------                       

HRNodeFailure(n) == 
    /\ nodeFailure(n)
    /\ hr_upd_nothing
    
    
HRNext == \* Modeling Hermes protocol (Coordinator and Follower actions while emulating failures)
    \E n \in aliveNodes:       
            \/ HRFollowerActions(n)
            \/ HRCoordinatorActions(n)
            \/ HRNodeFailure(n) \* emulate node failures
            
=============================================================================
