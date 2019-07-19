------------------------------- MODULE HermesRMWs -------------------------------
EXTENDS     Hermes
            
VARIABLES   Rmsgs,nodeFlagRMW      \* RMW change
                                 
HRMessage ==  \* Invalidation msgs exchanged by the Hermes Protocol w/ RMWs  
    [type: {"RINV"},       flagRMW   : {0,1}, \* RMW change
                           sender    : H_NODES,
                           version   : 0..H_MAX_VERSION,
                           tieBreaker: H_NODES] 

HRTypeOK ==  \* The type correctness invariant
    /\  HTypeOK
    /\  Rmsgs           \subseteq HRMessage
    /\  nodeFlagRMW     \in [H_NODES -> {0,1}]
                                              
HRInit == \* The initial predicate
    /\  HInit
    /\  Rmsgs       = {}
    /\  nodeFlagRMW = [n \in H_NODES |-> 0]  \* RMW change
-------------------------------------------------------------------------------------
\* A buffer maintaining all Invalidation  messages. Messages are only appended to this variable (not 
\* removed once delivered) intentionally to check protocols tolerance in dublicates and reorderings 
HRsend(m) == Rmsgs' = Rmsgs \union {m}  

smallerTS(v1,tb1,v2,tb2) == 
    /\ ~equalTS(v1,tb1,v2,tb2)
    /\ ~greaterTS(v1,tb1,v2,tb2)   
-------------------------------------------------------------------------------------
            
HRWrite(n) == \* Execute a write
    /\  nodeState[n]      \in {"valid", "invalid"}
    /\  nodeTS[n].version + 2 <= H_MAX_VERSION
    /\  nodeFlagRMW'      = [nodeFlagRMW     EXCEPT ![n] = 0] \* RMW change
    /\  nodeRcvedAcks'    = [nodeRcvedAcks   EXCEPT ![n] = {}]
    /\  nodeLastWriter'   = [nodeLastWriter  EXCEPT ![n] = n]
    /\  nodeState'        = [nodeState       EXCEPT ![n] = "write"]
    /\  nodeTS'           = [nodeTS          EXCEPT ![n].version    = 
                                                        nodeTS[n].version + 2, \* RMW change
                                                    ![n].tieBreaker = n]
    /\  nodeLastWriteTS'  = [nodeLastWriteTS EXCEPT ![n].version = 
                                                        nodeTS[n].version + 2, \* RMW change
                                                    ![n].tieBreaker = n]
    /\  HRsend([type        |-> "RINV",
              flagRMW     |-> 0,     \* RMW change
              sender      |-> n,
              version     |-> nodeTS[n].version + 2, \* RMW change
              tieBreaker  |-> n])              
    /\  UNCHANGED <<aliveNodes, msgs>>
    
\*    
HRRMW(n) == \* Execute an RMW
    /\  nodeState[n]      \in {"valid"}
    /\  nodeTS[n].version + 1 <= H_MAX_VERSION
    /\  nodeFlagRMW'      = [nodeFlagRMW     EXCEPT ![n] = 1]
    /\  nodeRcvedAcks'    = [nodeRcvedAcks   EXCEPT ![n] = {}]
    /\  nodeLastWriter'   = [nodeLastWriter  EXCEPT ![n] = n]
    /\  nodeState'        = [nodeState       EXCEPT ![n] = "write"]
    /\  nodeTS'           = [nodeTS          EXCEPT ![n].version    = 
                                                        nodeTS[n].version + 1,
                                                    ![n].tieBreaker = n]
    /\  nodeLastWriteTS'  = [nodeLastWriteTS EXCEPT ![n].version = 
                                                        nodeTS[n].version + 1,
                                                    ![n].tieBreaker = n]
    /\  HRsend([type        |-> "RINV",
              flagRMW     |-> 1,   
              sender      |-> n,
              version     |-> nodeTS[n].version + 1, \* RMW change
              tieBreaker  |-> n])              
    /\  UNCHANGED <<aliveNodes, msgs>>
                
HRReplayWrite(n) == \* Execute a write-replay
    /\  nodeState[n] = "invalid"
    /\  ~isAlive(nodeLastWriter[n])
    /\  nodeLastWriter'  = [nodeLastWriter   EXCEPT ![n] = n]
    /\  nodeState'       = [nodeState        EXCEPT ![n] = "replay"]
    /\  nodeRcvedAcks'   = [nodeRcvedAcks    EXCEPT ![n] = {}]
    /\  nodeLastWriteTS' = [nodeLastWriteTS  EXCEPT ![n] = nodeTS[n]]
    /\  HRsend([type       |-> "RINV",
              flagRMW    |-> nodeFlagRMW[n],     \* RMW change
              sender     |-> n,
              version    |-> nodeTS[n].version, 
              tieBreaker |-> nodeTS[n].tieBreaker])
    /\  UNCHANGED <<nodeTS, aliveNodes, msgs, nodeFlagRMW>> \* RMW change

\* Keep the HRead, HRcvAck and HSendVals the same as Hermes w/o RMWs
HRRead(n) == 
    /\ HRead(n)
    /\ UNCHANGED <<nodeFlagRMW, Rmsgs>>
    
HRRcvAck(n) == 
    /\ HRcvAck(n)
    /\ UNCHANGED <<nodeFlagRMW, Rmsgs>>
    
HRSendVals(n) == 
    /\ HSendVals(n)
    /\ UNCHANGED <<nodeFlagRMW, Rmsgs>> 
       
HRCoordinatorActions(n) ==   \* Actions of a read/write coordinator 
    \/ HRRead(n)          
    \/ HRReplayWrite(n) 
    \/ HRWrite(n)      
    \/ HRRMW(n)      
    \/ HRRcvAck(n)
    \/ HRSendVals(n) 
-------------------------------------------------------------------------------------               

HRRcvWriteInv(n) ==  \* Process a received invalidation for a write
    \E m \in Rmsgs: 
        /\ m.type = "RINV"
        /\ m.sender /= n
        /\ m.flagRMW = 0 \* RMW change
        \* always acknowledge a received invalidation (irrelevant to the timestamp)
        /\ send([type       |-> "ACK",
                 sender     |-> n,   
                 version    |-> m.version,
                 tieBreaker |-> m.tieBreaker])
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
           \/ /\ ~greaterTS(m.version,
                            m.tieBreaker,
                            nodeTS[n].version, 
                            nodeTS[n].tieBreaker)
              /\ UNCHANGED <<nodeState, nodeTS, nodeLastWriter, nodeFlagRMW>>
        /\ UNCHANGED <<nodeLastWriteTS, aliveNodes, nodeRcvedAcks, Rmsgs>>
 
HRRcvRMWInv(n) ==  \* Process a received invalidation for a write
    \E m \in Rmsgs: 
        /\ m.type = "RINV"
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
              /\ send([type       |-> "ACK",
                       sender     |-> n,   
                       version    |-> m.version,
                       tieBreaker |-> m.tieBreaker])
              /\ \/ /\ nodeState[n] \in {"valid", "invalid", "replay"}
                    /\ nodeState' = [nodeState EXCEPT ![n] = "invalid"]
                 \/ /\ nodeState[n] \in {"write", "invalid_write"} 
                    /\ nodeFlagRMW[n] = 0      \* RMW change
                    /\ nodeState' = [nodeState EXCEPT ![n] = "invalid_write"] 
                 \/ /\ nodeState[n]= "write"   \* RMW change
                    /\ nodeFlagRMW[n] = 1      \* RMW change
                    /\ nodeState' = [nodeState EXCEPT ![n] = "invalid"]    \* RMW change
             /\ UNCHANGED <<Rmsgs>>
          \/ /\ equalTS(m.version,
                         m.tieBreaker,
                         nodeTS[n].version, 
                         nodeTS[n].tieBreaker)
             \* acknowledge a received invalidation (w/ equal timestamp)
             /\ send([type       |-> "ACK",
                       sender     |-> n,   
                       version    |-> m.version,
                       tieBreaker |-> m.tieBreaker])
             /\ UNCHANGED <<nodeState, nodeTS, nodeLastWriter, nodeFlagRMW, Rmsgs>>
          \/ /\ smallerTS(m.version,
                          m.tieBreaker,
                          nodeTS[n].version, 
                          nodeTS[n].tieBreaker)
             /\  HRsend([type       |-> "RINV",
                         flagRMW    |-> nodeFlagRMW[n],     \* RMW change
                         sender     |-> n,
                         version    |-> nodeTS[n].version, 
                         tieBreaker |-> nodeTS[n].tieBreaker])
             /\ UNCHANGED <<nodeState, nodeTS, nodeLastWriter, nodeFlagRMW, msgs>>
        /\ UNCHANGED <<nodeLastWriteTS, aliveNodes, nodeRcvedAcks>> 
 
         
\* Keep the HRcvVals the same as Hermes w/o RMWs
HRRcvVal(n) == 
    /\ HRcvVal(n)
    /\ UNCHANGED <<nodeFlagRMW, Rmsgs>>
                           
HRFollowerActions(n) ==  \* Actions of a write follower
    \/ HRRcvWriteInv(n)
    \/ HRRcvRMWInv(n)
    \/ HRRcvVal(n) 
-------------------------------------------------------------------------------------                       

HRNodeFailure(n) == 
    /\ nodeFailure(n)
    /\ UNCHANGED <<nodeFlagRMW, Rmsgs>>
    
HRNext == \* Modeling Hermes protocol (Coordinator and Follower actions while emulating failures)
    \E n \in aliveNodes:       
            \/ HRFollowerActions(n)
            \/ HRCoordinatorActions(n)
            \/ HRNodeFailure(n) \* emulate node failures
=============================================================================
