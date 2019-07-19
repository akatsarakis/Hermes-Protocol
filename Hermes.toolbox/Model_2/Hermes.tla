------------------------------- MODULE Hermes -------------------------------
EXTENDS     Integers

CONSTANTS   NODES,
            MAX_VERSION
            
VARIABLES   msgs,
            nodeTS,
            nodeState, 
            nodeRcvedAcks,
            nodeLastWriter,
            nodeLastWriteTS,
            aliveNodes
            
            
\* The consistent invariant: all alive nodes in valid state should have the same value / TS         
HConsistent == 
    \A k,s \in aliveNodes:  \/ nodeState[k] /= "valid"
                            \/ nodeState[s] /= "valid" 
                            \/ nodeTS[k] = nodeTS[s]
                            
                                 
HMessage ==  \* Messages exchanged by the Protocol   
    [type: {"INV", "ACK"}, sender    : NODES,
                           version   : 0..MAX_VERSION, 
                           tieBreaker: NODES] 
        \union
    [type: {"VAL"},        version   : 0..MAX_VERSION, 
                           tieBreaker: NODES] 

HTypeOK ==  \* The type correctness invariant
    /\  msgs           \subseteq HMessage
    /\  aliveNodes     \subseteq NODES
    /\ \A n \in NODES: nodeRcvedAcks[n] \subseteq (NODES \ {n})
    /\  nodeLastWriter  \in [NODES -> NODES]
    /\  nodeLastWriteTS \in [NODES -> [version   : 0..MAX_VERSION,
                                       tieBreaker: NODES         ]]
    /\  nodeTS          \in [NODES -> [version   : 0..MAX_VERSION,
                                       tieBreaker: NODES         ]]
    /\  nodeState       \in [NODES -> {"valid", "invalid", "invalid_write", 
                                       "write", "replay"}]
                                              
HInit == \* The initial predicate
    /\  msgs            = {}
    /\  aliveNodes      = NODES
    /\  nodeRcvedAcks   = [n \in NODES |-> {}]
    /\  nodeState       = [n \in NODES |-> "valid"]
    /\  nodeLastWriter  = [n \in NODES |-> CHOOSE k \in NODES:
                                           \A m \in NODES: k <= m]
    /\  nodeTS          = [n \in NODES |-> [version |-> 0, 
                                            tieBreaker |-> 
                                             CHOOSE k \in NODES: 
                                              \A m \in NODES: k <= m]]
    /\  nodeLastWriteTS = [n \in NODES |-> [version |-> 0, 
                                             tieBreaker |-> 
                                              CHOOSE k \in NODES: 
                                               \A m \in NODES: k <= m]]
-------------------------------------------------------------------------------------
\* A buffer maintaining all network messages. Messages are only appended to this variable (not 
\* removed once delivered) intentionally to check protocols tolerance in dublicates and reorderings 
send(m) == msgs' = msgs \union {m}

\* Check if all acknowledgments for a write have been received                                                  
receivedAllAcks(n) == nodeRcvedAcks[n] = NODES \ {n}
        
equalTS(v1,tb1,v2,tb2) ==  \* Timestamp equality
    /\ v1 = v2
    /\ tb1 = tb2

greaterTS(v1,tb1,v2,tb2) == \* Timestamp comparison
    \/ v1 > v2
    \/ /\   v1 = v2
       /\  tb1 > tb2
       
isAlive(n) == n \in aliveNodes

nodeFailure(n) == \* Emulate a node failure
\*    Make sure that there are atleast 3 alive nodes before killing a node
    /\ \E k,m \in aliveNodes: /\ k /= n 
                              /\ m /= n
                              /\ m /= k
    /\ aliveNodes' = aliveNodes \ {n}
    /\ UNCHANGED <<msgs, nodeState, nodeTS, nodeLastWriter, 
                   nodeLastWriteTS, nodeRcvedAcks>>
-------------------------------------------------------------------------------------
HRead(n) ==  \* Execute a read
    /\ nodeState[n] = "valid"
    /\ UNCHANGED <<msgs, nodeTS, nodeState, nodeLastWriter, 
                   aliveNodes, nodeLastWriteTS, nodeRcvedAcks>>
             
HWrite(n) == \* Execute a write
    /\  nodeState[n]      \in {"valid", "invalid"}
    /\  nodeTS[n].version < MAX_VERSION
    /\  nodeRcvedAcks'    = [nodeRcvedAcks   EXCEPT ![n] = {}]
    /\  nodeLastWriter'   = [nodeLastWriter  EXCEPT ![n] = n]
    /\  nodeState'        = [nodeState       EXCEPT ![n] = "write"]
    /\  nodeTS'           = [nodeTS          EXCEPT ![n].version    = 
                                                        nodeTS[n].version + 1,
                                                    ![n].tieBreaker = n]
    /\  nodeLastWriteTS'  = [nodeLastWriteTS EXCEPT ![n].version = 
                                                        nodeTS[n].version + 1,
                                                    ![n].tieBreaker = n]
    /\  send([type        |-> "INV",
              sender      |-> n,
              version     |-> nodeTS[n].version + 1, 
              tieBreaker  |-> n])              
    /\  UNCHANGED <<aliveNodes>>
                
HReplayWrite(n) == \* Execute a write-replay
    /\  nodeState[n] = "invalid"
    /\  ~isAlive(nodeLastWriter[n])
    /\  nodeLastWriter'  = [nodeLastWriter   EXCEPT ![n] = n]
    /\  nodeState'       = [nodeState        EXCEPT ![n] = "replay"]
    /\  nodeRcvedAcks'   = [nodeRcvedAcks    EXCEPT ![n] = {}]
    /\  nodeLastWriteTS' = [nodeLastWriteTS  EXCEPT ![n] = nodeTS[n]]
    /\  send([type       |-> "INV",
              sender     |-> n,
              version    |-> nodeTS[n].version, 
              tieBreaker |-> nodeTS[n].tieBreaker])
    /\  UNCHANGED <<nodeTS, aliveNodes>>
-------------------------------------------------------------------------------------     
HRcvAck(n) ==   \* Process a received acknowledment
    \E m \in msgs: 
        /\ m.type = "ACK"
        /\ m.sender /= n
        /\ m.sender \notin nodeRcvedAcks[n]
        /\ equalTS(m.version,
                   m.tieBreaker,
                   nodeLastWriteTS[n].version, 
                   nodeLastWriteTS[n].tieBreaker)
        /\ nodeState[n] \in {"write", "invalid_write", "replay"}
        /\ nodeRcvedAcks' = [nodeRcvedAcks EXCEPT ![n] = 
                                              nodeRcvedAcks[n] \union {m.sender}]
        /\ UNCHANGED <<msgs, nodeLastWriter, nodeLastWriteTS, 
                       aliveNodes, nodeTS, nodeState>>

HSendVals(n) == \* Send validations once received acknowledments from all alive nodes
    /\ nodeState[n] \in {"write", "replay"}
    /\ receivedAllAcks(n)
    /\ nodeState'         = [nodeState EXCEPT![n] = "valid"]
    /\ send([type        |-> "VAL", 
             version     |-> nodeTS[n].version, 
             tieBreaker  |-> nodeTS[n].tieBreaker])
    /\ UNCHANGED <<nodeTS, nodeLastWriter, nodeLastWriteTS,
                   aliveNodes, nodeRcvedAcks>>

HCoordinatorActions(n) ==   \* Actions of a read/write coordinator 
    \/ HRead(n)          
    \/ HReplayWrite(n) 
    \/ HWrite(n)         
    \/ HRcvAck(n)
    \/ HSendVals(n) 
-------------------------------------------------------------------------------------               
HRcvInv(n) ==  \* Process a received invalidation
    \E m \in msgs: 
        /\ m.type = "INV"
        /\ m.sender /= n
        \* always acknowledge a received invalidation (irrelevant to the timestamp)
        /\ send([type       |-> "ACK",
                 sender     |-> n,   
                 version    |-> m.version,
                 tieBreaker |-> m.tieBreaker])
        /\ \/ /\ greaterTS(m.version,
                            m.tieBreaker,
                            nodeTS[n].version, 
                            nodeTS[n].tieBreaker)
              /\ nodeLastWriter' = [nodeLastWriter EXCEPT ![n] = m.sender]
              /\ nodeTS' = [nodeTS EXCEPT ![n].version    = m.version,
                                          ![n].tieBreaker = m.tieBreaker]
              /\ \/ /\ nodeState[n] \in {"valid", "invalid", "replay"}
                    /\ nodeState' = [nodeState EXCEPT ![n] = "invalid"]
                 \/ /\ nodeState[n] \in {"write", "invalid_write"} 
                    /\ nodeState' = [nodeState EXCEPT ![n] = "invalid_write"] 
           \/ /\ ~greaterTS(m.version,
                            m.tieBreaker,
                            nodeTS[n].version, 
                            nodeTS[n].tieBreaker)
              /\ UNCHANGED <<nodeState, nodeTS, nodeLastWriter>>
        /\ UNCHANGED <<nodeLastWriteTS, aliveNodes, nodeRcvedAcks>>
            
HRcvVal(n) ==   \* Process a received validation
    \E m \in msgs: 
        /\ nodeState[n] /= "valid"
        /\ m.type = "VAL"
        /\ equalTS(m.version,
                   m.tieBreaker,
                   nodeTS[n].version, 
                   nodeTS[n].tieBreaker)
        /\ nodeState' = [nodeState EXCEPT ![n] = "valid"]
        /\ UNCHANGED <<msgs, nodeTS, nodeLastWriter, nodeLastWriteTS,
                       aliveNodes, nodeRcvedAcks>>
                       
HFollowerActions(n) ==  \* Actions of a write follower
    \/ HRcvInv(n)
    \/ HRcvVal(n) 
-------------------------------------------------------------------------------------                       
HNext == \* Modeling Hermes protocol (Coordinator and Follower actions while emulating failures)
    \E n \in aliveNodes:       
            \/ HFollowerActions(n)
            \/ HCoordinatorActions(n)
            \/ nodeFailure(n) \* emulate node failures
=============================================================================
