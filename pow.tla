-------------------------------- MODULE POW --------------------------------

EXTENDS Integers

CONSTANT nodes
VARIABLES chain, blcks, last_block_id, status, status_changer

Block == [miner_id: nodes \union {"first"}, block_id: 0..3, prev_block_id: -1..3]

POWTypeOK ==
    /\ blcks \subseteq Block
    /\ chain \in [nodes -> SUBSET Block]
    /\ last_block_id \in [nodes -> 0..3]
    /\ status \in [nodes -> {"mined", "miner"}]
    /\ status_changer \in [nodes -> {0, 1}]

----------------------------------------------------------------------------

POWInit ==
    /\ blcks = {[miner_id |-> "first", block_id |-> 0, prev_block_id |-> -1]}
    /\ chain = [n \in nodes |-> {[miner_id |-> "first", block_id |-> 0, prev_block_id |-> -1]}]
    /\ last_block_id = [n \in nodes |-> 0]
    /\ status = [ n \in nodes |-> "miner"]
    /\ status_changer = [n \in nodes |-> 0]

----------------------------------------------------------------------------

MineABlock(n) ==
    /\ status[n] = "miner"
    /\ chain' = [chain EXCEPT ![n] = chain[n] \union {[miner_id |-> n, block_id |-> last_block_id[n] + 1,
                                                                     prev_block_id |-> last_block_id[n]]}]
    /\ blcks' = blcks \union {[miner_id |-> n, block_id |-> last_block_id[n] + 1, prev_block_id |-> last_block_id[n]]}
    /\ last_block_id' = [last_block_id EXCEPT ![n] = last_block_id[n] + 1]
    /\ status' = [status EXCEPT ![n] = "mined"]
    /\ status_changer' = [status_changer EXCEPT ![n] = 1]


CommitABlock(n, r) ==
    /\ status[n] = "mined"
    /\ last_block_id[r] = last_block_id[n] - 1
    /\ [miner_id |-> n, block_id |-> last_block_id[n], prev_block_id |-> last_block_id[n] - 1] \in blcks
    /\ chain' = chain
    /\ chain[r]' = chain[r] \union {[miner_id |-> n, block_id |-> last_block_id[n], prev_block_id |-> last_block_id[r]]}
    /\ last_block_id' = [last_block_id EXCEPT ![r] = last_block_id[n]]
    /\ status_changer' = [status_changer EXCEPT ![r] = 1]
    /\ UNCHANGED <<blcks, status>>
   
   
IgnoreABlock(n, r) ==
    /\ status[n] = "mined"
    /\ [miner_id |-> n, block_id |-> last_block_id[n], prev_block_id |-> last_block_id[n] - 1] \in blcks
    /\ status_changer' = [status_changer EXCEPT ![r] = 1]
    /\ UNCHANGED <<chain, blcks, last_block_id, status>>
   
ChangeStatus(n) ==
    /\ status_changer = [r \in nodes |-> 1]
    /\ status' = [status EXCEPT ![n] = "miner"]
    /\ status_changer' = [r \in nodes |-> 0]
    /\ UNCHANGED <<blcks, chain, last_block_id>>

-----------------------------------------------------------------------------

POWNext == (\E n\in nodes:
    \/ MineABlock(n) \/ ChangeStatus(n)
    \/ (\A r \in nodes: CommitABlock(n, r) \/ IgnoreABlock(n, r)))
   
-----------------------------------------------------------------------------

POWSpec == POWInit /\ [][POWNext]_<<chain, blcks, last_block_id, status>>
  (*************************************************************************)
  (* The complete spec of the Proof-of-work Commit protocol.               *)
  (*************************************************************************)

THEOREM POWSpec => []POWTypeOK
  (*************************************************************************)
  (* This theorem asserts that the type-correctness predicate POWTypeOK is *)
  (* an invariant of the specification.                                    *)
  (*************************************************************************)