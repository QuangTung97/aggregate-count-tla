------ MODULE AggCount ----
EXTENDS TLC, Integers, FiniteSets

CONSTANTS Dataset, Storage, nil

VARIABLES replicas, pending_counters

vars == <<replicas, pending_counters>>

min_repl_id == 21
max_repl_id == 25

ReplicaID == min_repl_id..max_repl_id

Status == {"pending", "written"}

ReplicaInfo == [ds: Dataset, status: Status, storage: Storage, agg: BOOLEAN]

Replica == [ReplicaID -> ReplicaInfo \union {nil}]

PendingKey == Dataset \X Storage

PendingInfo == [count: 0..100, need_update: BOOLEAN, version: 0..500]

TypeOK ==
    /\ replicas \in Replica
    /\ pending_counters \in [PendingKey -> PendingInfo]


initCounter == [count |-> 0, need_update |-> FALSE, version |-> 0]

Init ==
    /\ replicas = [id \in ReplicaID |-> nil]
    /\ pending_counters = [k \in PendingKey |-> initCounter]


addReplicaImpl(id, ds, st) ==
    LET
        new_repl == [ds |-> ds, status |-> "pending", storage |-> st, agg |-> FALSE]
        key == <<ds, st>>
        old_counter == pending_counters[key]
        new_counter == [old_counter EXCEPT !.need_update = TRUE, !.version = @ + 1]
    IN
        /\ replicas' = [replicas EXCEPT ![id] = new_repl]
        /\ pending_counters' = [pending_counters EXCEPT ![key] = new_counter]
    

AddReplica(id, ds, st) ==
    /\ replicas[id] = nil
    /\ addReplicaImpl(id, ds, st)


updateCounterAfterWritten(r) ==
    LET
        k == <<r.ds, r.storage>>
    IN
        pending_counters' = [
            pending_counters EXCEPT ![k] = [
                @ EXCEPT !.need_update = TRUE, !.version = @ + 1
            ]
        ]


UpdateToWritten(id) ==
    /\ replicas[id] # nil
    /\ replicas' = [replicas EXCEPT ![id].status = "written"]
    /\ updateCounterAfterWritten(replicas[id])


replicaHasKey(id, k) ==
    /\ replicas[id] # nil
    /\ replicas[id].ds = k[1]
    /\ replicas[id].storage = k[2]


getPendingReplicas(k) ==
    LET
        selectCond(id) ==
            /\ replicaHasKey(id, k) \* TODO missing cond
    IN
        {id \in ReplicaID: selectCond(id)}

setAggTrue(update_ids) ==
    LET
        new_fn(id) ==
            IF id \in update_ids
                THEN [replicas[id] EXCEPT !.agg = TRUE]
                ELSE replicas[id] \* unchanged
    IN
        replicas' = [id \in ReplicaID |-> new_fn(id)]

doUpdatePendingCounter(k) ==
    LET
        pending_repls == getPendingReplicas(k)
        num == Cardinality(pending_repls)

        old_counter == pending_counters[k]
        new_counter == [old_counter EXCEPT !.count = num, !.need_update = FALSE]
    IN
        /\ pending_counters' = [pending_counters EXCEPT ![k] = new_counter]
        /\ setAggTrue(pending_repls)


UpdatePendingCounter(k) ==
    /\ pending_counters[k].need_update = TRUE
    /\ doUpdatePendingCounter(k)


TerminateCond ==
    /\ \A id \in ReplicaID:
        /\ replicas[id] # nil
        /\ replicas[id].agg = TRUE
    /\ \A key \in PendingKey: pending_counters[key].need_update = FALSE

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ \E id \in ReplicaID, ds \in Dataset, st \in Storage:
        AddReplica(id, ds, st)
    \/ \E id \in ReplicaID:
        UpdateToWritten(id)
    \/ \E k \in PendingKey:
        UpdatePendingCounter(k)
    \/ Terminated


allPendingReplicas(k) ==
    LET
        checkCond(id) ==
            /\ replicaHasKey(id, k)
            /\ replicas[id].status = "pending"
        S == {id \in ReplicaID: checkCond(id)}
    IN
        Cardinality(S)

numPendingByCounter(k) ==
    LET
        checkCond(id) ==
            /\ replicaHasKey(id, k)
            /\ replicas[id].agg = FALSE
            /\ replicas[id].status = "pending"
        S == {id \in ReplicaID: checkCond(id)}
    IN
        Cardinality(S) + pending_counters[k].count

Inv ==
    /\ \A k \in PendingKey:
        allPendingReplicas(k) = numPendingByCounter(k)


Sym == Permutations(Dataset) \union Permutations(Storage)

====