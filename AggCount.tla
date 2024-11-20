------ MODULE AggCount ----
EXTENDS TLC, Integers, FiniteSets

CONSTANTS Dataset, Storage, nil

VARIABLES replicas, pending_counters

vars == <<replicas, pending_counters>>

min_repl_id == 21
max_repl_id == 25

ReplicaID == min_repl_id..max_repl_id

Status == {"pending", "written"}

AggStatus == {"need_include", "no_action", "need_remove"}

ReplicaInfo == [ds: Dataset, status: Status, storage: Storage, agg: AggStatus]

Replica == [ReplicaID -> ReplicaInfo \union {nil}]

PendingKey == Dataset \X Storage

PendingInfo == [count: 0..100, need_update: BOOLEAN]

TypeOK ==
    /\ replicas \in Replica
    /\ pending_counters \in [PendingKey -> PendingInfo]


initCounter == [count |-> 0, need_update |-> FALSE]

Init ==
    /\ replicas = [id \in ReplicaID |-> nil]
    /\ pending_counters = [k \in PendingKey |-> initCounter]


addPendingReplicaImpl(id, ds, st) ==
    LET
        new_repl == [
            ds |-> ds, status |-> "pending",
            storage |-> st, agg |-> "need_include"]
        key == <<ds, st>>
    IN
        /\ replicas' = [replicas EXCEPT ![id] = new_repl]
        /\ pending_counters' = [pending_counters EXCEPT ![key].need_update = TRUE]
    

AddPendingReplica(id, ds, st) ==
    /\ replicas[id] = nil
    /\ addPendingReplicaImpl(id, ds, st)


addWrittenReplicaImpl(id, ds, st) ==
    LET
        new_repl == [
            ds |-> ds, status |-> "written",
            storage |-> st, agg |-> "no_action"]
        key == <<ds, st>>
    IN
        /\ replicas' = [replicas EXCEPT ![id] = new_repl]
        /\ pending_counters' = [pending_counters EXCEPT ![key].need_update = TRUE]


AddWrittenReplica(id, ds, st) ==
    /\ replicas[id] = nil
    /\ addWrittenReplicaImpl(id, ds, st)


updateCounterAfterWritten(r) ==
    LET
        k == <<r.ds, r.storage>>
    IN
        pending_counters' = [pending_counters EXCEPT ![k].need_update = TRUE]


computeAggStatusForWritten(old_val) ==
    IF old_val = "no_action"
        THEN "need_remove"
        ELSE "no_action"


doUpdateReplicaToWritten(id) ==
    LET
        old_repl == replicas[id]

        need_remove_cond ==
            \/ /\ old_repl.status = "pending"
               /\ old_repl.agg = "no_action"
            \/ /\ old_repl.status = "written"
               /\ old_repl.agg = "need_remove"

        new_agg ==
            IF need_remove_cond
                THEN "need_remove"
                ELSE "no_action"

        new_repl == [old_repl EXCEPT !.status = "written", !.agg = new_agg]
    IN
        replicas' = [replicas EXCEPT ![id] = new_repl]


UpdateToWritten(id) ==
    /\ replicas[id] # nil
    /\ replicas[id].status # "written"
    /\ doUpdateReplicaToWritten(id)
    /\ updateCounterAfterWritten(replicas[id])


replicaHasKey(id, k) ==
    /\ replicas[id] # nil
    /\ replicas[id].ds = k[1]
    /\ replicas[id].storage = k[2]


getPendingReplicas(k) ==
    LET
        selectCond(id) ==
            /\ replicaHasKey(id, k)
            /\ replicas[id].status = "pending"
    IN
        {id \in ReplicaID: selectCond(id)}

setAggToNoAction(k) ==
    LET
        new_fn(id) ==
            IF replicaHasKey(id, k)
                THEN [replicas[id] EXCEPT !.agg = "no_action"]
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
        /\ setAggToNoAction(k)


UpdatePendingCounter(k) ==
    /\ pending_counters[k].need_update = TRUE
    /\ doUpdatePendingCounter(k)


TerminateCond ==
    /\ \A id \in ReplicaID:
        /\ replicas[id] # nil
        /\ replicas[id].agg = "no_action"
    /\ \A key \in PendingKey: pending_counters[key].need_update = FALSE

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ \E id \in ReplicaID, ds \in Dataset, st \in Storage:
        \/ AddPendingReplica(id, ds, st)
        \/ AddWrittenReplica(id, ds, st)
    \/ \E id \in ReplicaID:
        UpdateToWritten(id)
    \/ \E k \in PendingKey:
        UpdatePendingCounter(k)
    \/ Terminated


Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)


AlwaysTerminate == <> TerminateCond


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
        isPending(id) ==
            /\ replicaHasKey(id, k)
            /\ replicas[id].agg = "need_include"

        isNonPending(id) ==
            /\ replicaHasKey(id, k)
            /\ replicas[id].agg = "need_remove"

        S1 == {id \in ReplicaID: isPending(id)}
        S2 == {id \in ReplicaID: isNonPending(id)}
    IN
        Cardinality(S1) + pending_counters[k].count - Cardinality(S2)

Inv ==
    /\ \A k \in PendingKey:
        allPendingReplicas(k) = numPendingByCounter(k)


Sym == Permutations(Dataset) \union Permutations(Storage)

====