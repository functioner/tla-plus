----------------------------- MODULE Percolator -----------------------------
EXTENDS Naturals, TLAPS

(*-------------------------------------------------------------------------*)
\* constants

\* Txn: domain of txns
\* Rowtxn: domain of rowtxns
\* Key: domain of keys
\* Val: domain of values
\* TxnState: domain of txn states
\* RowtxnState: domain of rowtxn states
CONSTANTS Key, Val

CONSTANTS Rowtxn, RowtxnState, rowtxnKey, rowtxnVal

CONSTANTS Txn, txnPrim, txnSnds, TxnState

CONSTANTS Query, QueryState, queryKey, queryAns

(*-------------------------------------------------------------------------*)
\* state axioms

\* rowtxn workflow:
\* primary: directly commit
\* secondaries: write first, then commit
AXIOM RowtxnStateAxiom ==
    /\ RowtxnState = {"init", "prewritten", "written", "committed"}

AXIOM RowtxnKeyAxiom ==
    /\ rowtxnKey \in [Rowtxn -> Key]

AXIOM RowtxnValAxiom ==
    /\ rowtxnVal \in [Rowtxn -> Val]

\* txn proposal workflow:
\* get start ts
\* prewrite primary
\* prewrite secondaries
\* get commit ts
\* commit primary && update godKV
\* for secondaries: write commit ts && erase lock
AXIOM TxnStateAxiom ==
    /\ TxnState = {"init", "pwting-prim", "pwting-snds", "committing-prim", "committing-snds"}

AXIOM TxnPrimAxiom ==
    /\ txnPrim \in [Txn -> Rowtxn]

AXIOM TxnSndsAxiom ==
    /\ txnSnds \in [Txn -> SUBSET Rowtxn]

\* query workflow:
\* get ts (and thus snapshot)
\* get value (and backoff/cleanup by the way)
AXIOM QueryStateAxiom ==
    /\ QueryState = {"init", "snapshot", "done"}

AXIOM QueryKeyAxiom ==
    /\ queryKey \in [Query -> Key]

AXIOM QueryAnsAxiom ==
    /\ queryAns \in [Query -> Val]

(*-------------------------------------------------------------------------*)
\* variables

\* rowtxn functions (Txn * Rowtxn -> )
VARIABLES txnRowtxnState

\* txn functions (Txn -> )
VARIABLES txnState, txnCommitTS, txnStartTS

\* query functions (Query -> )
VARIABLES queryState, queryTS

\* new data
VARIABLES newDataItem, newDataExist

\* bigtable functions (Key * Nat -> )
VARIABLES lockItem, dataItem, writeItem
VARIABLES lockExist, writeExist

\* TSO timestamp
VARIABLES tsoTS

\* godKV functions (Key -> ), (Query -> )
VARIABLES godMap, godAns, godKeyExist

vars == <<>>

(*-------------------------------------------------------------------------*)
\* type invariants

TxnRowtxnStateTypeInv ==
    /\ txnRowtxnState \in [Txn -> [Rowtxn -> RowtxnState]]

NewDataItemTypeInv ==
    /\ newDataItem \in [Txn -> [Key -> Val]]

NewDataExistTypeInv ==
    /\ newDataExist \in [Txn -> [Key -> BOOLEAN]]

RowtxnTypeInv ==
    /\ TxnRowtxnStateTypeInv
    /\ NewDataItemTypeInv
    /\ NewDataExistTypeInv

TxnStateTypeInv ==
    /\ txnState \in [Txn -> TxnState]

TxnCommitTSTypeInv ==
    /\ txnCommitTS \in [Txn -> Nat]

TxnStartTSTypeInv ==
    /\ txnStartTS \in [Txn -> Nat]

TxnTypeInv ==
    /\ TxnStateTypeInv
    /\ TxnCommitTSTypeInv
    /\ TxnStartTSTypeInv

QueryStateTypeInv ==
    /\ QueryState \in [Query -> QueryState]

QueryTSTypeInv ==
    /\ queryTS \in [Query -> Nat]

QueryTypeInv ==
    /\ QueryStateTypeInv
    /\ QueryTSTypeInv

DataTypeInv ==
    /\ dataItem \in [Key -> [Nat -> Val]]

LockItemTypeInv ==
    /\ lockItem \in [Key -> [Nat -> Txn]]

LockExistTypeInv ==
    /\ lockExist \in [Key -> [Nat -> BOOLEAN]]

LockTypeInv ==
    /\ LockItemTypeInv
    /\ LockExistTypeInv

WriteItemTypeInv ==
    /\ writeItem \in [Key -> [Nat -> Nat]]

WriteExistTypeInv ==
    /\ writeExist \in [Key -> [Nat -> BOOLEAN]]

WriteTypeInv ==
    /\ WriteItemTypeInv
    /\ WriteExistTypeInv

BigtableTypeInv ==
    /\ DataTypeInv
    /\ LockTypeInv
    /\ WriteTypeInv

TSOTypeInv ==
    /\ tsoTS \in Nat

GodMapTypeInv ==
    /\ godMap \in [Key -> Val]

GodAnsTypeInv ==
    /\ godAns \in [Query -> Val]

GodKeyExistTypeInv ==
    /\ godKeyExist \in [Key -> BOOLEAN]

GodTypeInv ==
    /\ GodMapTypeInv
    /\ GodAnsTypeInv
    /\ GodKeyExistTypeInv

TypeInv ==
    /\ RowtxnTypeInv
    /\ TxnTypeInv
    /\ QueryTypeInv
    /\ BigtableTypeInv
    /\ TSOTypeInv
    /\ GodTypeInv

(*-------------------------------------------------------------------------*)
\* init specs

InitRowtxn ==
    /\ txnRowtxnState = [txn \in Txn |-> [rowtxn \in Rowtxn |-> "init"]]

InitTxn ==
    /\ txnState = [txn \in Txn |-> "init"]
    /\ newDataExist = [txn \in Txn |-> [key \in Key |-> FALSE]]
    /\ TxnCommitTSTypeInv
    /\ TxnStartTSTypeInv
    /\ NewDataItemTypeInv

InitQuery ==
    /\ queryState = [query \in Query |-> "init"]
    /\ QueryTSTypeInv

InitBigtable ==
    /\ lockExist = [key \in Key |-> [ts \in Nat |-> FALSE]]
    /\ writeExist = [key \in Key |-> [ts \in Nat |-> FALSE]]
    /\ LockItemTypeInv
    /\ DataTypeInv
    /\ WriteItemTypeInv

InitTSO ==
    /\ tsoTS = 0

InitGod ==
    /\ godKeyExist = [key \in Key |-> FALSE]
    /\ GodMapTypeInv
    /\ GodAnsTypeInv

Init ==
    /\ InitRowtxn
    /\ InitTxn
    /\ InitQuery
    /\ InitBigtable
    /\ InitTSO
    /\ InitGod

(*-------------------------------------------------------------------------*)
\* txn auxiliary actions

GetTS(ts, idx) ==
    /\ ts' = [ts EXCEPT ![idx] = tsoTS]
    /\ tsoTS' = tsoTS + 1

canPrewrite(rowtxn, txn) ==
    /\ \A ts \in Nat:
        /\ ~lockExist[rowtxnKey[rowtxn]][ts]
        /\ writeExist[rowtxnKey[rowtxn]][ts] => (ts > txnStartTS[txn])

Assign(array2d, i, j, v) ==
    /\ array2d' = [array2d EXCEPT ![i] = [array2d[i] EXCEPT ![j] = v]]

WriteArray(item, exist, i, j, v) ==
    /\ Assign(item, i, j, v)
    /\ Assign(exist, i, j, TRUE)

RowtxnPrewrite(rowtxn, txn) ==
    /\ canPrewrite(rowtxn, txn)
    /\ WriteArray(newDataItem, newDataExist, txn, rowtxnKey[rowtxn], rowtxnVal[rowtxn])
    /\ WriteArray(lockItem, lockExist, rowtxnKey[rowtxn], txnStartTS[txn], txn)
    /\ Assign(dataItem, rowtxnKey[rowtxn], txnStartTS[txn], rowtxnVal[rowtxn])

TxnSndRowtxnPrewrite(rowtxn, txn) ==
    /\ txnRowtxnState[txn][rowtxn] = "init"
    /\ RowtxnPrewrite(rowtxn, txn)
    /\ Assign(txnRowtxnState, txn, rowtxn, "prewritten")

TxnChooseSndRowtxnPrewrite(txn) ==
    /\ \E rowtxn \in txnSnds[txn]:
        /\ TxnSndRowtxnPrewrite(rowtxn, txn)

TxnPrewroteAllSecondaries(txn) ==
    /\ \A rowtxn \in txnSnds[txn]:
        /\ txnRowtxnState[txn][rowtxn] = "prewritten"

TxnCommitPrimary(txn) ==
    /\ lockExist[rowtxnKey[txnPrim[txn]]][txnStartTS[txn]]
    /\ WriteArray(writeItem, writeExist, rowtxnKey[txnPrim[txn]], txnCommitTS[txn], txnStartTS[txn])
    /\ Assign(lockExist, rowtxnKey[txnPrim[txn]], txnStartTS[txn], FALSE)

TxnUpdataGod(txn) ==
    /\ godMap' = [key \in Key |-> IF newDataExist[txn][key] THEN newDataItem[txn][key] ELSE godMap[key]]
    /\ godKeyExist' = [key \in Key |-> godKeyExist[key] \/ newDataExist[txn][key]]

SecondaryWrite(rowtxn, txn) ==
    /\ WriteArray(writeItem, writeExist, rowtxnKey[rowtxn], txnCommitTS[txn], txnStartTS[txn])

SecondaryEraseLock(rowtxn, txn) ==
    /\ writeExist[rowtxnKey[rowtxn]][txnCommitTS[txn]]
    /\ Assign(lockExist, rowtxnKey[rowtxn], txnStartTS[txn], FALSE)

TxnCommitSecondary(rowtxn, txn) ==
    \/ SecondaryWrite(rowtxn, txn)
    \/ SecondaryEraseLock(rowtxn, txn)

(*-------------------------------------------------------------------------*)
\* txn actions

TxnGetStartTS(txn) ==
    /\ txnState[txn] = "init"
    /\ GetTS(txnStartTS, txn)
    /\ txnState' = [txnState EXCEPT ![txn] = "pwting-prim"]
    /\ UNCHANGED <<>>

TxnPrewritePrimary(txn) ==
    /\ txnState[txn] = "pwting-prim"
    /\ RowtxnPrewrite(txnPrim[txn], txn)
    /\ txnState' = [txnState EXCEPT ![txn] = "pwting-snds"]
    /\ UNCHANGED <<>>

TxnPrewriteSecondaries(txn) ==
    /\ txnState[txn] = "pwting-snds"
    /\ TxnChooseSndRowtxnPrewrite(txn)
    /\ UNCHANGED <<>>

TxnGetCommitTS(txn) ==
    /\ txnState[txn] = "pwting-snds"
    /\ TxnPrewroteAllSecondaries(txn)
    /\ GetTS(txnCommitTS, txn)
    /\ txnState' = [txnState EXCEPT ![txn] = "committing-prim"]
    /\ UNCHANGED <<>>

TxnCommitPrimaryAndUpdataGod(txn) ==
    /\ txnState[txn] = "committing-prim"
    /\ TxnCommitPrimary(txn)
    /\ TxnUpdataGod(txn)
    /\ txnState' = [txnState EXCEPT ![txn] = "committing-snds"]
    /\ UNCHANGED <<>>

TxnCommitSecondaries(txn) ==
    /\ \E rowtxn \in txnSnds[txn]:
        /\ TxnCommitSecondary(rowtxn, txn)

\* txn proposal workflow:
\* get start ts
\* prewrite primary
\* prewrite secondaries
\* get commit ts
\* commit primary && update godKV
\* for secondaries: write commit ts && erase lock

TxnProceed(txn) ==
    \/ TxnGetStartTS(txn)
    \/ TxnPrewritePrimary(txn)
    \/ TxnPrewriteSecondaries(txn)
    \/ TxnGetCommitTS(txn)
    \/ TxnCommitPrimaryAndUpdataGod(txn)
    \/ TxnCommitSecondaries(txn)

TxnWork ==
    /\ \E txn \in Txn:
        /\ TxnProceed(txn)

(*-------------------------------------------------------------------------*)
\* query actions

TakeSnapshot(query) ==
    /\ queryState[query] = "init"
    /\ godKeyExist[queryKey[query]]
    /\ GetTS(queryTS, query)
    /\ queryState' = [queryState EXCEPT ![query] = "snapshot"]

CommittedPrimary(txn) ==
    /\ writeExist[rowtxnKey[txnPrim[txn]]][txnCommitTS[txn]]

BackoffRowtxn(txn, key) ==
    /\ WriteArray(writeItem, writeExist, key, txnCommitTS[txn], txnStartTS[txn])

CleanupLock(query, ts) ==
    /\ Assign(lockExist, queryKey[query], ts, FALSE)
    /\ CommittedPrimary(lockItem[queryKey[query]][ts]) =>
       BackoffRowtxn(lockItem[queryKey[query]][ts], queryKey[query])

CheckLock(query, ts) ==
    /\ lockExist[queryKey[query]][ts] => CleanupLock(query, ts)

CleanupLocksTS(query) ==
    /\ \A ts \in Nat:
        /\ ts < queryTS[query] => CheckLock(query, ts)

LatestWriteCorrect(query, ts) ==
    /\ dataItem[queryKey[query]][ts] = queryAns[query]

LatestWriteSuffices(query, latestTS, ts) ==
    /\ ts < queryTS[query] =>
       /\ ts = latestTS
       /\ LatestWriteCorrect(query, writeItem[queryKey[query]][latestTS])

CheckLatestWrite(query, latestTS) ==
    /\ \A ts \in Nat:
        /\ LatestWriteSuffices(query, latestTS, ts)

QueryCheckLatestWrite(query, latestTS) ==
    /\ latestTS < queryTS[query] /\ writeExist[queryKey[query]][latestTS] =>
       CheckLatestWrite(query, latestTS)

QueryCheckWriteAns(query) ==
    /\ \A latestTS \in Nat:
         /\ QueryCheckLatestWrite(query, latestTS)

QueryGetAns(query) ==
    /\ CleanupLocksTS(query)
    /\ QueryCheckWriteAns(query)

QueryTxn(query) ==
    /\ queryState[query] = "snapshot"
    /\ QueryGetAns(query)
    /\ queryState' = [queryState EXCEPT ![query] = "done"]

ProposeQuery(query) ==
    \/ TakeSnapshot(query)
    \/ QueryTxn(query)

QueryWork ==
    /\ \E query \in Query:
        /\ ProposeQuery(query)

(*-------------------------------------------------------------------------*)
\* the temporal logic specs

Next ==
    \/ TxnWork
    \/ QueryWork

Spec == Init /\ [][Next]_vars

(*-------------------------------------------------------------------------*)
\* Correctness

QueryCorrect(query) ==
    /\ (queryState[query] = "done") => (queryAns[query] = godAns[query])

SnapshotIsolation ==
    /\ \A query \in Query:
        /\ QueryCorrect(query)

Correctness ==
    /\ []TypeInv
    /\ []SnapshotIsolation

(*-------------------------------------------------------------------------*)
\* verifications

THEOREM Spec => Correctness

=============================================================================
\* Modification History
\* Last modified Fri Jan 05 02:12:09 CST 2018 by functioner
\* Created Fri Dec 22 10:44:36 CST 2017 by functioner
