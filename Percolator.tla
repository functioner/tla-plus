----------------------------- MODULE Percolator -----------------------------
EXTENDS Naturals, Integers, FiniteSets, Bags, Sequences, TLC

\* domain of bigtable keys
Keys == {"Bob", "Joe", "Jay"}

\* domain of Percolator transactions
Txns == {"txn-1", "txn-2", "txn-3"}

\* predefine row txns
rowtxns == [id \in 1..5 |-> {}]

\* predefine txns
rowtxns_of == [txn \in Txns |-> {}]

\* reserved NULL
Nil == "NULL"

\* rowtxn \in [key->, val->]

\* get start_ts
\* choose&prewrite primary
\* prewrite secondaries
\* get commit_ts
\* commit primary
\* write currrent secondary
\* erase current secondary

\* bigtable
VARIABLES data_of, locks_of, writes_of

\* TSO
VARIABLES next_ts

\* txns essentials
VARIABLES prim_of, snds_of, start_ts_of, commit_ts_of

\* txns auxiliaries
VARIABLES txn_state_of, cur_snd_of, rmn_snds_of

vars == <<data_of, locks_of, writes_of, next_ts,
          prim_of, snds_of, start_ts_of, commit_ts_of,
          txn_state_of, cur_snd_of, rmn_snds_of>>

\* inits

InitBigtable ==
    /\ data_of = [key \in Keys |-> {}]
    /\ locks_of = [key \in Keys |-> {}]
    /\ writes_of = [key \in Keys |-> {}]

InitTSO ==
    /\ next_ts = 0

InitTxns ==
    /\ prim_of = [txn \in Txns |-> Nil]
    /\ snds_of = [txn \in Txns |-> Nil]
    /\ start_ts_of = [txn \in Txns |-> Nil]
    /\ commit_ts_of = [txn \in Txns |-> Nil]
    /\ cur_snd_of = [txn \in Txns |-> Nil]
    /\ rmn_snds_of = [txn \in Txns |-> Nil]
    /\ txn_state_of = [txn \in Txns |-> "init"]

Init ==
    /\ InitBigtable
    /\ InitTSO
    /\ InitTxns

\* auxiliaries

SetState(txn, state) ==
    /\ txn_state_of' = [txn_state_of EXCEPT ![txn] = state] 

Abort(txn) ==
    /\ SetState(txn, "aborted")

SetTS(ts_of, txn) ==
    /\ next_ts' = next_ts + 1
    /\ ts_of' = [ts_of EXCEPT ![txn] = next_ts]

CheckState(txn, state) ==
    /\ txn_state_of[txn] = state

PrewriteRowtxn(rowtxn, txn) ==
    /\ \A write \in writes_of[rowtxn.key]: write.ts < start_ts_of[txn]
    /\ locks_of[rowtxn.key] = {}
    /\ data_of' = [data_of EXCEPT ![rowtxn.key] = @ \union [ts |-> start_ts_of[txn], val |-> rowtxn.val]]
    /\ locks_of' = [locks_of EXCEPT ![rowtxn.key] = @ \union [ts |-> start_ts_of[txn], prim |-> rowtxn.key]]

ChooseCurrentSecondaries(txn) ==
    /\ LET rowtxn == CHOOSE rowtxn \in rmn_snds_of[txn]: TRUE
       IN /\ cur_snd_of' = [cur_snd_of EXCEPT ![txn] = rowtxn]
          /\ rmn_snds_of' = [rmn_snds_of EXCEPT ![txn] = @ \ {rowtxn}]

\* phases

GetStartTS(txn) ==
    /\ CheckState(txn, "init")
    /\ SetTS(start_ts_of, txn)
    /\ SetState(txn, "got start_ts")
    /\ UNCHANGED <<data_of, locks_of, writes_of, prim_of, snds_of, commit_ts_of, cur_snd_of, rmn_snds_of>>

ChoosePrimary(txn) ==
    /\ CheckState(txn, "got start_ts")
    /\ LET rowtxn == CHOOSE rowtxn \in rowtxns_of[txn]: TRUE
       IN /\ prim_of' = [prim_of EXCEPT ![txn] = rowtxn]
          /\ snds_of' = [snds_of EXCEPT ![txn] = rowtxns_of[txn] \ {rowtxn}]
    /\ SetState(txn, "choosed primary")
    /\ UNCHANGED <<data_of, locks_of, writes_of, next_ts, start_ts_of, commit_ts_of, cur_snd_of, rmn_snds_of>>

PrewritePrimary(txn) ==
    /\ CheckState(txn, "choosed primary")
    /\ PrewriteRowtxn(prim_of[txn], txn)
    /\ SetState(txn, "prewritten primary")
    /\ UNCHANGED <<writes_of, next_ts, prim_of, snds_of, start_ts_of, commit_ts_of, cur_snd_of, rmn_snds_of>>

PrewriteSecondaries(txn) ==
    /\ CheckState(txn, "prewritten primary")
    /\ IF cur_snd_of[txn] = Nil
       THEN IF rmn_snds_of[txn] = {}
            THEN /\ SetState(txn, "prewritten secondaries")
                 /\ snds_of' = [snds_of EXCEPT ![txn] = rowtxns_of[txn] \ {prim_of[txn]}]
                 /\ UNCHANGED <<data_of, locks_of, writes_of, next_ts, prim_of, start_ts_of, commit_ts_of, cur_snd_of, rmn_snds_of>>
            ELSE /\ ChooseCurrentSecondaries(txn)
                 /\ UNCHANGED <<data_of, locks_of, writes_of, next_ts, prim_of, snds_of, start_ts_of, commit_ts_of, txn_state_of>>
       ELSE /\ PrewriteRowtxn(cur_snd_of[txn], txn)
            /\ cur_snd_of' = [cur_snd_of EXCEPT ![txn] = Nil]
            /\ UNCHANGED <<writes_of, next_ts, prim_of, snds_of, start_ts_of, commit_ts_of, txn_state_of, rmn_snds_of>>

GetCommitTS(txn) ==
    /\ CheckState(txn, "prewritten secondaries")
    /\ SetTS(commit_ts_of, txn)
    /\ SetState(txn, "got commit_ts")
    /\ UNCHANGED <<data_of, locks_of, writes_of, prim_of, snds_of, start_ts_of, cur_snd_of, rmn_snds_of>>

CommitPrimary(txn) ==
    /\ CheckState(txn, "got commit_ts")
    /\ data_of' = [data_of EXCEPT ![prim_of[txn]] = @ \union {[ts |-> start_ts_of[txn], val |-> prim_of[txn].val]}]
    /\ locks_of' = [locks_of EXCEPT ![locks_of[txn]] = @ \union {[ts |-> start_ts_of[txn], prim |-> prim_of[txn].key]}]
    /\ SetState(txn, "committed primary")
    /\ UNCHANGED <<writes_of, next_ts, prim_of, snds_of, start_ts_of, commit_ts_of, cur_snd_of, rmn_snds_of>>

WriteCurrentSecondary(txn) ==
    /\ CheckState(txn, "committed primary")
    /\ cur_snd_of[txn] = Nil
    /\ IF rmn_snds_of[txn] = {}
       THEN /\ SetState(txn, "done")
            /\ UNCHANGED <<data_of, locks_of, writes_of, next_ts, prim_of, snds_of, start_ts_of, commit_ts_of, cur_snd_of, rmn_snds_of>>
       ELSE /\ ChooseCurrentSecondaries(txn)
            /\ writes_of' = [writes_of EXCEPT ![txn] = @ \union {[ts |-> commit_ts_of[txn], start_ts |-> start_ts_of[txn]]}]
            /\ UNCHANGED <<data_of, locks_of, next_ts, start_ts_of, commit_ts_of, cur_snd_of, rmn_snds_of>>

EraseCurrentSecondary(txn) ==
    /\ CheckState(txn, "committed primary")
    /\ cur_snd_of[txn] # Nil
    /\ locks_of' = [locks_of EXCEPT ![txn] = @ \ {[ts |-> start_ts_of[txn], prim |-> prim_of[txn].key]}]
    /\ cur_snd_of' = [cur_snd_of EXCEPT ![txn] = Nil]
    /\ UNCHANGED <<data_of, writes_of, next_ts, prim_of, snds_of, start_ts_of, commit_ts_of, txn_state_of, rmn_snds_of>>

Get(key) ==
    /\ locks_of[key] # {}
    /\ locks_of' = [locks_of EXCEPT ![key] = {}]
    /\ writes_of' = [writes_of EXCEPT ![key] = @ \union
                        {[ts |-> next_ts, start_ts |-> lock.ts]:
                            lock \in {lock \in locks_of[key]:
                                 \E write \in writes_of[lock.prim]:
                                    write.start_ts = lock.ts}}]
    /\ UNCHANGED <<data_of, next_ts, prim_of, snds_of, start_ts_of, commit_ts_of, txn_state_of, cur_snd_of, rmn_snds_of>>

Next ==
    \/ \E txn \in Txns:
       \/ GetStartTS(txn)
       \/ ChoosePrimary(txn)
       \/ PrewritePrimary(txn)
       \/ PrewriteSecondaries(txn)
       \/ GetCommitTS(txn)
       \/ CommitPrimary(txn)
       \/ WriteCurrentSecondary(txn)
       \/ EraseCurrentSecondary(txn)
       \/ /\ ~CheckState(txn, "aborted")
          /\ Abort(txn)
          /\ UNCHANGED <<data_of, locks_of, writes_of, next_ts, prim_of, snds_of, start_ts_of, commit_ts_of, cur_snd_of, rmn_snds_of>>
    \/ \E key \in Keys:
       Get(key)

Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Last modified Tue Jan 02 03:25:56 CST 2018 by functioner
\* Created Fri Dec 22 10:44:36 CST 2017 by functioner
