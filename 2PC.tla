-------------------------------- MODULE 2PC --------------------------------
EXTENDS TLAPS

CONSTANTS RM, RMState, TMState, Msgs

VARIABLES rmState, tmState, tmPrepared, msgs

vars == <<rmState, tmState, tmPrepared, msgs>>

AXIOM RMStateAxiom ==
    /\ RMState = {"working", "prepared", "committed", "aborted"}

AXIOM TMStateAxiom ==
    /\ TMState = {"init", "committed", "aborted"}

AXIOM MsgsAxiom ==
    /\ Msgs = [type: {"prepared"}, rm: RM] \union [type: {"commit", "abort"}]

RMStateTypeInvariant ==
    /\ rmState \in [RM -> RMState]

TMStateTypeInvariant ==
    /\ tmState \in TMState

TMPreparedTypeInvariant ==
    /\ tmPrepared \subseteq RM

MsgsTypeInvariant ==
    /\ msgs \subseteq Msgs

TypeInvariant ==
    /\ RMStateTypeInvariant
    /\ TMStateTypeInvariant
    /\ TMPreparedTypeInvariant
    /\ MsgsTypeInvariant

Init ==
    /\ rmState = [rm \in RM |-> "working"]
    /\ tmState = "init"
    /\ tmPrepared = {}
    /\ msgs = {}

TMRcvPrepared(rm) ==
    /\ tmState = "init"
    /\ [type |-> "prepared", rm |-> rm] \in msgs
    /\ tmPrepared' = tmPrepared \union {rm}
    /\ UNCHANGED <<rmState, tmState, msgs>>

TMCommit ==
    /\ tmState = "init"
    /\ tmPrepared = RM
    /\ tmState' = "committed"
    /\ msgs' = msgs \union {[type |-> "commit"]}
    /\ UNCHANGED <<rmState, tmPrepared>>

TMAbort ==
    /\ tmState = "init"
    /\ tmState' = "aborted"
    /\ msgs' = msgs \union {[type |-> "abort"]}
    /\ UNCHANGED <<rmState, tmPrepared>>

RMPrepare(rm) ==
    /\ rmState[rm] = "working"
    /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]
    /\ msgs' = msgs \union {[type |-> "prepared", rm |-> rm]}
    /\ UNCHANGED <<tmState, tmPrepared>>

RMChooseToAbort(rm) ==
    /\ rmState[rm] = "working"
    /\ /\rmState' = [rmState EXCEPT ![rm] = "aborted"]
    /\ UNCHANGED <<tmState, tmPrepared, msgs>>

ExistAbortMsg ==
    /\ [type |-> "abort"] \in msgs

ExistCommitMsg ==
    /\ [type |-> "commit"] \in msgs

NoAbortMsg ==
    /\ [type |-> "abort"] \notin msgs

NoCommitMsg ==
    /\ [type |-> "commit"] \notin msgs

RMRcvCommitMsg(rm) ==
    /\ ExistCommitMsg
    /\ rmState' = [rmState EXCEPT ![rm] = "committed"]
    /\ UNCHANGED <<tmState, tmPrepared, msgs>>

RMRcvAbortMsg(rm) ==
    /\ ExistAbortMsg
    /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
    /\ UNCHANGED <<tmState, tmPrepared, msgs>>

RMOp(rm) ==
    \/ TMRcvPrepared(rm)
    \/ RMPrepare(rm)
    \/ RMChooseToAbort(rm)
    \/ RMRcvCommitMsg(rm)
    \/ RMRcvAbortMsg(rm)

ChooseRMOp ==
    /\ \E rm \in RM:
        /\ RMOp(rm)

Next ==
    \/ TMCommit
    \/ TMAbort
    \/ ChooseRMOp

Spec == Init /\ [][Next]_vars

ExistCommittedRM ==
    /\ \E rm \in RM: rmState[rm] = "committed"

NoAbortedRM ==
    /\ \A rm \in RM: rmState[rm] # "aborted"

ExistAbortedRM ==
    /\ \E rm \in RM: rmState[rm] = "aborted"

NoCommittedRM ==
    /\ \A rm \in RM: rmState[rm] # "committed"

Consistency ==
    /\ ExistCommittedRM => NoAbortedRM
    /\ ExistAbortedRM => NoCommittedRM

\* (~ \E rm \in RM: rmState[rm] = "committed") \/ \A rm \in RM: rmState[rm] # "aborted"
\* \A rm \in RM: rmState[rm] # "committed" \/ \A rm \in RM: rmState[rm] # "aborted"
\* case RMChooseToAbort: prove no prep msg
\* case RMRcvCommitMsg: prove has cmt msg => no abort rm
\* case RMRcvAbortMsg: prove has abt msg => no cmt rm

THEOREM TypeProperty == Spec => []TypeInvariant
<1> SUFFICES ASSUME Init /\ [][Next]_vars PROVE []TypeInvariant BY DEF Spec
<1>1 Init => TypeInvariant
  <2> SUFFICES ASSUME Init PROVE TypeInvariant OBVIOUS
  <2>1 RMStateTypeInvariant
    <3>a "working" \in RMState BY RMStateAxiom
    <3>b rmState = [rm \in RM |-> "working"] BY DEF Init
    <3> QED BY <3>a, <3>b DEF RMStateTypeInvariant
  <2>2 TMStateTypeInvariant
    <3>a tmState = "init" BY DEF Init
    <3>b @ \in TMState BY TMStateAxiom
    <3> QED BY <3>a, <3>b DEF TMStateTypeInvariant
  <2>3 TMPreparedTypeInvariant
    <3>a tmPrepared = {} BY DEF Init
    <3> QED BY <3>a DEF TMPreparedTypeInvariant
  <2>4 MsgsTypeInvariant
    <3>a msgs = {} BY DEF Init
    <3> QED BY MsgsAxiom, <3>a DEF MsgsTypeInvariant
  <2> QED BY <2>1, <2>2, <2>3, <2>4 DEF TypeInvariant
<1>2 TypeInvariant /\ Next => TypeInvariant'
  <2> SUFFICES ASSUME TypeInvariant /\ Next PROVE TypeInvariant' OBVIOUS
  <2> TMCommit \/ TMAbort \/ ChooseRMOp BY DEF Next
  <2>1 TMCommit => TypeInvariant'
    <3> SUFFICES ASSUME TMCommit PROVE TypeInvariant' OBVIOUS
    <3>1 RMStateTypeInvariant'
      <4>a UNCHANGED rmState BY DEF TMCommit
      <4>b rmState \in [RM -> RMState] BY DEF RMStateTypeInvariant, TypeInvariant
      <4> QED BY <4>a, <4>b DEF RMStateTypeInvariant
    <3>2 TMStateTypeInvariant'
      <4>a tmState' = "committed" BY DEF TMCommit
      <4> QED BY <4>a, TMStateAxiom DEF TMStateTypeInvariant
    <3>3 TMPreparedTypeInvariant'
      <4>a UNCHANGED tmPrepared BY DEF TMCommit
      <4>b tmPrepared \subseteq RM BY DEF TMPreparedTypeInvariant, TypeInvariant
      <4> QED BY <4>a, <4>b DEF TMPreparedTypeInvariant
    <3>4 MsgsTypeInvariant'
      <4>a {[type |-> "commit"]} \subseteq Msgs BY MsgsAxiom
      <4>b msgs' = msgs \union {[type |-> "commit"]} BY DEF TMCommit
      <4>c msgs \subseteq Msgs BY DEF MsgsTypeInvariant, TypeInvariant
      <4> QED BY <4>a, <4>b, <4>c DEF MsgsTypeInvariant
    <3> QED BY <3>1, <3>2, <3>3, <3>4 DEF TypeInvariant
  <2>2 TMAbort => TypeInvariant'
    <3> SUFFICES ASSUME TMAbort PROVE TypeInvariant' OBVIOUS
    <3>1 RMStateTypeInvariant'
      <4>a UNCHANGED rmState BY DEF TMAbort
      <4>b rmState \in [RM -> RMState] BY DEF RMStateTypeInvariant, TypeInvariant
      <4> QED BY <4>a, <4>b DEF RMStateTypeInvariant
    <3>2 TMStateTypeInvariant'
      <4>a tmState' = "aborted" BY DEF TMAbort
      <4> QED BY <4>a, TMStateAxiom DEF TMStateTypeInvariant
    <3>3 TMPreparedTypeInvariant'
      <4>a UNCHANGED tmPrepared BY DEF TMAbort
      <4>b tmPrepared \subseteq RM BY DEF TMPreparedTypeInvariant, TypeInvariant
      <4> QED BY <4>a, <4>b DEF TMPreparedTypeInvariant
    <3>4 MsgsTypeInvariant'
      <4>a {[type |-> "abort"]} \subseteq Msgs BY MsgsAxiom
      <4>b msgs' = msgs \union {[type |-> "abort"]} BY DEF TMAbort
      <4>c msgs \subseteq Msgs BY DEF MsgsTypeInvariant, TypeInvariant
      <4> QED BY <4>a, <4>b, <4>c DEF MsgsTypeInvariant
    <3> QED BY <3>1, <3>2, <3>3, <3>4 DEF TypeInvariant
  <2>3 ChooseRMOp => TypeInvariant'
    <3> SUFFICES ASSUME \E rm \in RM: RMOp(rm) PROVE TypeInvariant' BY DEF ChooseRMOp
    <3> PICK rm \in RM: RMOp(rm) OBVIOUS
    <3>1 TMRcvPrepared(rm) => TypeInvariant'
      <4> SUFFICES ASSUME TMRcvPrepared(rm) PROVE TypeInvariant' OBVIOUS
      <4>1 RMStateTypeInvariant'
        <5>a UNCHANGED rmState BY DEF TMRcvPrepared
        <5>b rmState \in [RM -> RMState] BY DEF RMStateTypeInvariant, TypeInvariant
        <5> QED BY <5>a, <5>b DEF RMStateTypeInvariant
      <4>2 TMStateTypeInvariant'
        <5>a UNCHANGED tmState BY DEF TMRcvPrepared
        <5>b tmState \in TMState BY DEF TMStateTypeInvariant, TypeInvariant
        <5> QED BY <5>a, <5>b DEF TMStateTypeInvariant
      <4>3 TMPreparedTypeInvariant'
        <5>a {rm} \subseteq RM OBVIOUS
        <5>b tmPrepared \subseteq RM BY DEF TMPreparedTypeInvariant, TypeInvariant
        <5>c tmPrepared' = tmPrepared \union {rm} BY DEF TMRcvPrepared
        <5> QED BY <5>a, <5>b, <5>c DEF TMPreparedTypeInvariant
      <4>4 MsgsTypeInvariant'
        <5>a UNCHANGED msgs BY DEF TMRcvPrepared
        <5>b msgs \subseteq Msgs BY DEF MsgsTypeInvariant, TypeInvariant
        <5> QED BY <5>a, <5>b DEF MsgsTypeInvariant
      <4> QED BY <4>1, <4>2, <4>3, <4>4 DEF TypeInvariant
    <3>2 RMPrepare(rm) => TypeInvariant'
      <4> SUFFICES ASSUME RMPrepare(rm) PROVE TypeInvariant' OBVIOUS
      <4>1 RMStateTypeInvariant'
        <5>a rmState \in [RM -> RMState] BY DEF RMStateTypeInvariant, TypeInvariant
        <5>b "prepared" \in RMState BY RMStateAxiom
        <5>c rmState' = [rmState EXCEPT ![rm] = "prepared"] BY DEF RMPrepare
        <5>d @ \in [RM -> RMState] BY <5>a, <5>b
        <5> QED BY <5>c, <5>d DEF RMStateTypeInvariant
      <4>2 TMStateTypeInvariant'
        <5>a UNCHANGED tmState BY DEF RMPrepare
        <5>b tmState \in TMState BY DEF TMStateTypeInvariant, TypeInvariant
        <5> QED BY <5>a, <5>b DEF TMStateTypeInvariant
      <4>3 TMPreparedTypeInvariant'
        <5>a UNCHANGED tmPrepared BY DEF RMPrepare
        <5>b tmPrepared \subseteq RM BY DEF TMPreparedTypeInvariant, TypeInvariant
        <5> QED BY <5>a, <5>b DEF TMPreparedTypeInvariant
      <4>4 MsgsTypeInvariant'
        <5>a msgs \subseteq Msgs BY DEF MsgsTypeInvariant, TypeInvariant
        <5>b [type |-> "prepared", rm |-> rm] \in Msgs BY MsgsAxiom
        <5>c msgs' = msgs \union {[type |-> "prepared", rm |-> rm]} BY DEF RMPrepare
        <5>d @ \subseteq Msgs BY MsgsAxiom, <5>a, <5>b
        <5> QED BY <5>c, <5>d DEF MsgsTypeInvariant
      <4> QED BY <4>1, <4>2, <4>3, <4>4 DEF TypeInvariant
    <3>3 RMChooseToAbort(rm) => TypeInvariant'
      <4> SUFFICES ASSUME RMChooseToAbort(rm) PROVE TypeInvariant' OBVIOUS
      <4>1 RMStateTypeInvariant'
        <5>a rmState \in [RM -> RMState] BY DEF RMStateTypeInvariant, TypeInvariant
        <5>b "aborted" \in RMState BY RMStateAxiom
        <5>c rmState' = [rmState EXCEPT ![rm] = "aborted"] BY DEF RMChooseToAbort
        <5>d @ \in [RM -> RMState] BY <5>a, <5>b
        <5> QED BY <5>c, <5>d DEF RMStateTypeInvariant
      <4>2 TMStateTypeInvariant'
        <5>a UNCHANGED tmState BY DEF RMChooseToAbort
        <5>b tmState \in TMState BY DEF TMStateTypeInvariant, TypeInvariant
        <5> QED BY <5>a, <5>b DEF TMStateTypeInvariant
      <4>3 TMPreparedTypeInvariant'
        <5>a UNCHANGED tmPrepared BY DEF RMChooseToAbort
        <5>b tmPrepared \subseteq RM BY DEF TMPreparedTypeInvariant, TypeInvariant
        <5> QED BY <5>a, <5>b DEF TMPreparedTypeInvariant
      <4>4 MsgsTypeInvariant'
        <5>a UNCHANGED msgs BY DEF RMChooseToAbort
        <5>b msgs \subseteq Msgs BY DEF MsgsTypeInvariant, TypeInvariant
        <5> QED BY <5>a, <5>b DEF MsgsTypeInvariant
      <4> QED BY <4>1, <4>2, <4>3, <4>4 DEF TypeInvariant
    <3>4 RMRcvCommitMsg(rm) => TypeInvariant'
      <4> SUFFICES ASSUME RMRcvCommitMsg(rm) PROVE TypeInvariant' OBVIOUS
      <4>1 RMStateTypeInvariant'
        <5>a rmState \in [RM -> RMState] BY DEF RMStateTypeInvariant, TypeInvariant
        <5>b "committed" \in RMState BY RMStateAxiom
        <5>c rmState' = [rmState EXCEPT ![rm] = "committed"] BY DEF RMRcvCommitMsg
        <5>d @ \in [RM -> RMState] BY <5>a, <5>b
        <5> QED BY <5>c, <5>d DEF RMStateTypeInvariant
      <4>2 TMStateTypeInvariant'
        <5>a UNCHANGED tmState BY DEF RMRcvCommitMsg
        <5>b tmState \in TMState BY DEF TMStateTypeInvariant, TypeInvariant
        <5> QED BY <5>a, <5>b DEF TMStateTypeInvariant
      <4>3 TMPreparedTypeInvariant'
        <5>a UNCHANGED tmPrepared BY DEF RMRcvCommitMsg
        <5>b tmPrepared \subseteq RM BY DEF TMPreparedTypeInvariant, TypeInvariant
        <5> QED BY <5>a, <5>b DEF TMPreparedTypeInvariant
      <4>4 MsgsTypeInvariant'
        <5>a UNCHANGED msgs BY DEF RMRcvCommitMsg
        <5>b msgs \subseteq Msgs BY DEF MsgsTypeInvariant, TypeInvariant
        <5> QED BY <5>a, <5>b DEF MsgsTypeInvariant
      <4> QED BY <4>1, <4>2, <4>3, <4>4 DEF TypeInvariant
    <3>5 RMRcvAbortMsg(rm) => TypeInvariant'
      <4> SUFFICES ASSUME RMRcvAbortMsg(rm) PROVE TypeInvariant' OBVIOUS
      <4>1 RMStateTypeInvariant'
        <5>a rmState \in [RM -> RMState] BY DEF RMStateTypeInvariant, TypeInvariant
        <5>b "aborted" \in RMState BY RMStateAxiom
        <5>c rmState' = [rmState EXCEPT ![rm] = "aborted"] BY DEF RMRcvAbortMsg
        <5>d @ \in [RM -> RMState] BY <5>a, <5>b
        <5> QED BY <5>c, <5>d DEF RMStateTypeInvariant
      <4>2 TMStateTypeInvariant'
        <5>a UNCHANGED tmState BY DEF RMRcvAbortMsg
        <5>b tmState \in TMState BY DEF TMStateTypeInvariant, TypeInvariant
        <5> QED BY <5>a, <5>b DEF TMStateTypeInvariant
      <4>3 TMPreparedTypeInvariant'
        <5>a UNCHANGED tmPrepared BY DEF RMRcvAbortMsg
        <5>b tmPrepared \subseteq RM BY DEF TMPreparedTypeInvariant, TypeInvariant
        <5> QED BY <5>a, <5>b DEF TMPreparedTypeInvariant
      <4>4 MsgsTypeInvariant'
        <5>a UNCHANGED msgs BY DEF RMRcvAbortMsg
        <5>b msgs \subseteq Msgs BY DEF MsgsTypeInvariant, TypeInvariant
        <5> QED BY <5>a, <5>b DEF MsgsTypeInvariant
      <4> QED BY <4>1, <4>2, <4>3, <4>4 DEF TypeInvariant
    <3> QED BY <3>1, <3>2, <3>3, <3>4, <3>5 DEF RMOp
  <2> QED BY <2>1, <2>2, <2>3
<1> QED BY <1>1, <1>2, PTL


\* RMChooseToAbort(rm) -> NoAbortedRM' \/ NoCommittedRM'
\* RMChooseToAbort(rm) -> NoCommittedRM'
\* RMChooseToAbort(rm) -> ExistUnpreparedRM -> Yet

\* RMRcvAbortMsg(rm) -> NoAbortedRM \/ NoCommittedRM
\* RMRcvAbortMsg(rm) -> NoCommittedRM
\* 

\* RMRcvCommitMsg(rm) -> NoAbortedRM \/ NoCommittedRM
\* RMRcvCommitMsg(rm) -> NoAbortedRM
\* RMRcvCommitMsg(rm) -> ExistCommitMsg -> NoAbortMsg


\* argument: 
\* argument: NoCommitMsg \/ NoAbortMsg
\* argument: NoAbortMsg \/ NoCommittedRM
\* argument: NoCommitMsg \/ NoAbortedRM

Argument2 == NoCommitMsg \/ NoAbortedRM

LEMMA Lemma2 == Spec => []Argument2

Argument1 == NoAbortedRM \/ NoCommittedRM

LEMMA Lemma1 == Spec => []Argument1
<1> SUFFICES ASSUME Init /\ [][Next]_vars PROVE []Argument1 BY DEF Spec
<1>b []TypeInvariant BY TypeProperty DEF Spec
<1>c RMStateTypeInvariant /\ RMStateTypeInvariant' BY <1>b, PTL DEF TypeInvariant
<1>d rmState \in [RM -> RMState] /\ rmState' \in [RM -> RMState] BY <1>c DEF RMStateTypeInvariant
<1>1 Init => Argument1 BY DEF Init, Argument1, NoAbortedRM
<1>2 Argument1 /\ Next => Argument1'
  <2>1 Argument1 /\ TMCommit => Argument1'
    <3>1 NoAbortedRM /\ TMCommit => Argument1' BY DEF NoAbortedRM, TMCommit, Argument1
    <3>2 NoCommittedRM /\ TMCommit => Argument1' BY DEF NoCommittedRM, TMCommit, Argument1
    <3> QED BY <3>1, <3>2 DEF Argument1
  <2>2 Argument1 /\ TMAbort => Argument1'
    <3>1 NoAbortedRM /\ TMAbort => Argument1' BY DEF NoAbortedRM, TMAbort, Argument1
    <3>2 NoCommittedRM /\ TMAbort => Argument1' BY DEF NoCommittedRM, TMAbort, Argument1
    <3> QED BY <3>1, <3>2 DEF Argument1
  <2>3 Argument1 /\ ChooseRMOp => Argument1'
    <3> SUFFICES ASSUME Argument1 /\ ChooseRMOp PROVE Argument1' OBVIOUS
    <3> PICK rm \in RM: RMOp(rm) BY DEF ChooseRMOp
    <3>1 TMRcvPrepared(rm) => Argument1' BY DEF TMRcvPrepared, Argument1, NoAbortedRM, NoCommittedRM
    <3>2 RMPrepare(rm) => Argument1'
      <4> SUFFICES ASSUME RMPrepare(rm) PROVE Argument1' OBVIOUS
      <4>a rmState' = [rmState EXCEPT ![rm] = "prepared"] BY DEF RMPrepare
      <4>b rmState'[rm] = "prepared" BY <1>d, <4>a
      <4>1 NoAbortedRM => NoAbortedRM'
        <5> SUFFICES ASSUME NoAbortedRM PROVE \A rm2 \in RM: rmState'[rm2] # "aborted" BY DEF NoAbortedRM
        <5> TAKE rm2 \in RM
        <5>1 rm2 = rm => rmState'[rm2] # "aborted" BY <4>b
        <5>2 rm2 # rm => rmState'[rm2] # "aborted"
          <6> SUFFICES ASSUME rm2 # rm PROVE rmState'[rm2] # "aborted" OBVIOUS
          <6>a rmState'[rm2] = rmState[rm2] BY <1>d, <4>a
          <6>b @ # "aborted" BY <4>a DEF NoAbortedRM, Argument1
          <6> QED BY <6>a, <6>b
        <5> QED BY <5>1, <5>2
      <4>2 NoCommittedRM => NoCommittedRM'
        <5> SUFFICES ASSUME NoCommittedRM PROVE \A rm2 \in RM: rmState'[rm2] # "committed" BY DEF NoCommittedRM
        <5> TAKE rm2 \in RM
        <5>1 rm2 = rm => rmState'[rm2] # "committed" BY <4>b
        <5>2 rm2 # rm => rmState'[rm2] # "committed"
          <6> SUFFICES ASSUME rm2 # rm PROVE rmState'[rm2] # "committed" OBVIOUS
          <6>a rmState'[rm2] = rmState[rm2] BY <1>d, <4>a
          <6>b @ # "committed" BY <4>a DEF NoCommittedRM, Argument1
          <6> QED BY <6>a, <6>b
        <5> QED BY <5>1, <5>2
      <4> QED BY <4>1, <4>2 DEF Argument1
    <3>3 RMChooseToAbort(rm) => Argument1'
      <4> SUFFICES ASSUME RMChooseToAbort(rm) PROVE Argument1' OBVIOUS
      <4>1 NoCommittedRM'
        <5> QED
      <4> QED BY <4>1 DEF Argument1
    <3>4 RMRcvCommitMsg(rm) => Argument1'
    <3>5 RMRcvAbortMsg(rm) => Argument1'
    <3> QED BY <3>1, <3>2, <3>3, <3>4, <3>5 DEF ChooseRMOp, RMOp
  <2> QED BY <2>1, <2>2, <2>3 DEF Next
<1> QED BY <1>1, <1>2, PTL

THEOREM Spec => []Consistency
<1>a Argument1 <=> Consistency BY DEF ExistCommittedRM, NoAbortedRM, ExistAbortedRM, NoCommittedRM, Consistency, Argument1
<1> QED BY <1>a, PTL, Lemma1

=============================================================================
\* Modification History
\* Last modified Mon Jan 15 11:11:51 CST 2018 by functioner
\* Created Fri Dec 22 20:05:29 CST 2017 by functioner
