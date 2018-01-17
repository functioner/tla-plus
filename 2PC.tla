-------------------------------- MODULE 2PC --------------------------------
EXTENDS TLAPS

CONSTANTS RM, RMState, TMState, Msgs

VARIABLES rmState, tmState, tmPrepared, msgs

vars == <<rmState, tmState, tmPrepared, msgs>>

AXIOM RMAxiom ==
    /\ RM # {}

AXIOM RMStateAxiom ==
    /\ RMState = {"working", "prepared", "committed", "aborted"}

AXIOM TMStateAxiom ==
    /\ TMState = {"init", "committed", "aborted"}

AXIOM MsgsAxiom ==
    /\ Msgs = [type: {"prepared"}, rm: RM] \union [type: {"commit", "abort"}]

ExistAbortMsg ==
    /\ [type |-> "abort"] \in msgs

ExistCommitMsg ==
    /\ [type |-> "commit"] \in msgs

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
    /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
    /\ UNCHANGED <<tmState, tmPrepared, msgs>>

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

THEOREM TypeSafety == Spec => []TypeInvariant
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

ExistCommittedRM ==
    /\ \E rm \in RM: rmState[rm] = "committed"

ExistAbortedRM ==
    /\ \E rm \in RM: rmState[rm] = "aborted"

Consistency ==
    /\ ExistCommittedRM => ~ExistAbortedRM
    /\ ExistAbortedRM => ~ExistCommittedRM

PreparedOrAbort(rm) ==
    \/ [type |-> "prepared", rm |-> rm] \notin msgs
    \/ rmState[rm] # "aborted"

TMPreparedOrder(rm) ==
    /\ rm \in tmPrepared => [type |-> "prepared", rm |-> rm] \in msgs

RMPreparedOrder(rm) ==
    /\ [type |-> "prepared", rm |-> rm] \in msgs => rmState[rm] = "prepared"

Phase1 ==
    /\ tmPrepared # RM

Phase2 ==
    /\ tmPrepared = RM

PhaseArguments ==
    /\ Phase1 => (tmState = "init" => \A rm \in RM: PreparedOrAbort(rm))
    /\ Phase1 => (tmState = "init" => \A rm \in RM: RMPreparedOrder(rm))
    /\ Phase2 => (ExistAbortedRM => ExistAbortMsg)
    /\ Phase2 => \A rm \in RM: rmState[rm] # "working"
    /\ ~ExistAbortedRM \/ ~ExistCommittedRM

Arguments ==
    /\ tmState = "committed" <=> ExistCommitMsg
    /\ tmState = "aborted" <=> ExistAbortMsg
    /\ ExistCommittedRM => ExistCommitMsg
    /\ tmState = "committed" => tmPrepared = RM
    /\ tmState = "init" => \A rm \in RM: TMPreparedOrder(rm)
    /\ PhaseArguments

THEOREM Safety == Spec => []Consistency
<1>a ~ExistAbortedRM \/ ~ExistCommittedRM <=> Consistency BY DEF ExistCommittedRM, ExistAbortedRM, Consistency
<1>b Arguments => ~ExistAbortedRM \/ ~ExistCommittedRM BY DEF Arguments, PhaseArguments
<1> SUFFICES Spec => []Arguments BY <1>a, <1>b, PTL
<1> SUFFICES ASSUME Init /\ [][Next]_vars PROVE []Arguments BY DEF Spec
<1>Ta []TypeInvariant BY TypeSafety DEF Spec
<1>Tb RMStateTypeInvariant /\ RMStateTypeInvariant' BY <1>Ta, PTL DEF TypeInvariant
<1>Tc TMPreparedTypeInvariant BY <1>Ta, PTL DEF TypeInvariant
<1>Td TMStateTypeInvariant BY <1>Ta, PTL DEF TypeInvariant
<1>T1 rmState \in [RM -> RMState] BY <1>Tb DEF RMStateTypeInvariant
<1>T2 rmState' \in [RM -> RMState] BY <1>Tb DEF RMStateTypeInvariant
<1>T3 tmPrepared \subseteq RM BY <1>Tc DEF TMPreparedTypeInvariant
<1>T4 tmState \in TMState BY <1>Td DEF TMStateTypeInvariant
<1>1 Init => Arguments
  <2> SUFFICES ASSUME Init PROVE Arguments OBVIOUS
  <2> USE DEF Init
  <2>a ~ExistCommittedRM BY DEF ExistCommittedRM
  <2>b \A rm \in RM: TMPreparedOrder(rm) BY DEF TMPreparedOrder
  <2>c \A rm \in RM: PreparedOrAbort(rm) BY DEF PreparedOrAbort
  <2>d \A rm \in RM: RMPreparedOrder(rm) BY DEF RMPreparedOrder
  <2>e ~Phase2 BY RMAxiom DEF Phase2
  <2>f ~ExistCommittedRM BY DEF ExistCommittedRM
  <2>g ~ExistCommitMsg BY DEF ExistCommitMsg
  <2>h ~ExistAbortMsg BY DEF ExistAbortMsg
  <2> QED BY <2>a, <2>b, <2>c, <2>d, <2>e, <2>f, <2>g, <2>h DEF Arguments, PhaseArguments
<1>2 Arguments /\ Next => Arguments'
  <2> SUFFICES ASSUME Arguments /\ Next PROVE Arguments' OBVIOUS
  <2>1 tmState' = "committed" <=> ExistCommitMsg'
    <3>1 CASE TMCommit
      <4>a tmState' = "committed" BY <3>1 DEF TMCommit
      <4>b [type |-> "commit"] \in msgs' BY <3>1 DEF TMCommit
      <4> QED BY <4>a, <4>b DEF ExistCommitMsg
    <3>2 CASE TMAbort
      <4>a tmState' # "committed" BY <3>2 DEF TMAbort
      <4>b [type |-> "commit"] \notin msgs BY <3>2 DEF Arguments, ExistCommitMsg, TMAbort
      <4>c [type |-> "commit"] \notin msgs' BY <4>b, <3>2 DEF TMAbort
      <4> QED BY <4>a, <4>c DEF ExistCommitMsg
    <3>3 CASE ChooseRMOp
      <4> PICK rm \in RM: RMOp(rm) BY <3>3 DEF ChooseRMOp
      <4>1 CASE TMRcvPrepared(rm)
        <5>a tmState' # "committed" BY <4>1 DEF TMRcvPrepared
        <5>b [type |-> "commit"] \notin msgs BY <4>1 DEF Arguments, ExistCommitMsg, TMRcvPrepared
        <5>c [type |-> "commit"] \notin msgs' BY <5>b, <4>1 DEF TMRcvPrepared
        <5> QED BY <5>a, <5>c DEF ExistCommitMsg
      <4>2 CASE RMPrepare(rm)
        <5>1 CASE tmState = "committed"
          <6>a [type |-> "commit"] \in msgs BY <5>1 DEF Arguments, ExistCommitMsg
          <6>b [type |-> "commit"] \in msgs' BY <4>2, <6>a DEF RMPrepare
          <6> QED BY <5>1, <6>b, <4>2 DEF RMPrepare, ExistCommitMsg
        <5>2 CASE tmState # "committed"
          <6>a [type |-> "commit"] \notin msgs BY <5>2 DEF Arguments, ExistCommitMsg
          <6>b [type |-> "commit"] \notin msgs' BY <6>a, <4>2 DEF RMPrepare
          <6> QED BY <5>2, <6>b, <4>2 DEF RMPrepare, ExistCommitMsg
        <5> QED BY <5>1, <5>2
      <4>3 CASE RMChooseToAbort(rm)
        <5>1 CASE tmState = "committed"
          <6>a [type |-> "commit"] \in msgs BY <5>1 DEF Arguments, ExistCommitMsg
          <6>b [type |-> "commit"] \in msgs' BY <4>3, <6>a DEF RMChooseToAbort
          <6> QED BY <5>1, <6>b, <4>3 DEF RMChooseToAbort, ExistCommitMsg
        <5>2 CASE tmState # "committed"
          <6>a [type |-> "commit"] \notin msgs BY <5>2 DEF Arguments, ExistCommitMsg
          <6>b [type |-> "commit"] \notin msgs' BY <6>a, <4>3 DEF RMChooseToAbort
          <6> QED BY <5>2, <6>b, <4>3 DEF RMChooseToAbort, ExistCommitMsg
        <5> QED BY <5>1, <5>2
      <4>4 CASE RMRcvCommitMsg(rm)
        <5>1 CASE tmState = "committed"
          <6>a [type |-> "commit"] \in msgs BY <5>1 DEF Arguments, ExistCommitMsg
          <6>b [type |-> "commit"] \in msgs' BY <4>4, <6>a DEF RMRcvCommitMsg
          <6> QED BY <5>1, <6>b, <4>4 DEF RMRcvCommitMsg, ExistCommitMsg
        <5>2 CASE tmState # "committed"
          <6>a [type |-> "commit"] \notin msgs BY <5>2 DEF Arguments, ExistCommitMsg
          <6>b [type |-> "commit"] \notin msgs' BY <6>a, <4>4 DEF RMRcvCommitMsg
          <6> QED BY <5>2, <6>b, <4>4 DEF RMRcvCommitMsg, ExistCommitMsg
        <5> QED BY <5>1, <5>2
      <4>5 CASE RMRcvAbortMsg(rm)
        <5>1 CASE tmState = "committed"
          <6>a [type |-> "commit"] \in msgs BY <5>1 DEF Arguments, ExistCommitMsg
          <6>b [type |-> "commit"] \in msgs' BY <4>5, <6>a DEF RMRcvAbortMsg
          <6> QED BY <5>1, <6>b, <4>5 DEF RMRcvAbortMsg, ExistCommitMsg
        <5>2 CASE tmState # "committed"
          <6>a [type |-> "commit"] \notin msgs BY <5>2 DEF Arguments, ExistCommitMsg
          <6>b [type |-> "commit"] \notin msgs' BY <6>a, <4>5 DEF RMRcvAbortMsg
          <6> QED BY <5>2, <6>b, <4>5 DEF RMRcvAbortMsg, ExistCommitMsg
        <5> QED BY <5>1, <5>2
      <4> QED BY <4>1, <4>2, <4>3, <4>4, <4>5 DEF RMOp
    <3> QED BY <3>1, <3>2, <3>3 DEF Next
  <2>2 tmState' = "aborted" <=> ExistAbortMsg'
    <3>1 CASE TMCommit
      <4>a tmState' # "aborted" BY <3>1 DEF TMCommit
      <4>b [type |-> "abort"] \notin msgs BY <3>1 DEF Arguments, ExistAbortMsg, TMCommit
      <4>c [type |-> "abort"] \notin msgs' BY <4>b, <3>1 DEF TMCommit
      <4> QED BY <4>a, <4>c DEF ExistAbortMsg
    <3>2 CASE TMAbort
      <4>a tmState' = "aborted" BY <3>2 DEF TMAbort
      <4>b [type |-> "abort"] \in msgs' BY <3>2 DEF TMAbort
      <4> QED BY <4>a, <4>b DEF ExistAbortMsg
    <3>3 CASE ChooseRMOp
      <4> PICK rm \in RM: RMOp(rm) BY <3>3 DEF ChooseRMOp
      <4>1 CASE TMRcvPrepared(rm)
        <5>a tmState' # "aborted" BY <4>1 DEF TMRcvPrepared
        <5>b [type |-> "abort"] \notin msgs BY <4>1 DEF Arguments, ExistAbortMsg, TMRcvPrepared
        <5>c [type |-> "abort"] \notin msgs' BY <5>b, <4>1 DEF TMRcvPrepared
        <5> QED BY <5>a, <5>c DEF ExistAbortMsg
      <4>2 CASE RMPrepare(rm)
        <5>1 CASE tmState = "aborted"
          <6>a [type |-> "abort"] \in msgs BY <5>1 DEF Arguments, ExistAbortMsg
          <6>b [type |-> "abort"] \in msgs' BY <4>2, <6>a DEF RMPrepare
          <6> QED BY <5>1, <6>b, <4>2 DEF RMPrepare, ExistAbortMsg
        <5>2 CASE tmState # "aborted"
          <6>a [type |-> "abort"] \notin msgs BY <5>2 DEF Arguments, ExistAbortMsg
          <6>b [type |-> "abort"] \notin msgs' BY <6>a, <4>2 DEF RMPrepare
          <6> QED BY <5>2, <6>b, <4>2 DEF RMPrepare, ExistAbortMsg
        <5> QED BY <5>1, <5>2
      <4>3 CASE RMChooseToAbort(rm)
        <5>1 CASE tmState = "aborted"
          <6>a [type |-> "abort"] \in msgs BY <5>1 DEF Arguments, ExistAbortMsg
          <6>b [type |-> "abort"] \in msgs' BY <4>3, <6>a DEF RMChooseToAbort
          <6> QED BY <5>1, <6>b, <4>3 DEF RMChooseToAbort, ExistAbortMsg
        <5>2 CASE tmState # "aborted"
          <6>a [type |-> "abort"] \notin msgs BY <5>2 DEF Arguments, ExistAbortMsg
          <6>b [type |-> "abort"] \notin msgs' BY <6>a, <4>3 DEF RMChooseToAbort
          <6> QED BY <5>2, <6>b, <4>3 DEF RMChooseToAbort, ExistAbortMsg
        <5> QED BY <5>1, <5>2
      <4>4 CASE RMRcvCommitMsg(rm)
        <5>1 CASE tmState = "aborted"
          <6>a [type |-> "abort"] \in msgs BY <5>1 DEF Arguments, ExistAbortMsg
          <6>b [type |-> "abort"] \in msgs' BY <4>4, <6>a DEF RMRcvCommitMsg
          <6> QED BY <5>1, <6>b, <4>4 DEF RMRcvCommitMsg, ExistAbortMsg
        <5>2 CASE tmState # "aborted"
          <6>a [type |-> "abort"] \notin msgs BY <5>2 DEF Arguments, ExistAbortMsg
          <6>b [type |-> "abort"] \notin msgs' BY <6>a, <4>4 DEF RMRcvCommitMsg
          <6> QED BY <5>2, <6>b, <4>4 DEF RMRcvCommitMsg, ExistAbortMsg
        <5> QED BY <5>1, <5>2
      <4>5 CASE RMRcvAbortMsg(rm)
        <5>1 CASE tmState = "aborted"
          <6>a [type |-> "abort"] \in msgs BY <5>1 DEF Arguments, ExistAbortMsg
          <6>b [type |-> "abort"] \in msgs' BY <4>5, <6>a DEF RMRcvAbortMsg
          <6> QED BY <5>1, <6>b, <4>5 DEF RMRcvAbortMsg, ExistAbortMsg
        <5>2 CASE tmState # "aborted"
          <6>a [type |-> "abort"] \notin msgs BY <5>2 DEF Arguments, ExistAbortMsg
          <6>b [type |-> "abort"] \notin msgs' BY <6>a, <4>5 DEF RMRcvAbortMsg
          <6> QED BY <5>2, <6>b, <4>5 DEF RMRcvAbortMsg, ExistAbortMsg
        <5> QED BY <5>1, <5>2
      <4> QED BY <4>1, <4>2, <4>3, <4>4, <4>5 DEF RMOp
    <3> QED BY <3>1, <3>2, <3>3 DEF Next
  <2>3 ExistCommittedRM' => ExistCommitMsg'
    <3>1 CASE TMCommit
      <4>a [type |-> "commit"] \in msgs' BY <3>1 DEF TMCommit
      <4> QED BY <4>a DEF ExistCommitMsg
    <3>2 CASE TMAbort
      <4>1 CASE ExistCommittedRM
        <5>a [type |-> "commit"] \in msgs BY <4>1 DEF Arguments, ExistCommitMsg
        <5>b [type |-> "commit"] \in msgs' BY <5>a, <3>2 DEF TMAbort
        <5> QED BY <5>b DEF ExistCommitMsg
      <4>2 CASE ~ExistCommittedRM BY <3>2, <4>2 DEF TMAbort, ExistCommittedRM
      <4> QED BY <4>1, <4>2
    <3>3 CASE ChooseRMOp
      <4> PICK rm \in RM: RMOp(rm) BY <3>3 DEF ChooseRMOp
      <4>1 CASE TMRcvPrepared(rm) BY <4>1 DEF TMRcvPrepared, ExistCommittedRM, ExistCommitMsg, Arguments
      <4>2 CASE RMPrepare(rm)
        <5>1 CASE ExistCommittedRM
          <6>a [type |-> "commit"] \in msgs BY <5>1 DEF Arguments, ExistCommitMsg
          <6>b [type |-> "commit"] \in msgs' BY <4>2, <6>a DEF RMPrepare
          <6> QED BY <5>1, <6>b, <4>2 DEF RMPrepare, ExistCommitMsg
        <5>2 CASE ~ExistCommittedRM
          <6> SUFFICES \A rm2 \in RM: rmState'[rm2] # "committed" BY DEF ExistCommittedRM
          <6> TAKE rm2 \in RM
          <6>1 CASE rm2 = rm
            <7>a rmState'[rm2] = "prepared" BY <6>1, <4>2, <1>T2 DEF RMPrepare
            <7> QED BY <7>a
          <6>2 CASE rm2 # rm
            <7>a rmState[rm2] # "committed" BY <5>2 DEF ExistCommittedRM
            <7>b rmState'[rm2] # "committed" BY <7>a, <4>2, <6>2, <1>T2 DEF RMPrepare
            <7> QED BY <7>b
          <6> QED BY <6>1, <6>2
        <5> QED BY <5>1, <5>2
      <4>3 CASE RMChooseToAbort(rm)
        <5>1 CASE ExistCommittedRM
          <6>a [type |-> "commit"] \in msgs BY <5>1 DEF Arguments, ExistCommitMsg
          <6>b [type |-> "commit"] \in msgs' BY <4>3, <6>a DEF RMChooseToAbort
          <6> QED BY <5>1, <6>b, <4>3 DEF RMChooseToAbort, ExistCommitMsg
        <5>2 CASE ~ExistCommittedRM
          <6> SUFFICES \A rm2 \in RM: rmState'[rm2] # "committed" BY DEF ExistCommittedRM
          <6> TAKE rm2 \in RM
          <6>1 CASE rm2 = rm
            <7>a rmState'[rm2] = "aborted" BY <6>1, <4>3, <1>T2 DEF RMChooseToAbort
            <7> QED BY <7>a
          <6>2 CASE rm2 # rm
            <7>a rmState[rm2] # "committed" BY <5>2 DEF ExistCommittedRM
            <7>b rmState'[rm2] # "committed" BY <7>a, <4>3, <6>2, <1>T2 DEF RMChooseToAbort
            <7> QED BY <7>b
          <6> QED BY <6>1, <6>2
        <5> QED BY <5>1, <5>2
      <4>4 CASE RMRcvCommitMsg(rm) BY <4>4 DEF RMRcvCommitMsg, ExistCommitMsg
      <4>5 CASE RMRcvAbortMsg(rm)
        <5> SUFFICES \A rm2 \in RM: rmState'[rm2] # "committed" BY DEF ExistCommittedRM
        <5> TAKE rm2 \in RM
        <5>1 CASE rm2 = rm BY <4>5, <1>T2, <5>1 DEF RMRcvAbortMsg
        <5>2 CASE rm2 # rm
          <6>a ~ExistCommitMsg BY <4>5 DEF RMRcvAbortMsg, Arguments
          <6>b rmState[rm2] # "committed" BY <6>a DEF Arguments, ExistCommittedRM
          <6> QED BY <6>b, <5>2, <4>5, <1>T2 DEF RMRcvAbortMsg
        <5> QED BY <5>1, <5>2
      <4> QED BY <4>1, <4>2, <4>3, <4>4, <4>5 DEF RMOp
    <3> QED BY <3>1, <3>2, <3>3 DEF Next
  <2>4 tmState' = "committed" => tmPrepared' = RM
    <3>1 CASE TMCommit BY <3>1 DEF TMCommit
    <3>2 CASE TMAbort BY <3>2 DEF TMAbort
    <3>3 CASE ChooseRMOp
      <4> PICK rm \in RM: RMOp(rm) BY <3>3 DEF ChooseRMOp
      <4>1 CASE TMRcvPrepared(rm) BY <4>1 DEF TMRcvPrepared
      <4>2 CASE RMPrepare(rm)
        <5>1 CASE tmState = "committed"
          <6>a tmPrepared = RM BY <5>1 DEF Arguments
          <6> QED BY <6>a, <4>2 DEF RMPrepare
        <5>2 CASE tmState # "committed" BY <5>2, <4>2 DEF RMPrepare
        <5> QED BY <5>1, <5>2
      <4>3 CASE RMChooseToAbort(rm) BY <4>3 DEF RMChooseToAbort, Arguments
      <4>4 CASE RMRcvCommitMsg(rm) BY <4>4 DEF RMRcvCommitMsg, Arguments
      <4>5 CASE RMRcvAbortMsg(rm) BY <4>5 DEF RMRcvAbortMsg, Arguments
      <4> QED BY <4>1, <4>2, <4>3, <4>4, <4>5 DEF RMOp
    <3> QED BY <3>1, <3>2, <3>3 DEF Next
  <2>5 tmState' = "init" => \A rm \in RM: TMPreparedOrder(rm)'
    <3>1 CASE TMCommit BY <3>1 DEF TMCommit, TMPreparedOrder, Arguments
    <3>2 CASE TMAbort BY <3>2 DEF TMAbort, TMPreparedOrder, Arguments
    <3>3 CASE ChooseRMOp
      <4> PICK rm \in RM: RMOp(rm) BY <3>3 DEF ChooseRMOp
      <4>1 CASE TMRcvPrepared(rm)
        <5> SUFFICES \A rm2 \in RM: TMPreparedOrder(rm2)' OBVIOUS
        <5> TAKE rm2 \in RM
        <5>1 CASE rm2 = rm
          <6>a [type |-> "prepared", rm |-> rm2] \in msgs' BY <5>1, <4>1 DEF TMRcvPrepared
          <6> QED BY <6>a DEF TMPreparedOrder
        <5>2 CASE rm2 # rm BY <5>2, <4>1 DEF TMPreparedOrder, Arguments, TMRcvPrepared
        <5> QED BY <5>1, <5>2
      <4>2 CASE RMPrepare(rm)
        <5>1 CASE tmState = "init" BY <4>2, <5>1 DEF RMPrepare, Arguments, TMPreparedOrder
        <5>2 CASE tmState # "init" BY <5>2, <4>2 DEF RMPrepare, Arguments
        <5> QED BY <5>1, <5>2
      <4>3 CASE RMChooseToAbort(rm)
        <5>1 CASE tmState = "init" BY <4>3, <5>1 DEF RMChooseToAbort, Arguments, TMPreparedOrder
        <5>2 CASE tmState # "init" BY <5>2, <4>3 DEF RMChooseToAbort, Arguments
        <5> QED BY <5>1, <5>2
      <4>4 CASE RMRcvCommitMsg(rm)
        <5>1 CASE tmState = "init" BY <5>1, <4>4 DEF RMRcvCommitMsg, Arguments, TMPreparedOrder
        <5>2 CASE tmState # "init" BY <5>2, <4>4 DEF RMRcvCommitMsg, Arguments
        <5> QED BY <5>1, <5>2
      <4>5 CASE RMRcvAbortMsg(rm)
        <5>1 CASE tmState = "init" BY <5>1, <4>5 DEF RMRcvAbortMsg, Arguments, TMPreparedOrder
        <5>2 CASE tmState # "init" BY <5>2, <4>5 DEF RMRcvAbortMsg, Arguments
        <5> QED BY <5>1, <5>2
      <4> QED BY <4>1, <4>2, <4>3, <4>4, <4>5 DEF RMOp
    <3> QED BY <3>1, <3>2, <3>3 DEF Next
  <2>6 PhaseArguments'
    <3>1 CASE Phase1
      <4>a ~ExistCommitMsg BY <3>1 DEF Phase1, ExistCommitMsg, Arguments
      <4>b ~ExistCommittedRM BY <4>a DEF ExistCommittedRM, Arguments
      <4>1 Phase1' => (tmState' = "init" => \A rm \in RM: PreparedOrAbort(rm)')
        <5>1 ~TMCommit BY <3>1 DEF TMCommit, Phase1
        <5>2 CASE TMAbort
          <6> SUFFICES \A rm \in RM: PreparedOrAbort(rm)' OBVIOUS
          <6> TAKE rm \in RM
          <6>a tmState = "init" BY <5>2 DEF TMAbort
          <6>1 CASE [type |-> "prepared", rm |-> rm] \notin msgs
            <7>a [type |-> "prepared", rm |-> rm] \notin msgs' BY <6>1, <5>2 DEF TMAbort
            <7> QED BY <7>a DEF PreparedOrAbort
          <6>2 CASE rmState[rm] # "aborted"
            <7>a rmState'[rm] # "aborted" BY <6>2, <5>2 DEF TMAbort
            <7> QED BY <7>a DEF PreparedOrAbort
          <6> QED BY <6>1, <6>2, <3>1, <6>a DEF PreparedOrAbort, PhaseArguments, Arguments
        <5>3 CASE ChooseRMOp
          <6> PICK rm \in RM: RMOp(rm) BY <5>3 DEF ChooseRMOp
          <6>1 CASE TMRcvPrepared(rm) BY <6>1, <3>1 DEF TMRcvPrepared, PhaseArguments, Arguments, PreparedOrAbort
          <6>2 CASE RMPrepare(rm)
            <7> SUFFICES \A rm2 \in RM: tmState' = "init" => PreparedOrAbort(rm2)' OBVIOUS
            <7> TAKE rm2 \in RM
            <7>1 CASE rm2 = rm
              <8>a rmState'[rm2] # "aborted" BY <6>2, <1>T2, <7>1 DEF RMPrepare
              <8> QED BY <8>a DEF PreparedOrAbort
            <7>2 CASE rm2 # rm
              <8>a tmState = "init" => PreparedOrAbort(rm2) BY <3>1 DEF PhaseArguments, Arguments
              <8> QED BY <7>2, <6>2, <8>a, <1>T1, <1>T2 DEF RMPrepare, PreparedOrAbort
            <7> QED BY <7>1, <7>2
          <6>3 CASE RMChooseToAbort(rm)
            <7>1 CASE tmState = "init"
              <8> SUFFICES \A rm2 \in RM: tmState' = "init" => PreparedOrAbort(rm2)' OBVIOUS
              <8> TAKE rm2 \in RM
              <8>1 CASE rm2 = rm
                <9>a rmState[rm] = "working" BY <6>3 DEF RMChooseToAbort
                <9>b [type |-> "prepared", rm |-> rm] \notin msgs BY <9>a, <3>1, <7>1 DEF RMPreparedOrder, PhaseArguments, Arguments
                <9> QED BY <9>b, <8>1, <6>3 DEF PreparedOrAbort, RMChooseToAbort
              <8>2 CASE rm2 # rm BY <8>2, <6>3, <3>1, <1>T2 DEF RMChooseToAbort, PhaseArguments, Arguments, PreparedOrAbort
              <8> QED BY <8>1, <8>2
            <7>2 CASE tmState # "init" BY <7>2, <6>3 DEF RMChooseToAbort
            <7> QED BY <7>1, <7>2
          <6>4 ~RMRcvCommitMsg(rm) BY <3>1 DEF Phase1, Arguments, RMRcvCommitMsg
          <6>5 CASE RMRcvAbortMsg(rm)
            <7>a tmState = "aborted" BY <6>5 DEF RMRcvAbortMsg, Arguments
            <7> QED BY <7>a, <6>5 DEF RMRcvAbortMsg
          <6> QED BY <6>1, <6>2, <6>3, <6>4, <6>5 DEF RMOp
        <5> QED BY <5>1, <5>2, <5>3 DEF Next
      <4>2 Phase1' => (tmState' = "init" => \A rm \in RM: RMPreparedOrder(rm)')
        <5>1 CASE TMCommit BY <5>1, <3>1 DEF TMCommit, Arguments, PhaseArguments
        <5>2 CASE TMAbort BY <5>2, <3>1 DEF TMAbort, Arguments, PhaseArguments
        <5>3 CASE ChooseRMOp
          <6> PICK rm \in RM: RMOp(rm) BY <5>3 DEF ChooseRMOp
          <6>1 CASE TMRcvPrepared(rm) BY <6>1, <3>1 DEF TMRcvPrepared, Arguments, PhaseArguments, RMPreparedOrder
          <6>2 CASE RMPrepare(rm)
            <7>1 CASE tmState = "init"
              <8> SUFFICES \A rm2 \in RM: RMPreparedOrder(rm2)' OBVIOUS
              <8> TAKE rm2 \in RM
              <8>a RMPreparedOrder(rm2) BY <7>1, <3>1 DEF Arguments, PhaseArguments
              <8> QED BY <8>a, <6>2, <1>T2 DEF RMPreparedOrder, RMPrepare
            <7>2 CASE tmState # "init" BY <7>2, <6>2, <3>1 DEF Arguments, PhaseArguments, RMPreparedOrder, RMPrepare
            <7> QED BY <7>1, <7>2
          <6>3 CASE RMChooseToAbort(rm)
            <7>1 CASE tmState = "init"
              <8> SUFFICES \A rm2 \in RM: RMPreparedOrder(rm2)' OBVIOUS
              <8> TAKE rm2 \in RM
              <8>a RMPreparedOrder(rm2) BY <7>1, <3>1 DEF Arguments, PhaseArguments
              <8>b [type |-> "prepared", rm |-> rm] \notin msgs BY <3>1, <7>1, <6>3 DEF RMPreparedOrder, RMChooseToAbort, Arguments, PhaseArguments
              <8>1 CASE rm2 = rm BY <8>b, <8>1, <6>3 DEF RMChooseToAbort, RMPreparedOrder
              <8>2 CASE rm2 # rm BY <8>a, <8>2, <1>T2, <6>3 DEF RMPreparedOrder, RMChooseToAbort
              <8> QED BY <8>1, <8>2
            <7>2 CASE tmState # "init" BY <7>2, <6>3, <3>1 DEF Arguments, PhaseArguments, RMPreparedOrder, RMChooseToAbort
            <7> QED BY <7>1, <7>2
          <6>4 CASE RMRcvCommitMsg(rm) BY <3>1, <6>4 DEF Phase1, RMRcvCommitMsg, Arguments, PhaseArguments, ExistCommitMsg
          <6>5 CASE RMRcvAbortMsg(rm) BY <3>1, <6>5 DEF Phase1, RMRcvAbortMsg, Arguments, PhaseArguments, ExistAbortMsg
          <6> QED BY <6>1, <6>2, <6>3, <6>4, <6>5 DEF RMOp
        <5> QED BY <5>1, <5>2, <5>3 DEF Next
      <4>3 ~Phase2' \/ ~ExistAbortedRM'
        <5>1 ~TMCommit BY <3>1 DEF Phase1, TMCommit
        <5>2 CASE TMAbort BY <5>2, <3>1 DEF TMAbort, Phase1, Phase2
        <5>3 CASE ChooseRMOp
          <6> PICK rm \in RM: RMOp(rm) BY <5>3 DEF ChooseRMOp
          <6>1 CASE TMRcvPrepared(rm)
            <7>1 CASE tmPrepared \union {rm} = RM
              <8> SUFFICES \A rm2 \in RM: rmState'[rm2] # "aborted" BY DEF ExistAbortedRM
              <8> TAKE rm2 \in RM
              <8>1 CASE rm2 = rm
                <9>a rmState[rm] # "aborted" BY <3>1, <6>1 DEF PreparedOrAbort, Arguments, PhaseArguments, TMRcvPrepared
                <9> QED BY <9>a, <8>1, <1>T2, <6>1 DEF TMRcvPrepared
              <8>2 CASE rm2 # rm
                <9>a rm2 \in tmPrepared BY <8>2, <7>1
                <9>b [type |-> "prepared", rm |-> rm2] \in msgs BY <9>a, <3>1, <6>1 DEF TMPreparedOrder, Arguments, TMRcvPrepared
                <9>c rmState[rm2] = "prepared" BY <9>b, <6>1, <3>1 DEF RMPreparedOrder, Arguments, TMRcvPrepared, PhaseArguments
                <9> QED BY <9>c, <8>2, <6>1 DEF TMRcvPrepared
              <8> QED BY <8>1, <8>2
            <7>2 CASE tmPrepared \union {rm} # RM BY <7>2, <6>1 DEF Phase2, TMRcvPrepared
            <7> QED BY <7>1, <7>2, <1>T3
          <6>2 CASE RMPrepare(rm) BY <6>2, <3>1 DEF RMPrepare, Phase1, Phase2
          <6>3 CASE RMChooseToAbort(rm) BY <6>3, <3>1 DEF RMChooseToAbort, Phase1, Phase2
          <6>4 CASE RMRcvCommitMsg(rm) BY <6>4, <3>1 DEF RMRcvCommitMsg, Phase1, Phase2
          <6>5 CASE RMRcvAbortMsg(rm) BY <6>5, <3>1 DEF RMRcvAbortMsg, Phase1, Phase2
          <6> QED BY <6>1, <6>2, <6>3, <6>4, <6>5 DEF RMOp
        <5> QED BY <5>1, <5>2, <5>3 DEF Next
      <4>4 Phase2' => \A rm \in RM: rmState'[rm] # "working"
        <5>1 ~TMCommit BY <3>1 DEF Phase1, TMCommit, Phase2
        <5>2 CASE TMAbort BY <5>2, <3>1 DEF TMAbort, Phase1, Phase2
        <5>3 CASE ChooseRMOp
          <6> PICK rm \in RM: RMOp(rm) BY <5>3 DEF ChooseRMOp
          <6>1 CASE TMRcvPrepared(rm)
            <7>1 CASE tmPrepared \union {rm} = RM
              <8> SUFFICES \A rm2 \in RM: rmState'[rm2] # "working" OBVIOUS
              <8> TAKE rm2 \in RM
              <8>a [type |-> "prepared", rm |-> rm2] \in msgs
                <9>1 CASE rm2 = rm BY <6>1, <9>1 DEF TMRcvPrepared
                <9>2 CASE rm2 # rm
                  <10>a rm2 \in tmPrepared BY <7>1, <9>2
                  <10> QED  BY <10>a, <6>1 DEF Arguments, TMPreparedOrder, TMRcvPrepared
                <9> QED BY <9>1, <9>2
              <8>b rmState[rm2] = "prepared" BY <8>a, <3>1, <6>1, <1>T1 DEF RMPreparedOrder, Arguments, PhaseArguments, TMRcvPrepared
              <8> QED BY <8>b, <6>1 DEF TMRcvPrepared
            <7>2 CASE tmPrepared \union {rm} # RM BY <7>2, <6>1 DEF Phase2, TMRcvPrepared
            <7> QED BY <7>1, <7>2, <1>T3
          <6>2 CASE RMPrepare(rm) BY <6>2, <3>1 DEF RMPrepare, Phase1, Phase2
          <6>3 CASE RMChooseToAbort(rm) BY <6>3, <3>1 DEF RMChooseToAbort, Phase1, Phase2
          <6>4 CASE RMRcvCommitMsg(rm) BY <6>4, <3>1 DEF RMRcvCommitMsg, Phase1, Phase2
          <6>5 CASE RMRcvAbortMsg(rm) BY <6>5, <3>1 DEF RMRcvAbortMsg, Phase1, Phase2
          <6> QED BY <6>1, <6>2, <6>3, <6>4, <6>5 DEF RMOp
        <5> QED BY <5>1, <5>2, <5>3 DEF Next
      <4>5 ~ExistAbortedRM' \/ ~ExistCommittedRM'
        <5>1 ~TMCommit BY <3>1 DEF Phase1, TMCommit
        <5>2 CASE TMAbort BY <4>b, <5>2 DEF TMAbort, ExistCommittedRM
        <5>3 CASE ChooseRMOp
          <6> PICK rm \in RM: RMOp(rm) BY <5>3 DEF ChooseRMOp
          <6>1 CASE TMRcvPrepared(rm) BY <6>1 DEF TMRcvPrepared, Arguments, PhaseArguments, ExistAbortedRM, ExistCommittedRM
          <6>2 CASE RMPrepare(rm)
            <7> SUFFICES \A rm2 \in RM: rmState'[rm2] # "committed" BY DEF ExistCommittedRM
            <7> TAKE rm2 \in RM
            <7>1 CASE rm2 = rm BY <7>1, <6>2, <1>T2 DEF RMPrepare
            <7>2 CASE rm2 # rm BY <7>2, <6>2, <4>b, <1>T2 DEF RMPrepare, ExistCommittedRM
            <7> QED BY <7>1, <7>2
          <6>3 CASE RMChooseToAbort(rm)
            <7> SUFFICES \A rm2 \in RM: rmState'[rm2] # "committed" BY DEF ExistCommittedRM
            <7> TAKE rm2 \in RM
            <7>1 CASE rm2 = rm BY <7>1, <6>3, <1>T2 DEF RMChooseToAbort
            <7>2 CASE rm2 # rm BY <7>2, <6>3, <4>b, <1>T2 DEF RMChooseToAbort, ExistCommittedRM
            <7> QED BY <7>1, <7>2
          <6>4 ~RMRcvCommitMsg(rm) BY <4>a DEF RMRcvCommitMsg
          <6>5 CASE RMRcvAbortMsg(rm)
            <7> SUFFICES \A rm2 \in RM: rmState'[rm2] # "committed" BY DEF ExistCommittedRM
            <7> TAKE rm2 \in RM
            <7>1 CASE rm2 = rm BY <7>1, <6>5, <1>T2 DEF RMRcvAbortMsg
            <7>2 CASE rm2 # rm BY <7>2, <6>5, <4>b, <1>T2 DEF RMRcvAbortMsg, ExistCommittedRM
            <7> QED BY <7>1, <7>2
          <6> QED BY <6>1, <6>2, <6>3, <6>4, <6>5 DEF RMOp
        <5> QED BY <5>1, <5>2, <5>3 DEF Next
      <4> QED BY <4>1, <4>2, <4>3, <4>4, <4>5 DEF PhaseArguments
    <3>2 CASE Phase2
      <4>a tmPrepared = RM BY <3>2 DEF Phase2
      <4>b ExistAbortedRM => ExistAbortMsg BY <3>2 DEF Arguments, PhaseArguments
      <4>c \A rm \in RM: rmState[rm] # "working" BY <3>2 DEF Arguments, PhaseArguments
      <4>1 ~Phase1'
        <5>1 CASE TMCommit BY <4>a, <5>1 DEF TMCommit, Phase1
        <5>2 CASE TMAbort BY <4>a, <5>2 DEF TMAbort, Phase1
        <5>3 CASE ChooseRMOp
          <6> PICK rm \in RM: RMOp(rm) BY <5>3 DEF ChooseRMOp
          <6>1 CASE TMRcvPrepared(rm)  BY <4>a, <6>1 DEF TMRcvPrepared, Phase1
          <6>2 CASE RMPrepare(rm) BY <4>a, <6>2 DEF RMPrepare, Phase1
          <6>3 CASE RMChooseToAbort(rm) BY <4>a, <6>3 DEF RMChooseToAbort, Phase1
          <6>4 CASE RMRcvCommitMsg(rm) BY <4>a, <6>4 DEF RMRcvCommitMsg, Phase1
          <6>5 CASE RMRcvAbortMsg(rm) BY <4>a, <6>5 DEF RMRcvAbortMsg, Phase1
          <6> QED BY <6>1, <6>2, <6>3, <6>4, <6>5 DEF RMOp
        <5> QED BY <5>1, <5>2, <5>3 DEF Next
      <4>2 ExistAbortedRM' => ExistAbortMsg'
        <5>1 CASE TMCommit
          <6>1 CASE ExistAbortedRM BY <6>1, <4>b, <5>1 DEF ExistAbortedRM, ExistAbortMsg, TMCommit
          <6>2 CASE ~ExistAbortedRM BY <6>2, <5>1 DEF ExistAbortedRM, TMCommit
          <6> QED BY <6>1, <6>2
        <5>2 CASE TMAbort
          <6>1 CASE ExistAbortedRM BY <6>1, <4>b, <5>2 DEF ExistAbortedRM, ExistAbortMsg, TMAbort
          <6>2 CASE ~ExistAbortedRM BY <6>2, <5>2 DEF ExistAbortedRM, TMAbort
          <6> QED BY <6>1, <6>2
        <5>3 CASE ChooseRMOp
          <6> PICK rm \in RM: RMOp(rm) BY <5>3 DEF ChooseRMOp
          <6>1 CASE TMRcvPrepared(rm)
            <7>1 CASE ExistAbortedRM BY <7>1, <4>b, <6>1 DEF ExistAbortedRM, ExistAbortMsg, TMRcvPrepared
            <7>2 CASE ~ExistAbortedRM BY <7>2, <6>1 DEF ExistAbortedRM, TMRcvPrepared
            <7> QED BY <7>1, <7>2
          <6>2 CASE RMPrepare(rm)
            <7>1 CASE ExistAbortedRM BY <7>1, <4>b, <6>2 DEF ExistAbortedRM, ExistAbortMsg, RMPrepare
            <7>2 CASE ~ExistAbortedRM
              <8> SUFFICES \A rm2 \in RM: rmState'[rm2] # "aborted" BY DEF ExistAbortedRM
              <8> TAKE rm2 \in RM
              <8>1 CASE rm2 = rm BY <8>1, <1>T2, <7>2, <6>2 DEF ExistAbortedRM, RMPrepare
              <8>2 CASE rm2 # rm BY <8>2, <1>T2, <7>2, <6>2 DEF ExistAbortedRM, RMPrepare
              <8> QED BY <8>1, <8>2
            <7> QED BY <7>1, <7>2
          <6>3 ~RMChooseToAbort(rm) BY <3>2 DEF RMChooseToAbort, Arguments, PhaseArguments
          <6>4 CASE RMRcvCommitMsg(rm)
            <7> SUFFICES \A rm2 \in RM: rmState'[rm2] # "aborted" BY DEF ExistAbortedRM
            <7> TAKE rm2 \in RM
            <7>a ~ExistAbortedRM BY <6>4, <4>b DEF RMRcvCommitMsg, ExistAbortMsg, Arguments
            <7>1 CASE rm2 = rm BY <7>1, <6>4, <1>T2 DEF RMRcvCommitMsg
            <7>2 CASE rm2 # rm BY <7>2, <6>4, <1>T2, <7>a DEF RMRcvCommitMsg, ExistAbortedRM
            <7> QED BY <7>1, <7>2
          <6>5 CASE RMRcvAbortMsg(rm) BY <6>5 DEF RMRcvAbortMsg, ExistAbortMsg
          <6> QED BY <6>1, <6>2, <6>3, <6>4, <6>5 DEF RMOp
        <5> QED BY <5>1, <5>2, <5>3 DEF Next
      <4>3 \A rm2 \in RM: rmState'[rm2] # "working"
        <5> TAKE rm2 \in RM
        <5>a rmState[rm2] # "working" BY <4>c
        <5>1 CASE TMCommit BY <5>1, <5>a DEF TMCommit
        <5>2 CASE TMAbort BY <5>2, <5>a DEF TMAbort
        <5>3 CASE ChooseRMOp
          <6> PICK rm \in RM: RMOp(rm) BY <5>3 DEF ChooseRMOp
          <6>1 CASE TMRcvPrepared(rm) BY <6>1, <5>a DEF TMRcvPrepared
          <6>2 CASE RMPrepare(rm)
            <7>1 CASE rm2 = rm BY <7>1, <6>2, <1>T2 DEF RMPrepare
            <7>2 CASE rm2 # rm BY <7>2, <5>a, <6>2, <1>T2 DEF RMPrepare
            <7> QED BY <7>1, <7>2
          <6>3 CASE RMChooseToAbort(rm)
            <7>1 CASE rm2 = rm BY <7>1, <6>3, <1>T2 DEF RMChooseToAbort
            <7>2 CASE rm2 # rm BY <7>2, <5>a, <6>3, <1>T2 DEF RMChooseToAbort
            <7> QED BY <7>1, <7>2
          <6>4 CASE RMRcvCommitMsg(rm)
            <7>1 CASE rm2 = rm BY <7>1, <6>4, <1>T2 DEF RMRcvCommitMsg
            <7>2 CASE rm2 # rm BY <7>2, <5>a, <6>4, <1>T2 DEF RMRcvCommitMsg
            <7> QED BY <7>1, <7>2
          <6>5 CASE RMRcvAbortMsg(rm)
            <7>1 CASE rm2 = rm BY <7>1, <6>5, <1>T2 DEF RMRcvAbortMsg
            <7>2 CASE rm2 # rm BY <7>2, <5>a, <6>5, <1>T2 DEF RMRcvAbortMsg
            <7> QED BY <7>1, <7>2
          <6> QED BY <6>1, <6>2, <6>3, <6>4, <6>5 DEF RMOp
        <5> QED BY <5>1, <5>2, <5>3 DEF Next
      <4>4 ~ExistAbortedRM' \/ ~ExistCommittedRM'
        <5>1 CASE TMCommit
          <6> SUFFICES \A rm \in RM: rmState'[rm] # "aborted" BY DEF ExistAbortedRM
          <6> TAKE rm \in RM
          <6>a ~ExistAbortMsg BY <5>1 DEF TMCommit, Arguments
          <6>b ~ExistAbortedRM BY <6>a, <4>b
          <6>c rmState[rm] # "aborted" BY <6>b DEF ExistAbortedRM
          <6> QED BY <6>c, <5>1 DEF TMCommit
        <5>2 CASE TMAbort
          <6> SUFFICES \A rm \in RM: rmState'[rm] # "committed" BY DEF ExistCommittedRM
          <6> TAKE rm \in RM
          <6>a ~ExistCommitMsg BY <5>2 DEF TMAbort, Arguments
          <6>b ~ExistCommittedRM BY <6>a DEF Arguments
          <6>c rmState[rm] # "committed" BY <6>b DEF ExistCommittedRM
          <6> QED BY <6>c, <5>2 DEF TMAbort
        <5>3 CASE ChooseRMOp
          <6> PICK rm \in RM: RMOp(rm) BY <5>3 DEF ChooseRMOp
          <6>1 CASE TMRcvPrepared(rm) BY <6>1 DEF TMRcvPrepared, Arguments, PhaseArguments, ExistAbortedRM, ExistCommittedRM
          <6>2 ~RMPrepare(rm) BY <4>c DEF RMPrepare
          <6>3 ~RMChooseToAbort(rm) BY <4>c DEF RMChooseToAbort
          <6>4 CASE RMRcvCommitMsg(rm)
            <7> SUFFICES \A rm2 \in RM: rmState'[rm2] # "aborted" BY DEF ExistAbortedRM
            <7> TAKE rm2 \in RM
            <7>a ~ExistAbortMsg BY <6>4 DEF RMRcvCommitMsg, Arguments
            <7>b ~ExistAbortedRM BY <7>a, <3>2 DEF Arguments, PhaseArguments
            <7>1 CASE rm2 = rm BY <7>1, <6>4, <1>T2 DEF RMRcvCommitMsg
            <7>2 CASE rm2 # rm BY <7>b, <7>2, <6>4, <1>T2 DEF RMRcvCommitMsg, ExistAbortedRM
            <7> QED BY <7>1, <7>2
          <6>5 CASE RMRcvAbortMsg(rm)
            <7> SUFFICES \A rm2 \in RM: rmState'[rm2] # "committed" BY DEF ExistCommittedRM
            <7> TAKE rm2 \in RM
            <7>a ~ExistCommitMsg BY <6>5 DEF RMRcvAbortMsg, Arguments
            <7>b ~ExistCommittedRM BY <7>a, <3>2 DEF Arguments, PhaseArguments
            <7>1 CASE rm2 = rm BY <7>1, <6>5, <1>T2 DEF RMRcvAbortMsg
            <7>2 CASE rm2 # rm BY <7>b, <7>2, <6>5, <1>T2 DEF RMRcvAbortMsg, ExistCommittedRM
            <7> QED BY <7>1, <7>2
          <6> QED BY <6>1, <6>2, <6>3, <6>4, <6>5 DEF RMOp
        <5> QED BY <5>1, <5>2, <5>3 DEF Next
      <4> QED BY <4>1, <4>2, <4>3, <4>4 DEF PhaseArguments
    <3> QED BY <3>1, <3>2 DEF Phase1, Phase2
  <2> QED BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF Arguments
<1> QED BY <1>1, <1>2, PTL

=============================================================================
\* Modification History
\* Last modified Wed Jan 17 15:42:37 CST 2018 by functioner
\* Created Fri Dec 22 20:05:29 CST 2017 by functioner
