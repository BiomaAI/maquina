import FoundrySim.Workcell
import Maquina.Command

/-!
# Foundry Control Room

A bounded command graph over one authoritative account state and two isolated
Foundry station runtimes. Operators can assign the unique Body, create
backpressure, coordinate simultaneous orders, recover from a deterministic
failure, or conserve resources. The graph is game-owned; its topology and
replay obligations are checked by `Maquina.CommandGraph`.
-/

namespace Maquina.Games.Foundry.ControlRoom

open Refuel Simulation

def operatorActor : ActorId := ⟨10⟩

def initialState : Workcell.State where
  accounts := concurrencyWorld
  primary := Workcell.initialState.primary
  secondary := Workcell.initialState.secondary
  primaryBacked := MachineCustody.backed_empty concurrencyWorld machineAccount
  secondaryBacked :=
    MachineCustody.backed_empty concurrencyWorld Workcell.secondaryMachineAccount

abbrev Snapshot := TimelineSnapshot Workcell.executor initialState

def initialTimeline : TimelineState Workcell.State Workcell.Intent where
  application := initialState
  tick := ⟨0⟩
  pending := []
  pendingIdsUnique := by simp
  nextEventSequence := 0

def rootSnapshot : Snapshot where
  id := ⟨0⟩
  timeline := initialTimeline
  history := []
  replayExact := rfl

def intent
    (station : Workcell.Station)
    (proposal : OperationProposal schema operationLanguage) : Workcell.Intent where
  station
  operation := Workcell.proposalFor station proposal

def enter (station : Workcell.Station) := intent station Refuel.enterMachine
def reserve (station : Workcell.Station) := intent station Refuel.reserveFuel
def dispatch (station : Workcell.Station) := intent station Refuel.dispatchRefuel
def advance (station : Workcell.Station) := intent station Refuel.advanceRefuel
def complete (station : Workcell.Station) := intent station Refuel.completeRefuel
def collect (station : Workcell.Station) := intent station Refuel.collectRefuel
def cancel (station : Workcell.Station) := intent station Refuel.cancelQueuedRefuel
def leave (station : Workcell.Station) := intent station Refuel.leaveMachine
def stop (station : Workcell.Station) := intent station Refuel.stop
def start (station : Workcell.Station) := intent station Refuel.start
def fail (station : Workcell.Station) := intent station Refuel.fail
def repair (station : Workcell.Station) := intent station Refuel.repair

def candidate (id : Nat) (payload : Workcell.Intent) :
    CommandCandidate Workcell.Intent where
  id := ⟨id⟩
  actor := operatorActor
  payload

def order
    (id major minor : Nat)
    (payload : Workcell.Intent) : CommandOrder Workcell.Intent where
  id := ⟨id⟩
  actor := operatorActor
  arbitration := ⟨major, minor⟩
  payload

def singletonSet
    (id major minor : Nat)
    (payload : Workcell.Intent) : OrderSet Workcell.Intent where
  orders := [order id major minor payload]
  idsUnique := by simp

def primaryEnterCandidate := candidate 100 (enter .primary)
def secondaryEnterCandidate := candidate 101 (enter .secondary)
def prematureDispatchCandidate := candidate 102 (dispatch .primary)

def primaryReserveCandidate := candidate 110 (reserve .primary)
def primaryLeaveCandidate := candidate 111 (leave .primary)
def primaryStopCandidate := candidate 112 (stop .primary)
def primaryCompetingEnterCandidate := candidate 113 (enter .secondary)

def secondaryReserveCandidate := candidate 120 (reserve .secondary)
def secondaryLeaveCandidate := candidate 121 (leave .secondary)
def secondaryStopCandidate := candidate 122 (stop .secondary)
def secondaryCompetingEnterCandidate := candidate 123 (enter .primary)

def primaryDispatchCandidate := candidate 130 (dispatch .primary)
def primaryQueuedLeaveCandidate := candidate 131 (leave .primary)
def primaryCancelCandidate := candidate 132 (cancel .primary)
def primaryPrematureFailCandidate := candidate 133 (fail .primary)

def secondaryDispatchCandidate := candidate 140 (dispatch .secondary)
def secondaryQueuedLeaveCandidate := candidate 141 (leave .secondary)
def secondaryCancelCandidate := candidate 142 (cancel .secondary)
def secondaryPrematureFailCandidate := candidate 143 (fail .secondary)

def primaryEnterSet := singletonSet 100 10 0 (enter .primary)
def secondaryEnterSet := singletonSet 101 10 0 (enter .secondary)
def primaryReserveSet := singletonSet 110 10 0 (reserve .primary)
def secondaryReserveSet := singletonSet 120 10 0 (reserve .secondary)
def primaryLeaveSet := singletonSet 111 10 0 (leave .primary)
def secondaryLeaveSet := singletonSet 121 10 0 (leave .secondary)
def primaryStopSet := singletonSet 112 10 0 (stop .primary)
def secondaryStopSet := singletonSet 122 10 0 (stop .secondary)
def primaryDispatchSet := singletonSet 130 10 0 (dispatch .primary)
def secondaryDispatchSet := singletonSet 140 10 0 (dispatch .secondary)
def primaryQueuedLeaveSet := singletonSet 131 10 0 (leave .primary)
def secondaryQueuedLeaveSet := singletonSet 141 10 0 (leave .secondary)
def primaryCancelSet := singletonSet 132 10 0 (cancel .primary)
def secondaryCancelSet := singletonSet 142 10 0 (cancel .secondary)

def primaryDispatchAndLeaveSet : OrderSet Workcell.Intent where
  orders :=
    [order 130 10 0 (dispatch .primary),
     order 131 20 0 (leave .primary)]
  idsUnique := by decide

def secondaryDispatchAndLeaveSet : OrderSet Workcell.Intent where
  orders :=
    [order 140 10 0 (dispatch .secondary),
     order 141 20 0 (leave .secondary)]
  idsUnique := by decide

def automaticSet
    (id major : Nat)
    (payload : Workcell.Intent) : OrderSet Workcell.Intent :=
  singletonSet id major 0 payload

/-! ## Immutable fork construction -/

def primaryEntered :=
  resolveSnapshotOrderSet Workcell.executor initialState rootSnapshot ⟨1⟩ rfl
    primaryEnterSet
def secondaryEntered :=
  resolveSnapshotOrderSet Workcell.executor initialState rootSnapshot ⟨2⟩ rfl
    secondaryEnterSet

def primaryAssigned : Snapshot := primaryEntered.child
def secondaryAssigned : Snapshot := secondaryEntered.child

def primaryQueuedRun :=
  resolveSnapshotOrderSet Workcell.executor initialState primaryAssigned ⟨10⟩ rfl
    primaryReserveSet
def secondaryQueuedRun :=
  resolveSnapshotOrderSet Workcell.executor initialState secondaryAssigned ⟨20⟩ rfl
    secondaryReserveSet

def primaryQueued : Snapshot := primaryQueuedRun.child
def secondaryQueued : Snapshot := secondaryQueuedRun.child

/-! Productive branches. -/

def primaryProductiveDispatch :=
  resolveSnapshotOrderSet Workcell.executor initialState primaryQueued ⟨110⟩ rfl
    primaryDispatchSet
def primaryProductiveAdvance :=
  resolveSnapshotOrderSet Workcell.executor initialState primaryProductiveDispatch.child
    ⟨111⟩ rfl (automaticSet 900 10 (advance .primary))
def primaryProductiveComplete :=
  resolveSnapshotOrderSet Workcell.executor initialState primaryProductiveAdvance.child
    ⟨112⟩ rfl (automaticSet 901 10 (complete .primary))
def primaryProductiveLeave :=
  resolveSnapshotOrderSet Workcell.executor initialState primaryProductiveComplete.child
    ⟨113⟩ rfl (automaticSet 902 10 (leave .primary))
def primaryProductiveCollect :=
  resolveSnapshotOrderSet Workcell.executor initialState primaryProductiveLeave.child
    ⟨11⟩ rfl (automaticSet 903 10 (collect .primary))
def primaryProductive : Snapshot := primaryProductiveCollect.child

def secondaryProductiveDispatch :=
  resolveSnapshotOrderSet Workcell.executor initialState secondaryQueued ⟨210⟩ rfl
    secondaryDispatchSet
def secondaryProductiveAdvance :=
  resolveSnapshotOrderSet Workcell.executor initialState secondaryProductiveDispatch.child
    ⟨211⟩ rfl (automaticSet 910 10 (advance .secondary))
def secondaryProductiveComplete :=
  resolveSnapshotOrderSet Workcell.executor initialState secondaryProductiveAdvance.child
    ⟨212⟩ rfl (automaticSet 911 10 (complete .secondary))
def secondaryProductiveLeave :=
  resolveSnapshotOrderSet Workcell.executor initialState secondaryProductiveComplete.child
    ⟨213⟩ rfl (automaticSet 912 10 (leave .secondary))
def secondaryProductiveCollect :=
  resolveSnapshotOrderSet Workcell.executor initialState secondaryProductiveLeave.child
    ⟨21⟩ rfl (automaticSet 913 10 (collect .secondary))
def secondaryProductive : Snapshot := secondaryProductiveCollect.child

/-! Simultaneous dispatch/departure produces a deterministic conflict and outage. -/

def primaryRiskDispatch :=
  resolveSnapshotOrderSet Workcell.executor initialState primaryQueued ⟨120⟩ rfl
    primaryDispatchAndLeaveSet
def primaryRiskFail :=
  resolveSnapshotOrderSet Workcell.executor initialState primaryRiskDispatch.child
    ⟨121⟩ rfl (automaticSet 920 10 (fail .primary))
def primaryRiskRepair :=
  resolveSnapshotOrderSet Workcell.executor initialState primaryRiskFail.child
    ⟨122⟩ rfl (automaticSet 921 10 (repair .primary))
def primaryRiskStart :=
  resolveSnapshotOrderSet Workcell.executor initialState primaryRiskRepair.child
    ⟨123⟩ rfl (automaticSet 922 10 (start .primary))
def primaryRiskLeave :=
  resolveSnapshotOrderSet Workcell.executor initialState primaryRiskStart.child
    ⟨12⟩ rfl (automaticSet 923 10 (leave .primary))
def primaryRecovered : Snapshot := primaryRiskLeave.child

def secondaryRiskDispatch :=
  resolveSnapshotOrderSet Workcell.executor initialState secondaryQueued ⟨220⟩ rfl
    secondaryDispatchAndLeaveSet
def secondaryRiskFail :=
  resolveSnapshotOrderSet Workcell.executor initialState secondaryRiskDispatch.child
    ⟨221⟩ rfl (automaticSet 930 10 (fail .secondary))
def secondaryRiskRepair :=
  resolveSnapshotOrderSet Workcell.executor initialState secondaryRiskFail.child
    ⟨222⟩ rfl (automaticSet 931 10 (repair .secondary))
def secondaryRiskStart :=
  resolveSnapshotOrderSet Workcell.executor initialState secondaryRiskRepair.child
    ⟨223⟩ rfl (automaticSet 932 10 (start .secondary))
def secondaryRiskLeave :=
  resolveSnapshotOrderSet Workcell.executor initialState secondaryRiskStart.child
    ⟨22⟩ rfl (automaticSet 933 10 (leave .secondary))
def secondaryRecovered : Snapshot := secondaryRiskLeave.child

/-! Backpressure, cancellation, conservation, and maintenance branches. -/

def primaryBacklogRun :=
  resolveSnapshotOrderSet Workcell.executor initialState primaryQueued ⟨13⟩ rfl
    primaryQueuedLeaveSet
def secondaryBacklogRun :=
  resolveSnapshotOrderSet Workcell.executor initialState secondaryQueued ⟨23⟩ rfl
    secondaryQueuedLeaveSet
def primaryBacklog : Snapshot := primaryBacklogRun.child
def secondaryBacklog : Snapshot := secondaryBacklogRun.child

def primaryCancelRun :=
  resolveSnapshotOrderSet Workcell.executor initialState primaryQueued ⟨140⟩ rfl
    primaryCancelSet
def primaryCancelLeave :=
  resolveSnapshotOrderSet Workcell.executor initialState primaryCancelRun.child ⟨14⟩ rfl
    (automaticSet 940 10 (leave .primary))
def primaryConserved : Snapshot := primaryCancelLeave.child

def secondaryCancelRun :=
  resolveSnapshotOrderSet Workcell.executor initialState secondaryQueued ⟨240⟩ rfl
    secondaryCancelSet
def secondaryCancelLeave :=
  resolveSnapshotOrderSet Workcell.executor initialState secondaryCancelRun.child ⟨24⟩ rfl
    (automaticSet 941 10 (leave .secondary))
def secondaryConserved : Snapshot := secondaryCancelLeave.child

def primaryDeferredRun :=
  resolveSnapshotOrderSet Workcell.executor initialState primaryAssigned ⟨15⟩ rfl
    primaryLeaveSet
def secondaryDeferredRun :=
  resolveSnapshotOrderSet Workcell.executor initialState secondaryAssigned ⟨25⟩ rfl
    secondaryLeaveSet
def primaryDeferred : Snapshot := primaryDeferredRun.child
def secondaryDeferred : Snapshot := secondaryDeferredRun.child

def primaryMaintenanceStop :=
  resolveSnapshotOrderSet Workcell.executor initialState primaryAssigned ⟨160⟩ rfl
    primaryStopSet
def primaryMaintenanceStart :=
  resolveSnapshotOrderSet Workcell.executor initialState primaryMaintenanceStop.child
    ⟨161⟩ rfl (automaticSet 950 10 (start .primary))
def primaryMaintenanceLeave :=
  resolveSnapshotOrderSet Workcell.executor initialState primaryMaintenanceStart.child
    ⟨16⟩ rfl (automaticSet 951 10 (leave .primary))
def primaryMaintained : Snapshot := primaryMaintenanceLeave.child

def secondaryMaintenanceStop :=
  resolveSnapshotOrderSet Workcell.executor initialState secondaryAssigned ⟨260⟩ rfl
    secondaryStopSet
def secondaryMaintenanceStart :=
  resolveSnapshotOrderSet Workcell.executor initialState secondaryMaintenanceStop.child
    ⟨261⟩ rfl (automaticSet 960 10 (start .secondary))
def secondaryMaintenanceLeave :=
  resolveSnapshotOrderSet Workcell.executor initialState secondaryMaintenanceStart.child
    ⟨26⟩ rfl (automaticSet 961 10 (leave .secondary))
def secondaryMaintained : Snapshot := secondaryMaintenanceLeave.child

/-! ## Game-owned command metadata -/

inductive Outcome where
  | active
  | productive
  | recovered
  | backlog
  | conserved
  | deferred
  | maintained
  deriving DecidableEq, Repr

structure CandidateSpec where
  candidate : CommandCandidate Workcell.Intent
  label : String
  detail : String

structure Node where
  snapshot : Snapshot
  title : String
  summary : String
  outcome : Outcome
  candidates : List CandidateSpec
  candidateIdsUnique :
    (candidates.map fun spec => spec.candidate.id).Nodup

def rootNode : Node where
  snapshot := rootSnapshot
  title := "Shift online"
  summary := "Assign the unique operator Body to one station before releasing work."
  outcome := .active
  candidates :=
    [{ candidate := primaryEnterCandidate
       label := "Staff primary station"
       detail := "Transfer the unique Body into Primary custody." },
     { candidate := secondaryEnterCandidate
       label := "Staff secondary station"
       detail := "Transfer the unique Body into Secondary custody." },
     { candidate := prematureDispatchCandidate
       label := "Dispatch without backlog"
       detail := "Inspect the complete rejection for an empty input queue." }]
  candidateIdsUnique := by decide

def assignedNode
    (station : Workcell.Station)
    (snapshot : Snapshot) : Node :=
  let primary := station = .primary
  let reserveCandidate := if primary then primaryReserveCandidate else secondaryReserveCandidate
  let leaveCandidate := if primary then primaryLeaveCandidate else secondaryLeaveCandidate
  let stopCandidate := if primary then primaryStopCandidate else secondaryStopCandidate
  let competingCandidate :=
    if primary then primaryCompetingEnterCandidate else secondaryCompetingEnterCandidate
  { snapshot
    title := if primary then "Primary staffed" else "Secondary staffed"
    summary := "Queue a service lot, release the Body, or take an idle maintenance window."
    outcome := .active
    candidates :=
      [{ candidate := reserveCandidate
         label := "Queue fuel service"
         detail := "Reserve ten liters and occupy the station input queue." },
       { candidate := leaveCandidate
         label := "Release operator"
         detail := "Return the unique Body without starting work." },
       { candidate := stopCandidate
         label := "Maintenance window"
         detail := "Stop while idle, restart deterministically, then release the Body." },
       { candidate := competingCandidate
         label := "Staff the other station too"
         detail := "Inspect unique Body contention with no successor mutation." }]
    candidateIdsUnique := by cases station <;> decide }

def primaryAssignedNode := assignedNode .primary primaryAssigned
def secondaryAssignedNode := assignedNode .secondary secondaryAssigned

def queuedNode
    (station : Workcell.Station)
    (snapshot : Snapshot) : Node :=
  let primary := station = .primary
  let dispatchCandidate := if primary then primaryDispatchCandidate else secondaryDispatchCandidate
  let leaveCandidate :=
    if primary then primaryQueuedLeaveCandidate else secondaryQueuedLeaveCandidate
  let cancelCandidate := if primary then primaryCancelCandidate else secondaryCancelCandidate
  let failCandidate :=
    if primary then primaryPrematureFailCandidate else secondaryPrematureFailCandidate
  { snapshot
    title := if primary then "Primary backlog ready" else "Secondary backlog ready"
    summary := "Dispatch, coordinate departure, strand backlog, or cancel cleanly."
    outcome := .active
    candidates :=
      [{ candidate := dispatchCandidate
         label := "Dispatch service"
         detail := "Move the reserved lot into active processing." },
       { candidate := leaveCandidate
         label := "Release during dispatch"
         detail := "Select with Dispatch to expose deterministic same-tick conflict." },
       { candidate := cancelCandidate
         label := "Cancel backlog"
         detail := "Return reserved fuel, then release the Body." },
       { candidate := failCandidate
         label := "Report active failure"
         detail := "Inspect rejection because queued work is not active work." }]
    candidateIdsUnique := by cases station <;> decide }

def primaryQueuedNode := queuedNode .primary primaryQueued
def secondaryQueuedNode := queuedNode .secondary secondaryQueued

def terminalNode
    (snapshot : Snapshot)
    (title summary : String)
    (outcome : Outcome) : Node where
  snapshot
  title
  summary
  outcome
  candidates := []
  candidateIdsUnique := by simp

def primaryProductiveNode := terminalNode primaryProductive "Primary lot delivered"
  "Ten liters crossed custody and queues; service credits reached both recipients."
  .productive
def secondaryProductiveNode := terminalNode secondaryProductive "Secondary lot delivered"
  "The same account protocol completed through the isolated Secondary runtime."
  .productive
def primaryRecoveredNode := terminalNode primaryRecovered "Primary outage recovered"
  "Dispatch won the tick, departure lost, failure returned reservations, and repair restored service."
  .recovered
def secondaryRecoveredNode := terminalNode secondaryRecovered "Secondary outage recovered"
  "Canonical arbitration and repair produced the same deterministic recovery policy."
  .recovered
def primaryBacklogNode := terminalNode primaryBacklog "Primary backlog stranded"
  "The Body was released while a reserved service lot remained queued."
  .backlog
def secondaryBacklogNode := terminalNode secondaryBacklog "Secondary backlog stranded"
  "The station preserved queued fuel but cannot dispatch without the operator returning."
  .backlog
def primaryConservedNode := terminalNode primaryConserved "Primary order canceled"
  "Reserved fuel returned to the provider and the unique Body returned to the worker."
  .conserved
def secondaryConservedNode := terminalNode secondaryConserved "Secondary order canceled"
  "Cancellation conserved shared resources without producing service credits."
  .conserved
def primaryDeferredNode := terminalNode primaryDeferred "Primary work deferred"
  "No service lot was reserved; every shared resource remains available for a later shift."
  .deferred
def secondaryDeferredNode := terminalNode secondaryDeferred "Secondary work deferred"
  "The operator released the station before consuming queue capacity."
  .deferred
def primaryMaintainedNode := terminalNode primaryMaintained "Primary maintained"
  "An idle stop/start cycle completed and the Body returned without consuming fuel."
  .maintained
def secondaryMaintainedNode := terminalNode secondaryMaintained "Secondary maintained"
  "The isolated Secondary runtime completed the same safe maintenance policy."
  .maintained

def nodes : List Node :=
  [rootNode, primaryAssignedNode, secondaryAssignedNode,
   primaryQueuedNode, secondaryQueuedNode,
   primaryProductiveNode, secondaryProductiveNode,
   primaryRecoveredNode, secondaryRecoveredNode,
   primaryBacklogNode, secondaryBacklogNode,
   primaryConservedNode, secondaryConservedNode,
   primaryDeferredNode, secondaryDeferredNode,
   primaryMaintainedNode, secondaryMaintainedNode]

/-! ## Generic proof-carrying graph instantiation -/

abbrev ProvedNode := Maquina.CommandGraphNode Workcell.executor initialState

def provedNode (node : Node) : ProvedNode :=
  assessCommandGraphNode Workcell.executor initialState node.snapshot
    (node.candidates.map fun spec => spec.candidate) (by
      simpa [List.map_map, Function.comp_def] using node.candidateIdsUnique)

def provedRootNode := provedNode rootNode
def provedPrimaryAssignedNode := provedNode primaryAssignedNode
def provedSecondaryAssignedNode := provedNode secondaryAssignedNode
def provedPrimaryQueuedNode := provedNode primaryQueuedNode
def provedSecondaryQueuedNode := provedNode secondaryQueuedNode
def provedPrimaryProductiveNode := provedNode primaryProductiveNode
def provedSecondaryProductiveNode := provedNode secondaryProductiveNode
def provedPrimaryRecoveredNode := provedNode primaryRecoveredNode
def provedSecondaryRecoveredNode := provedNode secondaryRecoveredNode
def provedPrimaryBacklogNode := provedNode primaryBacklogNode
def provedSecondaryBacklogNode := provedNode secondaryBacklogNode
def provedPrimaryConservedNode := provedNode primaryConservedNode
def provedSecondaryConservedNode := provedNode secondaryConservedNode
def provedPrimaryDeferredNode := provedNode primaryDeferredNode
def provedSecondaryDeferredNode := provedNode secondaryDeferredNode
def provedPrimaryMaintainedNode := provedNode primaryMaintainedNode
def provedSecondaryMaintainedNode := provedNode secondaryMaintainedNode

def provedNodes : List ProvedNode :=
  [provedRootNode, provedPrimaryAssignedNode, provedSecondaryAssignedNode,
   provedPrimaryQueuedNode, provedSecondaryQueuedNode,
   provedPrimaryProductiveNode, provedSecondaryProductiveNode,
   provedPrimaryRecoveredNode, provedSecondaryRecoveredNode,
   provedPrimaryBacklogNode, provedSecondaryBacklogNode,
   provedPrimaryConservedNode, provedSecondaryConservedNode,
   provedPrimaryDeferredNode, provedSecondaryDeferredNode,
   provedPrimaryMaintainedNode, provedSecondaryMaintainedNode]

abbrev ProvedResolution :=
  Maquina.CommandGraphResolution Workcell.executor initialState provedNodes

def provedTick
    (parent : Snapshot)
    (resolved : ResolvedSnapshotOrderSet Workcell.executor initialState parent) :
    Maquina.CommandGraphStep Workcell.executor initialState :=
  commandGraphStep Workcell.executor initialState parent resolved

structure Resolution where
  proof : ProvedResolution
  label : String
  summary : String
  automaticOrders : List String

def resolutions : List Resolution :=
  [{ proof :=
       { id := 0
         source := provedRootNode
         target := provedPrimaryAssignedNode
         sourceMember := by simp [provedNodes]
         targetMember := by simp [provedNodes]
         actionIds := [primaryEnterCandidate.id]
         actionIdsNonempty := by decide
         actionIdsUnique := by decide
         actionsAccepted := by native_decide
         steps := [provedTick rootSnapshot primaryEntered]
         stepsNonempty := by decide
         firstStepActionsExact := by native_decide
         stepsConnect := by
           simp only [CommandGraphStepsConnect]
           exact ⟨SameSnapshotData.refl rootSnapshot,
             SameSnapshotData.refl primaryAssigned⟩ }
     label := "Staff Primary"
     summary := "Assign the unique Body to the Primary station."
     automaticOrders := [] },
   { proof :=
       { id := 1
         source := provedRootNode
         target := provedSecondaryAssignedNode
         sourceMember := by simp [provedNodes]
         targetMember := by simp [provedNodes]
         actionIds := [secondaryEnterCandidate.id]
         actionIdsNonempty := by decide
         actionIdsUnique := by decide
         actionsAccepted := by native_decide
         steps := [provedTick rootSnapshot secondaryEntered]
         stepsNonempty := by decide
         firstStepActionsExact := by native_decide
         stepsConnect := by
           simp only [CommandGraphStepsConnect]
           exact ⟨SameSnapshotData.refl rootSnapshot,
             SameSnapshotData.refl secondaryAssigned⟩ }
     label := "Staff Secondary"
     summary := "Assign the unique Body to the Secondary station."
     automaticOrders := [] },
   { proof :=
       { id := 10
         source := provedPrimaryAssignedNode
         target := provedPrimaryQueuedNode
         sourceMember := by simp [provedNodes]
         targetMember := by simp [provedNodes]
         actionIds := [primaryReserveCandidate.id]
         actionIdsNonempty := by decide
         actionIdsUnique := by decide
         actionsAccepted := by native_decide
         steps := [provedTick primaryAssigned primaryQueuedRun]
         stepsNonempty := by decide
         firstStepActionsExact := by native_decide
         stepsConnect := by
           simp only [CommandGraphStepsConnect]
           exact ⟨SameSnapshotData.refl primaryAssigned,
             SameSnapshotData.refl primaryQueued⟩ }
     label := "Queue Primary lot"
     summary := "Reserve shared fuel and occupy Primary input capacity."
     automaticOrders := [] },
   { proof :=
       { id := 11
         source := provedPrimaryAssignedNode
         target := provedPrimaryDeferredNode
         sourceMember := by simp [provedNodes]
         targetMember := by simp [provedNodes]
         actionIds := [primaryLeaveCandidate.id]
         actionIdsNonempty := by decide
         actionIdsUnique := by decide
         actionsAccepted := by native_decide
         steps := [provedTick primaryAssigned primaryDeferredRun]
         stepsNonempty := by decide
         firstStepActionsExact := by native_decide
         stepsConnect := by
           simp only [CommandGraphStepsConnect]
           exact ⟨SameSnapshotData.refl primaryAssigned,
             SameSnapshotData.refl primaryDeferred⟩ }
     label := "Defer work"
     summary := "Release the Body before reserving any shared resources."
     automaticOrders := [] },
   { proof :=
       { id := 12
         source := provedPrimaryAssignedNode
         target := provedPrimaryMaintainedNode
         sourceMember := by simp [provedNodes]
         targetMember := by simp [provedNodes]
         actionIds := [primaryStopCandidate.id]
         actionIdsNonempty := by decide
         actionIdsUnique := by decide
         actionsAccepted := by native_decide
         steps :=
           [provedTick primaryAssigned primaryMaintenanceStop,
            provedTick primaryMaintenanceStop.child primaryMaintenanceStart,
            provedTick primaryMaintenanceStart.child primaryMaintenanceLeave]
         stepsNonempty := by decide
         firstStepActionsExact := by native_decide
         stepsConnect := by
           simp only [CommandGraphStepsConnect]
           exact ⟨SameSnapshotData.refl primaryAssigned,
             ⟨SameSnapshotData.refl primaryMaintenanceStop.child,
               ⟨SameSnapshotData.refl primaryMaintenanceStart.child,
                 SameSnapshotData.refl primaryMaintained⟩⟩⟩ }
     label := "Maintain Primary"
     summary := "Stop and restart safely while processing is idle."
     automaticOrders := ["restart Primary", "release operator"] },
   { proof :=
       { id := 20
         source := provedSecondaryAssignedNode
         target := provedSecondaryQueuedNode
         sourceMember := by simp [provedNodes]
         targetMember := by simp [provedNodes]
         actionIds := [secondaryReserveCandidate.id]
         actionIdsNonempty := by decide
         actionIdsUnique := by decide
         actionsAccepted := by native_decide
         steps := [provedTick secondaryAssigned secondaryQueuedRun]
         stepsNonempty := by decide
         firstStepActionsExact := by native_decide
         stepsConnect := by
           simp only [CommandGraphStepsConnect]
           exact ⟨SameSnapshotData.refl secondaryAssigned,
             SameSnapshotData.refl secondaryQueued⟩ }
     label := "Queue Secondary lot"
     summary := "Reserve shared fuel and occupy Secondary input capacity."
     automaticOrders := [] },
   { proof :=
       { id := 21
         source := provedSecondaryAssignedNode
         target := provedSecondaryDeferredNode
         sourceMember := by simp [provedNodes]
         targetMember := by simp [provedNodes]
         actionIds := [secondaryLeaveCandidate.id]
         actionIdsNonempty := by decide
         actionIdsUnique := by decide
         actionsAccepted := by native_decide
         steps := [provedTick secondaryAssigned secondaryDeferredRun]
         stepsNonempty := by decide
         firstStepActionsExact := by native_decide
         stepsConnect := by
           simp only [CommandGraphStepsConnect]
           exact ⟨SameSnapshotData.refl secondaryAssigned,
             SameSnapshotData.refl secondaryDeferred⟩ }
     label := "Defer work"
     summary := "Release the Body before reserving any shared resources."
     automaticOrders := [] },
   { proof :=
       { id := 22
         source := provedSecondaryAssignedNode
         target := provedSecondaryMaintainedNode
         sourceMember := by simp [provedNodes]
         targetMember := by simp [provedNodes]
         actionIds := [secondaryStopCandidate.id]
         actionIdsNonempty := by decide
         actionIdsUnique := by decide
         actionsAccepted := by native_decide
         steps :=
           [provedTick secondaryAssigned secondaryMaintenanceStop,
            provedTick secondaryMaintenanceStop.child secondaryMaintenanceStart,
            provedTick secondaryMaintenanceStart.child secondaryMaintenanceLeave]
         stepsNonempty := by decide
         firstStepActionsExact := by native_decide
         stepsConnect := by
           simp only [CommandGraphStepsConnect]
           exact ⟨SameSnapshotData.refl secondaryAssigned,
             ⟨SameSnapshotData.refl secondaryMaintenanceStop.child,
               ⟨SameSnapshotData.refl secondaryMaintenanceStart.child,
                 SameSnapshotData.refl secondaryMaintained⟩⟩⟩ }
     label := "Maintain Secondary"
     summary := "Exercise the isolated Secondary runtime without consuming fuel."
     automaticOrders := ["restart Secondary", "release operator"] },
   { proof :=
       { id := 30
         source := provedPrimaryQueuedNode
         target := provedPrimaryProductiveNode
         sourceMember := by simp [provedNodes]
         targetMember := by simp [provedNodes]
         actionIds := [primaryDispatchCandidate.id]
         actionIdsNonempty := by decide
         actionIdsUnique := by decide
         actionsAccepted := by native_decide
         steps :=
           [provedTick primaryQueued primaryProductiveDispatch,
            provedTick primaryProductiveDispatch.child primaryProductiveAdvance,
            provedTick primaryProductiveAdvance.child primaryProductiveComplete,
            provedTick primaryProductiveComplete.child primaryProductiveLeave,
            provedTick primaryProductiveLeave.child primaryProductiveCollect]
         stepsNonempty := by decide
         firstStepActionsExact := by native_decide
         stepsConnect := by
           simp only [CommandGraphStepsConnect]
           exact ⟨SameSnapshotData.refl primaryQueued,
             ⟨SameSnapshotData.refl primaryProductiveDispatch.child,
               ⟨SameSnapshotData.refl primaryProductiveAdvance.child,
                 ⟨SameSnapshotData.refl primaryProductiveComplete.child,
                   ⟨SameSnapshotData.refl primaryProductiveLeave.child,
                     SameSnapshotData.refl primaryProductive⟩⟩⟩⟩⟩ }
     label := "Run productive cycle"
     summary := "Dispatch, advance, complete, release, and collect one full lot."
     automaticOrders := ["advance work", "complete lot", "release operator", "collect output"] },
   { proof :=
       { id := 31
         source := provedPrimaryQueuedNode
         target := provedPrimaryRecoveredNode
         sourceMember := by simp [provedNodes]
         targetMember := by simp [provedNodes]
         actionIds := [primaryDispatchCandidate.id, primaryQueuedLeaveCandidate.id]
         actionIdsNonempty := by decide
         actionIdsUnique := by decide
         actionsAccepted := by native_decide
         steps :=
           [provedTick primaryQueued primaryRiskDispatch,
            provedTick primaryRiskDispatch.child primaryRiskFail,
            provedTick primaryRiskFail.child primaryRiskRepair,
            provedTick primaryRiskRepair.child primaryRiskStart,
            provedTick primaryRiskStart.child primaryRiskLeave]
         stepsNonempty := by decide
         firstStepActionsExact := by native_decide
         stepsConnect := by
           simp only [CommandGraphStepsConnect]
           exact ⟨SameSnapshotData.refl primaryQueued,
             ⟨SameSnapshotData.refl primaryRiskDispatch.child,
               ⟨SameSnapshotData.refl primaryRiskFail.child,
                 ⟨SameSnapshotData.refl primaryRiskRepair.child,
                   ⟨SameSnapshotData.refl primaryRiskStart.child,
                     SameSnapshotData.refl primaryRecovered⟩⟩⟩⟩⟩ }
     label := "Dispatch and release"
     summary := "Resolve simultaneous orders, then recover from a deterministic active failure."
     automaticOrders := ["active failure", "repair", "restart", "release operator"] },
   { proof :=
       { id := 32
         source := provedPrimaryQueuedNode
         target := provedPrimaryBacklogNode
         sourceMember := by simp [provedNodes]
         targetMember := by simp [provedNodes]
         actionIds := [primaryQueuedLeaveCandidate.id]
         actionIdsNonempty := by decide
         actionIdsUnique := by decide
         actionsAccepted := by native_decide
         steps := [provedTick primaryQueued primaryBacklogRun]
         stepsNonempty := by decide
         firstStepActionsExact := by native_decide
         stepsConnect := by
           simp only [CommandGraphStepsConnect]
           exact ⟨SameSnapshotData.refl primaryQueued,
             SameSnapshotData.refl primaryBacklog⟩ }
     label := "Strand Primary backlog"
     summary := "Release the Body while preserving a reserved queued lot."
     automaticOrders := [] },
   { proof :=
       { id := 33
         source := provedPrimaryQueuedNode
         target := provedPrimaryConservedNode
         sourceMember := by simp [provedNodes]
         targetMember := by simp [provedNodes]
         actionIds := [primaryCancelCandidate.id]
         actionIdsNonempty := by decide
         actionIdsUnique := by decide
         actionsAccepted := by native_decide
         steps :=
           [provedTick primaryQueued primaryCancelRun,
            provedTick primaryCancelRun.child primaryCancelLeave]
         stepsNonempty := by decide
         firstStepActionsExact := by native_decide
         stepsConnect := by
           simp only [CommandGraphStepsConnect]
           exact ⟨SameSnapshotData.refl primaryQueued,
             ⟨SameSnapshotData.refl primaryCancelRun.child,
               SameSnapshotData.refl primaryConserved⟩⟩ }
     label := "Cancel and conserve"
     summary := "Return reservations before releasing the operator."
     automaticOrders := ["release operator"] },
   { proof :=
       { id := 40
         source := provedSecondaryQueuedNode
         target := provedSecondaryProductiveNode
         sourceMember := by simp [provedNodes]
         targetMember := by simp [provedNodes]
         actionIds := [secondaryDispatchCandidate.id]
         actionIdsNonempty := by decide
         actionIdsUnique := by decide
         actionsAccepted := by native_decide
         steps :=
           [provedTick secondaryQueued secondaryProductiveDispatch,
            provedTick secondaryProductiveDispatch.child secondaryProductiveAdvance,
            provedTick secondaryProductiveAdvance.child secondaryProductiveComplete,
            provedTick secondaryProductiveComplete.child secondaryProductiveLeave,
            provedTick secondaryProductiveLeave.child secondaryProductiveCollect]
         stepsNonempty := by decide
         firstStepActionsExact := by native_decide
         stepsConnect := by
           simp only [CommandGraphStepsConnect]
           exact ⟨SameSnapshotData.refl secondaryQueued,
             ⟨SameSnapshotData.refl secondaryProductiveDispatch.child,
               ⟨SameSnapshotData.refl secondaryProductiveAdvance.child,
                 ⟨SameSnapshotData.refl secondaryProductiveComplete.child,
                   ⟨SameSnapshotData.refl secondaryProductiveLeave.child,
                     SameSnapshotData.refl secondaryProductive⟩⟩⟩⟩⟩ }
     label := "Run productive cycle"
     summary := "Execute the same resource protocol through Secondary."
     automaticOrders := ["advance work", "complete lot", "release operator", "collect output"] },
   { proof :=
       { id := 41
         source := provedSecondaryQueuedNode
         target := provedSecondaryRecoveredNode
         sourceMember := by simp [provedNodes]
         targetMember := by simp [provedNodes]
         actionIds := [secondaryDispatchCandidate.id, secondaryQueuedLeaveCandidate.id]
         actionIdsNonempty := by decide
         actionIdsUnique := by decide
         actionsAccepted := by native_decide
         steps :=
           [provedTick secondaryQueued secondaryRiskDispatch,
            provedTick secondaryRiskDispatch.child secondaryRiskFail,
            provedTick secondaryRiskFail.child secondaryRiskRepair,
            provedTick secondaryRiskRepair.child secondaryRiskStart,
            provedTick secondaryRiskStart.child secondaryRiskLeave]
         stepsNonempty := by decide
         firstStepActionsExact := by native_decide
         stepsConnect := by
           simp only [CommandGraphStepsConnect]
           exact ⟨SameSnapshotData.refl secondaryQueued,
             ⟨SameSnapshotData.refl secondaryRiskDispatch.child,
               ⟨SameSnapshotData.refl secondaryRiskFail.child,
                 ⟨SameSnapshotData.refl secondaryRiskRepair.child,
                   ⟨SameSnapshotData.refl secondaryRiskStart.child,
                     SameSnapshotData.refl secondaryRecovered⟩⟩⟩⟩⟩ }
     label := "Dispatch and release"
     summary := "Expose conflict arbitration and deterministic Secondary recovery."
     automaticOrders := ["active failure", "repair", "restart", "release operator"] },
   { proof :=
       { id := 42
         source := provedSecondaryQueuedNode
         target := provedSecondaryBacklogNode
         sourceMember := by simp [provedNodes]
         targetMember := by simp [provedNodes]
         actionIds := [secondaryQueuedLeaveCandidate.id]
         actionIdsNonempty := by decide
         actionIdsUnique := by decide
         actionsAccepted := by native_decide
         steps := [provedTick secondaryQueued secondaryBacklogRun]
         stepsNonempty := by decide
         firstStepActionsExact := by native_decide
         stepsConnect := by
           simp only [CommandGraphStepsConnect]
           exact ⟨SameSnapshotData.refl secondaryQueued,
             SameSnapshotData.refl secondaryBacklog⟩ }
     label := "Strand Secondary backlog"
     summary := "Preserve the queued reservation while releasing the Body."
     automaticOrders := [] },
   { proof :=
       { id := 43
         source := provedSecondaryQueuedNode
         target := provedSecondaryConservedNode
         sourceMember := by simp [provedNodes]
         targetMember := by simp [provedNodes]
         actionIds := [secondaryCancelCandidate.id]
         actionIdsNonempty := by decide
         actionIdsUnique := by decide
         actionsAccepted := by native_decide
         steps :=
           [provedTick secondaryQueued secondaryCancelRun,
            provedTick secondaryCancelRun.child secondaryCancelLeave]
         stepsNonempty := by decide
         firstStepActionsExact := by native_decide
         stepsConnect := by
           simp only [CommandGraphStepsConnect]
           exact ⟨SameSnapshotData.refl secondaryQueued,
             ⟨SameSnapshotData.refl secondaryCancelRun.child,
               SameSnapshotData.refl secondaryConserved⟩⟩ }
     label := "Cancel and conserve"
     summary := "Return shared resources without producing output."
     automaticOrders := ["release operator"] }]

def provedResolutions : List ProvedResolution :=
  resolutions.map fun resolution => resolution.proof

def provedGraph : Maquina.CommandGraph Workcell.executor initialState where
  actor := operatorActor
  nodes := provedNodes
  root := provedRootNode
  rootMember := by simp [provedNodes]
  nodeIdsUnique := by native_decide
  candidatesOwned := by native_decide
  resolutions := provedResolutions
  resolutionIdsUnique := by native_decide
  resolutionChoicesUnique := by native_decide
  acceptedCandidatesCovered := by native_decide
  terminalComplete := by native_decide

/-! ## Concrete semantic pressure tests -/

def eventAccepted (event : TimelineEvent Workcell.Issue Workcell.ScheduledReceipt) : Bool :=
  match event.outcome with
  | .accepted _ => true
  | .rejected _ _ => false

example : nodes.length = 17 := by native_decide
example : resolutions.length = 16 := by native_decide

example : primaryRiskDispatch.applied.events.map eventAccepted = [true, false] := by
  native_decide

example : secondaryRiskDispatch.applied.events.map eventAccepted = [true, false] := by
  native_decide

example :
    (primaryProductive.timeline.application.accounts.balance
      machineAccount fuelId).atoms = 10 := by native_decide

example :
    (secondaryProductive.timeline.application.accounts.balance
      Workcell.secondaryMachineAccount fuelId).atoms = 10 := by native_decide

example :
    (primaryProductive.timeline.application.accounts.balance
      collectorAccount serviceCreditId).atoms = 1 := by native_decide

example :
    (primaryRecovered.timeline.application.accounts.balance
      providerAccount fuelId).atoms = 20 := by native_decide

example :
    (primaryBacklog.timeline.application.accounts.balance
      escrowAccount fuelId).atoms = 10 := by native_decide

example :
    (primaryConserved.timeline.application.accounts.balance
      providerAccount fuelId).atoms = 20 := by native_decide

end Maquina.Games.Foundry.ControlRoom
