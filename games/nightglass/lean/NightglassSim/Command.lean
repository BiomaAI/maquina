import NightglassSim.Simulation
import Maquina.Command

/-!
# Operation Nightglass Command Graph

A bounded, Lean-owned counterfactual command graph. The browser receives
already-assessed candidates and proof-backed resolutions; it never executes
Nightglass rules.
-/

namespace Maquina.Games.Nightglass.Command

open Maquina.Games.Nightglass Simulation

abbrev Snapshot := TimelineSnapshot executor initialState

def commanderActor : ActorId := ⟨1⟩
def oppositionActor : ActorId := ⟨2⟩

def commandPreludeEvents : List (TimelineEvent Issue Receipt) :=
  tickZero.events ++ tickOne.events

def commandRootTimeline : TimelineState State Intent :=
  { tickOne.after with
      pending := []
      pendingIdsUnique := by simp }

def commandRoot : Snapshot where
  id := ⟨0⟩
  timeline := commandRootTimeline
  history := commandPreludeEvents
  replayExact := by
    change replayTimelineEvents executor (tickZero.events ++ tickOne.events)
      initialState = tickOne.after.application
    rw [replayTimelineEvents_append]
    change replayTimelineEvents executor tickOne.events
      (replayTimelineEvents executor tickZero.events initialTimeline.application) =
        tickOne.after.application
    rw [tickZero.replayExact, tickOne.replayExact]

def candidate (id : Nat) (payload : Intent) : CommandCandidate Intent where
  id := ⟨id⟩
  actor := commanderActor
  payload

def order
    (id major minor : Nat)
    (actor : ActorId)
    (payload : Intent) : CommandOrder Intent where
  id := ⟨id⟩
  actor
  arbitration := ⟨major, minor⟩
  payload

def acquireAlphaCandidate := candidate 100 acquireAlpha
def acquireBravoCandidate := candidate 101 acquireBravo
def prematureLaunchCandidate := candidate 102 launchAlpha
def launchAlphaCandidate := candidate 110 launchAlpha
def launchBravoCandidate := candidate 111 launchBravo
def advanceCandidate := candidate 120 enterRouteOne
def abortCandidate := candidate 130 abortStaging
def competingBravoCandidate := candidate 140 acquireBravo
def competingAlphaCandidate := candidate 141 acquireAlpha

def acquireAlphaSet : OrderSet Intent where
  orders := [order 100 20 0 commanderActor acquireAlpha]
  idsUnique := by decide

def acquireBravoSet : OrderSet Intent where
  orders := [order 101 20 0 commanderActor acquireBravo]
  idsUnique := by decide

def launchAlphaSet : OrderSet Intent where
  orders := [order 110 10 0 commanderActor launchAlpha]
  idsUnique := by decide

def launchBravoSet : OrderSet Intent where
  orders := [order 111 10 0 commanderActor launchBravo]
  idsUnique := by decide

def advanceSet : OrderSet Intent where
  orders := [order 120 20 0 commanderActor enterRouteOne]
  idsUnique := by decide

def alphaCoordinatedSet : OrderSet Intent where
  orders :=
    [order 110 10 0 commanderActor launchAlpha,
     order 120 20 0 commanderActor enterRouteOne]
  idsUnique := by decide

def bravoCoordinatedSet : OrderSet Intent where
  orders :=
    [order 111 10 0 commanderActor launchBravo,
     order 120 20 0 commanderActor enterRouteOne]
  idsUnique := by decide

def abortSet : OrderSet Intent where
  orders := [order 130 10 0 commanderActor abortStaging]
  idsUnique := by decide

def strikeSet : OrderSet Intent where
  orders := [order 900 10 0 oppositionActor strikeConvoy]
  idsUnique := by decide

def routeOneSet : OrderSet Intent where
  orders := [order 901 20 0 commanderActor enterRouteOne]
  idsUnique := by decide

def repairSet : OrderSet Intent where
  orders := [order 902 10 0 commanderActor repairConvoy]
  idsUnique := by decide

def routeTwoSet : OrderSet Intent where
  orders := [order 903 10 0 commanderActor enterRouteTwo]
  idsUnique := by decide

def finishAlphaSet : OrderSet Intent where
  orders :=
    [order 904 10 0 commanderActor completeAlpha,
     order 905 20 0 commanderActor extractConvoy,
     order 906 30 0 commanderActor clearTrack]
  idsUnique := by decide

def finishBravoSet : OrderSet Intent where
  orders :=
    [order 904 10 0 commanderActor completeBravo,
     order 905 20 0 commanderActor extractConvoy,
     order 906 30 0 commanderActor clearTrack]
  idsUnique := by decide

def exposedFinishSet : OrderSet Intent where
  orders := [order 905 20 0 commanderActor extractConvoy]
  idsUnique := by decide

def alphaAssignment :=
  resolveSnapshotOrderSet executor initialState commandRoot ⟨1⟩ rfl acquireAlphaSet

def bravoAssignment :=
  resolveSnapshotOrderSet executor initialState commandRoot ⟨2⟩ rfl acquireBravoSet

def alphaAssigned : Snapshot := alphaAssignment.child
def bravoAssigned : Snapshot := bravoAssignment.child

/-! ## Shield-first plans -/

def alphaCleanLaunch :=
  resolveSnapshotOrderSet executor initialState alphaAssigned ⟨100⟩ rfl launchAlphaSet
def alphaCleanThreat :=
  resolveSnapshotOrderSet executor initialState alphaCleanLaunch.child ⟨101⟩ rfl strikeSet
def alphaCleanRouteOne :=
  resolveSnapshotOrderSet executor initialState alphaCleanThreat.child ⟨102⟩ rfl routeOneSet
def alphaCleanRouteTwo :=
  resolveSnapshotOrderSet executor initialState alphaCleanRouteOne.child ⟨103⟩ rfl routeTwoSet
def alphaCleanFinish :=
  resolveSnapshotOrderSet executor initialState alphaCleanRouteTwo.child ⟨10⟩ rfl finishAlphaSet
def alphaCleanFinal : Snapshot := alphaCleanFinish.child

def bravoCleanLaunch :=
  resolveSnapshotOrderSet executor initialState bravoAssigned ⟨200⟩ rfl launchBravoSet
def bravoCleanThreat :=
  resolveSnapshotOrderSet executor initialState bravoCleanLaunch.child ⟨201⟩ rfl strikeSet
def bravoCleanRouteOne :=
  resolveSnapshotOrderSet executor initialState bravoCleanThreat.child ⟨202⟩ rfl routeOneSet
def bravoCleanRouteTwo :=
  resolveSnapshotOrderSet executor initialState bravoCleanRouteOne.child ⟨203⟩ rfl routeTwoSet
def bravoCleanFinish :=
  resolveSnapshotOrderSet executor initialState bravoCleanRouteTwo.child ⟨14⟩ rfl finishBravoSet
def bravoCleanFinal : Snapshot := bravoCleanFinish.child

/-! ## Coordinated advance plans -/

def alphaCostlyAdvance :=
  resolveSnapshotOrderSet executor initialState alphaAssigned ⟨110⟩ rfl alphaCoordinatedSet
def alphaCostlyThreat :=
  resolveSnapshotOrderSet executor initialState alphaCostlyAdvance.child ⟨111⟩ rfl strikeSet
def alphaCostlyRepair :=
  resolveSnapshotOrderSet executor initialState alphaCostlyThreat.child ⟨112⟩ rfl repairSet
def alphaCostlyRouteTwo :=
  resolveSnapshotOrderSet executor initialState alphaCostlyRepair.child ⟨113⟩ rfl routeTwoSet
def alphaCostlyFinish :=
  resolveSnapshotOrderSet executor initialState alphaCostlyRouteTwo.child ⟨11⟩ rfl finishAlphaSet
def alphaCostlyFinal : Snapshot := alphaCostlyFinish.child

def bravoCostlyAdvance :=
  resolveSnapshotOrderSet executor initialState bravoAssigned ⟨210⟩ rfl bravoCoordinatedSet
def bravoCostlyThreat :=
  resolveSnapshotOrderSet executor initialState bravoCostlyAdvance.child ⟨211⟩ rfl strikeSet
def bravoCostlyRepair :=
  resolveSnapshotOrderSet executor initialState bravoCostlyThreat.child ⟨212⟩ rfl repairSet
def bravoCostlyRouteTwo :=
  resolveSnapshotOrderSet executor initialState bravoCostlyRepair.child ⟨213⟩ rfl routeTwoSet
def bravoCostlyFinish :=
  resolveSnapshotOrderSet executor initialState bravoCostlyRouteTwo.child ⟨15⟩ rfl finishBravoSet
def bravoCostlyFinal : Snapshot := bravoCostlyFinish.child

/-! ## Unshielded sprint plans -/

def alphaExposedAdvance :=
  resolveSnapshotOrderSet executor initialState alphaAssigned ⟨120⟩ rfl advanceSet
def alphaExposedThreat :=
  resolveSnapshotOrderSet executor initialState alphaExposedAdvance.child ⟨121⟩ rfl strikeSet
def alphaExposedRepair :=
  resolveSnapshotOrderSet executor initialState alphaExposedThreat.child ⟨122⟩ rfl repairSet
def alphaExposedRouteTwo :=
  resolveSnapshotOrderSet executor initialState alphaExposedRepair.child ⟨123⟩ rfl routeTwoSet
def alphaExposedFinish :=
  resolveSnapshotOrderSet executor initialState alphaExposedRouteTwo.child ⟨12⟩ rfl exposedFinishSet
def alphaExposedFinal : Snapshot := alphaExposedFinish.child

def bravoExposedAdvance :=
  resolveSnapshotOrderSet executor initialState bravoAssigned ⟨220⟩ rfl advanceSet
def bravoExposedThreat :=
  resolveSnapshotOrderSet executor initialState bravoExposedAdvance.child ⟨221⟩ rfl strikeSet
def bravoExposedRepair :=
  resolveSnapshotOrderSet executor initialState bravoExposedThreat.child ⟨222⟩ rfl repairSet
def bravoExposedRouteTwo :=
  resolveSnapshotOrderSet executor initialState bravoExposedRepair.child ⟨223⟩ rfl routeTwoSet
def bravoExposedFinish :=
  resolveSnapshotOrderSet executor initialState bravoExposedRouteTwo.child ⟨16⟩ rfl exposedFinishSet
def bravoExposedFinal : Snapshot := bravoExposedFinish.child

/-! ## Abort plans -/

def alphaAbort :=
  resolveSnapshotOrderSet executor initialState alphaAssigned ⟨13⟩ rfl abortSet
def bravoAbort :=
  resolveSnapshotOrderSet executor initialState bravoAssigned ⟨17⟩ rfl abortSet
def alphaAbortFinal : Snapshot := alphaAbort.child
def bravoAbortFinal : Snapshot := bravoAbort.child

inductive CommandOutcome where
  | active
  | cleanVictory
  | costlyVictory
  | exposedExtraction
  | defeat
  deriving DecidableEq, Repr

structure CommanderObservation where
  tick : Nat
  radar : Radar.Mode
  alpha : Battery.Mode
  bravo : Battery.Mode
  convoy : Convoy.Mode
  channelLocation : Nat
  interceptors : Nat
  spareParts : Nat
  evacuees : Nat
  deriving DecidableEq, Repr

def channelLocation (state : State) : Nat :=
  if (state.accounts.balance commandAccount targetingChannelId).atoms = 1 then 0
  else if (state.accounts.balance alphaBatteryAccount targetingChannelId).atoms = 1 then 1
  else if (state.accounts.balance bravoBatteryAccount targetingChannelId).atoms = 1 then 2
  else 3

def commanderView (timeline : TimelineState State Intent) : CommanderObservation where
  tick := timeline.tick.value
  radar := timeline.application.radar.mode
  alpha := timeline.application.alpha.mode
  bravo := timeline.application.bravo.mode
  convoy := timeline.application.convoy.mode
  channelLocation := channelLocation timeline.application
  interceptors :=
    (timeline.application.accounts.balance arsenalAccount interceptorAmmoId).atoms
  spareParts :=
    (timeline.application.accounts.balance repairAccount sparePartsId).atoms
  evacuees :=
    (timeline.application.accounts.balance convoyAccount evacueeId).atoms

def commanderObservationPolicy :
    ObservationPolicy (TimelineState State Intent) CommanderObservation where
  permitted := fun _ state view => view = commanderView state
  observe := fun _ state => commanderView state
  sound := by intro actor state; rfl

/--
The commander's observation depends only on these explicitly visible fields.
Pending intent payloads, event history, custody proofs, queue internals, and
other application data do not occur in this relation.
-/
structure CommanderVisibleEquivalent
    (left right : TimelineState State Intent) : Prop where
  tick : left.tick = right.tick
  radar : left.application.radar.mode = right.application.radar.mode
  alpha : left.application.alpha.mode = right.application.alpha.mode
  bravo : left.application.bravo.mode = right.application.bravo.mode
  convoy : left.application.convoy.mode = right.application.convoy.mode
  commandChannel :
    left.application.accounts.balance commandAccount targetingChannelId =
      right.application.accounts.balance commandAccount targetingChannelId
  alphaChannel :
    left.application.accounts.balance alphaBatteryAccount targetingChannelId =
      right.application.accounts.balance alphaBatteryAccount targetingChannelId
  bravoChannel :
    left.application.accounts.balance bravoBatteryAccount targetingChannelId =
      right.application.accounts.balance bravoBatteryAccount targetingChannelId
  interceptors :
    left.application.accounts.balance arsenalAccount interceptorAmmoId =
      right.application.accounts.balance arsenalAccount interceptorAmmoId
  spareParts :
    left.application.accounts.balance repairAccount sparePartsId =
      right.application.accounts.balance repairAccount sparePartsId
  evacuees :
    left.application.accounts.balance convoyAccount evacueeId =
      right.application.accounts.balance convoyAccount evacueeId

theorem commanderView_noninterference
    (equivalent : CommanderVisibleEquivalent left right) :
    commanderView left = commanderView right := by
  cases equivalent
  simp_all [commanderView, channelLocation]

def commandStateKey (snapshot : Snapshot) : String :=
  reprStr (commanderView snapshot.timeline)

structure CandidateSpec where
  candidate : CommandCandidate Intent
  component : Component
  label : String
  detail : String

structure CommandNode where
  snapshot : Snapshot
  title : String
  summary : String
  outcome : CommandOutcome
  candidates : List CandidateSpec
  candidateIdsUnique :
    (candidates.map fun spec => spec.candidate.id).Nodup

structure CommandResolution where
  id : Nat
  label : String
  summary : String
  automaticOrders : List String

def rootNode : CommandNode where
  snapshot := commandRoot
  title := "Contact tracked"
  summary := "Assign the unique targeting channel to one interceptor battery."
  outcome := .active
  candidates :=
    [{ candidate := acquireAlphaCandidate
       component := .alphaBattery
       label := "Assign Battery Alpha"
       detail := "Transfer the unique targeting channel to Alpha." },
     { candidate := acquireBravoCandidate
       component := .bravoBattery
       label := "Assign Battery Bravo"
       detail := "Transfer the unique targeting channel to Bravo." },
     { candidate := prematureLaunchCandidate
       component := .alphaBattery
       label := "Launch before acquisition"
       detail := "Inspect the structured rejection for launching without a channel." }]
  candidateIdsUnique := by decide

def alphaNode : CommandNode where
  snapshot := alphaAssigned
  title := "Alpha has the channel"
  summary := "Queue defense, movement, both simultaneous orders, or abort."
  outcome := .active
  candidates :=
    [{ candidate := launchAlphaCandidate
       component := .alphaBattery
       label := "Launch Alpha interceptor"
       detail := "Spend one interceptor and engage Alpha." },
     { candidate := advanceCandidate
       component := .convoy
       label := "Advance convoy"
       detail := "Move the evacuation convoy into route one." },
     { candidate := abortCandidate
       component := .convoy
       label := "Abort extraction"
       detail := "End the mission before entering the threat corridor." },
     { candidate := competingBravoCandidate
       component := .bravoBattery
       label := "Assign Bravo too"
       detail := "Inspect unique-channel contention without mutation." }]
  candidateIdsUnique := by decide

def bravoNode : CommandNode where
  snapshot := bravoAssigned
  title := "Bravo has the channel"
  summary := "Queue defense, movement, both simultaneous orders, or abort."
  outcome := .active
  candidates :=
    [{ candidate := launchBravoCandidate
       component := .bravoBattery
       label := "Launch Bravo interceptor"
       detail := "Spend one interceptor and engage Bravo." },
     { candidate := advanceCandidate
       component := .convoy
       label := "Advance convoy"
       detail := "Move the evacuation convoy into route one." },
     { candidate := abortCandidate
       component := .convoy
       label := "Abort extraction"
       detail := "End the mission before entering the threat corridor." },
     { candidate := competingAlphaCandidate
       component := .alphaBattery
       label := "Assign Alpha too"
       detail := "Inspect unique-channel contention without mutation." }]
  candidateIdsUnique := by decide

def terminalNode
    (snapshot : Snapshot)
    (title summary : String)
    (outcome : CommandOutcome) : CommandNode where
  snapshot
  title
  summary
  outcome
  candidates := []
  candidateIdsUnique := by simp

def alphaCleanNode :=
  terminalNode alphaCleanFinal "Clean extraction"
    "The threat was intercepted before convoy movement; no repair part was spent."
    .cleanVictory

def alphaCostlyNode :=
  terminalNode alphaCostlyFinal "Costly extraction"
    "The convoy moved under cover, survived damage, repaired, and extracted."
    .costlyVictory

def alphaExposedNode :=
  terminalNode alphaExposedFinal "Exposed extraction"
    "The convoy extracted, but the interceptor was conserved and the channel remains committed."
    .exposedExtraction

def alphaAbortNode :=
  terminalNode alphaAbortFinal "Mission aborted"
    "Command terminated the extraction before entering the corridor." .defeat

def bravoCleanNode :=
  terminalNode bravoCleanFinal "Clean extraction"
    "The threat was intercepted before convoy movement; no repair part was spent."
    .cleanVictory

def bravoCostlyNode :=
  terminalNode bravoCostlyFinal "Costly extraction"
    "The convoy moved under cover, survived damage, repaired, and extracted."
    .costlyVictory

def bravoExposedNode :=
  terminalNode bravoExposedFinal "Exposed extraction"
    "The convoy extracted, but the interceptor was conserved and the channel remains committed."
    .exposedExtraction

def bravoAbortNode :=
  terminalNode bravoAbortFinal "Mission aborted"
    "Command terminated the extraction before entering the corridor." .defeat

def nodes : List CommandNode :=
  [rootNode, alphaNode, bravoNode,
   alphaCleanNode, alphaCostlyNode, alphaExposedNode, alphaAbortNode,
   bravoCleanNode, bravoCostlyNode, bravoExposedNode, bravoAbortNode]

abbrev ProvedNode := Maquina.CommandGraphNode executor initialState

def provedNode (node : CommandNode) : ProvedNode :=
  assessCommandGraphNode executor initialState node.snapshot
    (node.candidates.map fun spec => spec.candidate) (by
      simpa [List.map_map, Function.comp_def] using node.candidateIdsUnique)

def provedRootNode := provedNode rootNode
def provedAlphaNode := provedNode alphaNode
def provedBravoNode := provedNode bravoNode
def provedAlphaCleanNode := provedNode alphaCleanNode
def provedAlphaCostlyNode := provedNode alphaCostlyNode
def provedAlphaExposedNode := provedNode alphaExposedNode
def provedAlphaAbortNode := provedNode alphaAbortNode
def provedBravoCleanNode := provedNode bravoCleanNode
def provedBravoCostlyNode := provedNode bravoCostlyNode
def provedBravoExposedNode := provedNode bravoExposedNode
def provedBravoAbortNode := provedNode bravoAbortNode

def provedNodes : List ProvedNode :=
  [provedRootNode, provedAlphaNode, provedBravoNode,
   provedAlphaCleanNode, provedAlphaCostlyNode, provedAlphaExposedNode,
   provedAlphaAbortNode, provedBravoCleanNode, provedBravoCostlyNode,
   provedBravoExposedNode, provedBravoAbortNode]

abbrev ProvedResolution :=
  Maquina.CommandGraphResolution executor initialState provedNodes

def provedTick
    (parent : Snapshot)
    (resolved : ResolvedSnapshotOrderSet executor initialState parent) :
    Maquina.CommandGraphStep executor initialState :=
  commandGraphStep executor initialState parent resolved

def resolutions : List CommandResolution :=
  [{ id := 0
     label := "Assign Alpha"
     summary := "Battery Alpha acquires the unique targeting channel."
     automaticOrders := [] },
   { id := 1
     label := "Assign Bravo"
     summary := "Battery Bravo acquires the unique targeting channel."
     automaticOrders := [] },
   { id := 10
     label := "Shield first"
     summary := "Launch before movement, let the strike pass staging, then extract."
     automaticOrders := ["hostile strike", "route one", "route two", "extract and stand down"] },
   { id := 11
     label := "Move under cover"
     summary := "Launch and move simultaneously; repair after the deterministic strike."
     automaticOrders := ["hostile strike", "repair", "route two", "extract and stand down"] },
   { id := 12
     label := "Sprint unshielded"
     summary := "Move without launching; repair and extract with the channel still committed."
     automaticOrders := ["hostile strike", "repair", "route two", "extract"] },
   { id := 13
     label := "Abort mission"
     summary := "Terminate the extraction without entering the corridor."
     automaticOrders := [] },
   { id := 20
     label := "Shield first"
     summary := "Launch before movement, let the strike pass staging, then extract."
     automaticOrders := ["hostile strike", "route one", "route two", "extract and stand down"] },
   { id := 21
     label := "Move under cover"
     summary := "Launch and move simultaneously; repair after the deterministic strike."
     automaticOrders := ["hostile strike", "repair", "route two", "extract and stand down"] },
   { id := 22
     label := "Sprint unshielded"
     summary := "Move without launching; repair and extract with the channel still committed."
     automaticOrders := ["hostile strike", "repair", "route two", "extract"] },
   { id := 23
     label := "Abort mission"
     summary := "Terminate the extraction without entering the corridor."
     automaticOrders := [] }]

def provedResolutions : List ProvedResolution :=
  [{ id := 0
     source := provedRootNode
     target := provedAlphaNode
     sourceMember := by simp [provedNodes]
     targetMember := by simp [provedNodes]
     actionIds := [acquireAlphaCandidate.id]
     actionIdsNonempty := by decide
     actionIdsUnique := by decide
     actionsAccepted := by native_decide
     steps := [provedTick commandRoot alphaAssignment]
     stepsNonempty := by decide
     firstStepActionsExact := by native_decide
     stepsConnect := by
       simp only [CommandGraphStepsConnect]
       constructor
       · exact SameSnapshotData.refl commandRoot
       · exact SameSnapshotData.refl alphaAssigned },
   { id := 1
     source := provedRootNode
     target := provedBravoNode
     sourceMember := by simp [provedNodes]
     targetMember := by simp [provedNodes]
     actionIds := [acquireBravoCandidate.id]
     actionIdsNonempty := by decide
     actionIdsUnique := by decide
     actionsAccepted := by native_decide
     steps := [provedTick commandRoot bravoAssignment]
     stepsNonempty := by decide
     firstStepActionsExact := by native_decide
     stepsConnect := by
       simp only [CommandGraphStepsConnect]
       exact ⟨SameSnapshotData.refl commandRoot,
         SameSnapshotData.refl bravoAssigned⟩ },
   { id := 10
     source := provedAlphaNode
     target := provedAlphaCleanNode
     sourceMember := by simp [provedNodes]
     targetMember := by simp [provedNodes]
     actionIds := [launchAlphaCandidate.id]
     actionIdsNonempty := by decide
     actionIdsUnique := by decide
     actionsAccepted := by native_decide
     steps :=
       [provedTick alphaAssigned alphaCleanLaunch,
        provedTick alphaCleanLaunch.child alphaCleanThreat,
        provedTick alphaCleanThreat.child alphaCleanRouteOne,
        provedTick alphaCleanRouteOne.child alphaCleanRouteTwo,
        provedTick alphaCleanRouteTwo.child alphaCleanFinish]
     stepsNonempty := by decide
     firstStepActionsExact := by native_decide
     stepsConnect := by
       simp only [CommandGraphStepsConnect]
       exact ⟨SameSnapshotData.refl alphaAssigned,
         ⟨SameSnapshotData.refl alphaCleanLaunch.child,
           ⟨SameSnapshotData.refl alphaCleanThreat.child,
             ⟨SameSnapshotData.refl alphaCleanRouteOne.child,
               ⟨SameSnapshotData.refl alphaCleanRouteTwo.child,
                 SameSnapshotData.refl alphaCleanFinal⟩⟩⟩⟩⟩ },
   { id := 11
     source := provedAlphaNode
     target := provedAlphaCostlyNode
     sourceMember := by simp [provedNodes]
     targetMember := by simp [provedNodes]
     actionIds := [launchAlphaCandidate.id, advanceCandidate.id]
     actionIdsNonempty := by decide
     actionIdsUnique := by decide
     actionsAccepted := by native_decide
     steps :=
       [provedTick alphaAssigned alphaCostlyAdvance,
        provedTick alphaCostlyAdvance.child alphaCostlyThreat,
        provedTick alphaCostlyThreat.child alphaCostlyRepair,
        provedTick alphaCostlyRepair.child alphaCostlyRouteTwo,
        provedTick alphaCostlyRouteTwo.child alphaCostlyFinish]
     stepsNonempty := by decide
     firstStepActionsExact := by native_decide
     stepsConnect := by
       simp only [CommandGraphStepsConnect]
       exact ⟨SameSnapshotData.refl alphaAssigned,
         ⟨SameSnapshotData.refl alphaCostlyAdvance.child,
           ⟨SameSnapshotData.refl alphaCostlyThreat.child,
             ⟨SameSnapshotData.refl alphaCostlyRepair.child,
               ⟨SameSnapshotData.refl alphaCostlyRouteTwo.child,
                 SameSnapshotData.refl alphaCostlyFinal⟩⟩⟩⟩⟩ },
   { id := 12
     source := provedAlphaNode
     target := provedAlphaExposedNode
     sourceMember := by simp [provedNodes]
     targetMember := by simp [provedNodes]
     actionIds := [advanceCandidate.id]
     actionIdsNonempty := by decide
     actionIdsUnique := by decide
     actionsAccepted := by native_decide
     steps :=
       [provedTick alphaAssigned alphaExposedAdvance,
        provedTick alphaExposedAdvance.child alphaExposedThreat,
        provedTick alphaExposedThreat.child alphaExposedRepair,
        provedTick alphaExposedRepair.child alphaExposedRouteTwo,
        provedTick alphaExposedRouteTwo.child alphaExposedFinish]
     stepsNonempty := by decide
     firstStepActionsExact := by native_decide
     stepsConnect := by
       simp only [CommandGraphStepsConnect]
       exact ⟨SameSnapshotData.refl alphaAssigned,
         ⟨SameSnapshotData.refl alphaExposedAdvance.child,
           ⟨SameSnapshotData.refl alphaExposedThreat.child,
             ⟨SameSnapshotData.refl alphaExposedRepair.child,
               ⟨SameSnapshotData.refl alphaExposedRouteTwo.child,
                 SameSnapshotData.refl alphaExposedFinal⟩⟩⟩⟩⟩ },
   { id := 13
     source := provedAlphaNode
     target := provedAlphaAbortNode
     sourceMember := by simp [provedNodes]
     targetMember := by simp [provedNodes]
     actionIds := [abortCandidate.id]
     actionIdsNonempty := by decide
     actionIdsUnique := by decide
     actionsAccepted := by native_decide
     steps := [provedTick alphaAssigned alphaAbort]
     stepsNonempty := by decide
     firstStepActionsExact := by native_decide
     stepsConnect := by
       simp only [CommandGraphStepsConnect]
       exact ⟨SameSnapshotData.refl alphaAssigned,
         SameSnapshotData.refl alphaAbortFinal⟩ },
   { id := 20
     source := provedBravoNode
     target := provedBravoCleanNode
     sourceMember := by simp [provedNodes]
     targetMember := by simp [provedNodes]
     actionIds := [launchBravoCandidate.id]
     actionIdsNonempty := by decide
     actionIdsUnique := by decide
     actionsAccepted := by native_decide
     steps :=
       [provedTick bravoAssigned bravoCleanLaunch,
        provedTick bravoCleanLaunch.child bravoCleanThreat,
        provedTick bravoCleanThreat.child bravoCleanRouteOne,
        provedTick bravoCleanRouteOne.child bravoCleanRouteTwo,
        provedTick bravoCleanRouteTwo.child bravoCleanFinish]
     stepsNonempty := by decide
     firstStepActionsExact := by native_decide
     stepsConnect := by
       simp only [CommandGraphStepsConnect]
       exact ⟨SameSnapshotData.refl bravoAssigned,
         ⟨SameSnapshotData.refl bravoCleanLaunch.child,
           ⟨SameSnapshotData.refl bravoCleanThreat.child,
             ⟨SameSnapshotData.refl bravoCleanRouteOne.child,
               ⟨SameSnapshotData.refl bravoCleanRouteTwo.child,
                 SameSnapshotData.refl bravoCleanFinal⟩⟩⟩⟩⟩ },
   { id := 21
     source := provedBravoNode
     target := provedBravoCostlyNode
     sourceMember := by simp [provedNodes]
     targetMember := by simp [provedNodes]
     actionIds := [launchBravoCandidate.id, advanceCandidate.id]
     actionIdsNonempty := by decide
     actionIdsUnique := by decide
     actionsAccepted := by native_decide
     steps :=
       [provedTick bravoAssigned bravoCostlyAdvance,
        provedTick bravoCostlyAdvance.child bravoCostlyThreat,
        provedTick bravoCostlyThreat.child bravoCostlyRepair,
        provedTick bravoCostlyRepair.child bravoCostlyRouteTwo,
        provedTick bravoCostlyRouteTwo.child bravoCostlyFinish]
     stepsNonempty := by decide
     firstStepActionsExact := by native_decide
     stepsConnect := by
       simp only [CommandGraphStepsConnect]
       exact ⟨SameSnapshotData.refl bravoAssigned,
         ⟨SameSnapshotData.refl bravoCostlyAdvance.child,
           ⟨SameSnapshotData.refl bravoCostlyThreat.child,
             ⟨SameSnapshotData.refl bravoCostlyRepair.child,
               ⟨SameSnapshotData.refl bravoCostlyRouteTwo.child,
                 SameSnapshotData.refl bravoCostlyFinal⟩⟩⟩⟩⟩ },
   { id := 22
     source := provedBravoNode
     target := provedBravoExposedNode
     sourceMember := by simp [provedNodes]
     targetMember := by simp [provedNodes]
     actionIds := [advanceCandidate.id]
     actionIdsNonempty := by decide
     actionIdsUnique := by decide
     actionsAccepted := by native_decide
     steps :=
       [provedTick bravoAssigned bravoExposedAdvance,
        provedTick bravoExposedAdvance.child bravoExposedThreat,
        provedTick bravoExposedThreat.child bravoExposedRepair,
        provedTick bravoExposedRepair.child bravoExposedRouteTwo,
        provedTick bravoExposedRouteTwo.child bravoExposedFinish]
     stepsNonempty := by decide
     firstStepActionsExact := by native_decide
     stepsConnect := by
       simp only [CommandGraphStepsConnect]
       exact ⟨SameSnapshotData.refl bravoAssigned,
         ⟨SameSnapshotData.refl bravoExposedAdvance.child,
           ⟨SameSnapshotData.refl bravoExposedThreat.child,
             ⟨SameSnapshotData.refl bravoExposedRepair.child,
               ⟨SameSnapshotData.refl bravoExposedRouteTwo.child,
                 SameSnapshotData.refl bravoExposedFinal⟩⟩⟩⟩⟩ },
   { id := 23
     source := provedBravoNode
     target := provedBravoAbortNode
     sourceMember := by simp [provedNodes]
     targetMember := by simp [provedNodes]
     actionIds := [abortCandidate.id]
     actionIdsNonempty := by decide
     actionIdsUnique := by decide
     actionsAccepted := by native_decide
     steps := [provedTick bravoAssigned bravoAbort]
     stepsNonempty := by decide
     firstStepActionsExact := by native_decide
     stepsConnect := by
       simp only [CommandGraphStepsConnect]
       exact ⟨SameSnapshotData.refl bravoAssigned,
         SameSnapshotData.refl bravoAbortFinal⟩ }]

def provedGraph : Maquina.CommandGraph executor initialState where
  actor := commanderActor
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

/-! ## Concrete conformance proofs -/

example : (nodes.map fun node => node.snapshot.id).Nodup := by native_decide
example : (resolutions.map fun resolution => resolution.id).Nodup := by native_decide
example : rootNode.candidates.length = 3 := by native_decide
example : alphaNode.candidates.length = 4 := by native_decide
example : nodes.length = 11 := by native_decide
example : resolutions.length = 10 := by native_decide
example : resolutions.length = provedResolutions.length := by native_decide
example : (resolutions.zip provedResolutions).all
    (fun pair => pair.1.id == pair.2.id) = true := by native_decide

/- Every exported command snapshot preserves the unique channel and evacuee
   population, and no branch overspends bounded consumables. -/
example : nodes.all (fun node =>
    (node.snapshot.timeline.application.accounts.total targetingChannelId).atoms == 1) =
      true := by native_decide

example : nodes.all (fun node =>
    (node.snapshot.timeline.application.accounts.total evacueeId).atoms == 24) =
      true := by native_decide

example : nodes.all (fun node =>
    (node.snapshot.timeline.application.accounts.total interceptorAmmoId).atoms ≤ 4 &&
    (node.snapshot.timeline.application.accounts.total sparePartsId).atoms ≤ 2) =
      true := by native_decide

example : nodes.all (fun node =>
    (node.snapshot.timeline.application.accounts.balance alphaBatteryAccount
      targetingChannelId).atoms +
    (node.snapshot.timeline.application.accounts.balance bravoBatteryAccount
      targetingChannelId).atoms ≤ 1) = true := by native_decide

example :
    (assessCandidate executor commandRoot.timeline.application
      prematureLaunchCandidate).assessment.successor? = none := by
  native_decide

example :
    (assessCandidate executor alphaAssigned.timeline.application
      competingBravoCandidate).assessment.successor? = none := by
  native_decide

example : missionStatus alphaCleanFinal.timeline = .victory := by native_decide
example : missionStatus alphaCostlyFinal.timeline = .victory := by native_decide
example : missionStatus alphaExposedFinal.timeline = .victory := by native_decide
example : missionStatus alphaAbortFinal.timeline = .defeat := by native_decide

example : commanderView alphaCleanFinal.timeline = commanderView bravoCleanFinal.timeline := by
  native_decide

example : commanderView alphaCostlyFinal.timeline = commanderView bravoCostlyFinal.timeline := by
  native_decide

example :
    replayTimelineEvents executor alphaCleanFinal.history initialState =
      alphaCleanFinal.timeline.application :=
  alphaCleanFinal.replayExact

example :
    replayTimelineEvents executor bravoCostlyFinal.history initialState =
      bravoCostlyFinal.timeline.application :=
  bravoCostlyFinal.replayExact

example : ∃ leftSuffix rightSuffix,
    alphaAssigned.history = commandRoot.history ++ leftSuffix ∧
    bravoAssigned.history = commandRoot.history ++ rightSuffix :=
  alphaAssignment.fork.siblings_share_parent_prefix bravoAssignment.fork

def alphaCoordinatedReversed : OrderSet Intent where
  orders := alphaCoordinatedSet.orders.reverse
  idsUnique := by native_decide

example :
    (orderScheduledIntents (scheduledOrders alphaAssigned.timeline.tick
      alphaCoordinatedSet)).map (fun intent => intent.id.value) =
    (orderScheduledIntents (scheduledOrders alphaAssigned.timeline.tick
      alphaCoordinatedReversed)).map (fun intent => intent.id.value) := by
  native_decide

end Maquina.Games.Nightglass.Command
