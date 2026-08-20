import FoundrySim.ControlRoom
import MaquinaViz

/-!
# Foundry Showcase Adapter

Foundry supplies names, scenarios, and declarative appearance to the shared
Maquina visualization protocol. It does not supply transition or rendering
logic.
-/

namespace Maquina.Games.Foundry.Showcase

open Refuel Simulation Visualization

def modeName : Mode → String
  | .off => "off"
  | .running => "running"
  | .broken => "broken"

def operationName {before after : Mode} : Operation before after → String
  | .start => "start"
  | .enterMachine => "enter machine"
  | .reserveFuel => "reserve fuel"
  | .dispatchRefuel => "dispatch refuel"
  | .advanceRefuel => "advance refuel"
  | .completeRefuel => "complete refuel"
  | .collectRefuel => "collect refuel"
  | .collectOperatorAllocation => "collect operator allocation"
  | .cancelQueuedRefuel => "cancel queued refuel"
  | .cancelActiveRefuel => "cancel active refuel"
  | .leaveMachine => "leave machine"
  | .addServiceInput => "add service input"
  | .removeServiceInput => "remove service input"
  | .stop => "stop"
  | .fail => "fail"
  | .repair => "repair"

def processKindName : ProcessKind → String
  | .refuel => "refuel"

def inputQueueKindName : InputQueueKind → String
  | .service => "service"

def processingQueueKindName : ProcessingQueueKind → String
  | .service => "service"

def outputQueueKindName : OutputQueueKind → String
  | .production => "production"

def projection : Visualization.Projection schema operationLanguage where
  machineId := "machine:foundry-service"
  modeName := modeName
  operationName := operationName
  processKindName := processKindName
  inputQueueKindName := inputQueueKindName
  processingQueueKindName := processingQueueKindName
  outputQueueKindName := outputQueueKindName

def workcellProjection : Workcell.Station →
    Visualization.Projection schema operationLanguage
  | .primary => { projection with machineId := "machine:foundry-service:primary" }
  | .secondary => { projection with machineId := "machine:foundry-service:secondary" }

private def position (x y z : Float) : Vec3 := { x, y, z }

def presentation : PresentationView where
  theme :=
    { background := "#101012"
      surface := "#161618"
      accent := "#e8e3d8" }
  resources :=
    [{ id := resourceKey fuelId
       label := "Fuel"
       symbol := "F"
       color := "#c2a15c"
       geometry := "cylinder"
       unit := some "L" },
     { id := resourceKey workerBodyId
       label := "Body"
       symbol := "B"
       color := "#e8e3d8"
       geometry := "sphere" },
     { id := resourceKey laborCapacityId
       label := "Labor"
       symbol := "L"
       color := "#7e8a95"
       geometry := "octahedron" },
     { id := resourceKey serviceCreditId
       label := "Service credit"
       symbol := "C"
       color := "#74a184"
       geometry := "cube" }]
  accounts :=
    [{ id := accountKey providerAccount
       label := "Provider"
       kind := "participant"
       color := "#c2a15c"
       position := position (-10.5) 0 (-4.2) },
     { id := accountKey escrowAccount
       label := "Process custody"
       kind := "custody"
       color := "#6f6250"
       position := position (-6.4) 0 (-2.1) },
     { id := accountKey machineAccount
       label := "Machine inventory"
       kind := "machine-inventory"
       color := "#7e8a95"
       position := position 0 0 0 },
     { id := accountKey workerAccount
       label := "Worker"
       kind := "participant"
       color := "#e8e3d8"
       position := position (-10.2) 0 5.2 },
     { id := accountKey workerCustodyAccount
       label := "Worker custody"
       kind := "custody"
       color := "#68737d"
       position := position (-5.8) 0 4.7 },
     { id := accountKey outputCustodyAccount
       label := "Output custody"
       kind := "custody"
       color := "#667d6e"
       position := position 6.1 0 (-2.1) },
     { id := accountKey operatorAccount
       label := "Operator"
       kind := "participant"
       color := "#9a958a"
       position := position 10.2 0 4.8 },
     { id := accountKey collectorAccount
       label := "Collector"
       kind := "participant"
       color := "#918c82"
       position := position 10.5 0 (-4.2) }]
  machines :=
    [{ id := projection.machineId
       label := "Foundry service machine"
       color := "#555b60"
       position := position 0 0 0 }]
  camera :=
    { position := position 16 16.5 22.5
      target := position 0 0 0 }

def refuelLifecycle : Visualization.Scenario resourceCatalog schema operationLanguage where
  id := "foundry-refuel-lifecycle"
  gameId := "foundry"
  title := "Refuel lifecycle"
  summary :=
    "Body presence admits work, fuel and labor move through custody and queues, then outputs are collected."
  initial := initialState
  program := Refuel.program
  presentation := presentation

def activePresenceProgram : List (OperationProposal schema operationLanguage) :=
  [Refuel.enterMachine,
   Refuel.reserveFuel,
   Refuel.leaveMachine,
   Refuel.dispatchRefuel,
   Refuel.enterMachine,
   Refuel.dispatchRefuelAt 1,
   Refuel.leaveMachineAt 1,
   Refuel.cancelActiveRefuel,
   Refuel.leaveMachineAt 1]

def activePresence : Visualization.Scenario resourceCatalog schema operationLanguage where
  id := "foundry-active-presence"
  gameId := "foundry"
  title := "Active presence boundary"
  summary :=
    "Queued work permits departure; active work requires a continuously held Body session and rejects premature departure."
  initial := concurrencyState
  program := activePresenceProgram
  presentation := presentation

def operatingGuards : Visualization.Scenario resourceCatalog schema operationLanguage where
  id := "foundry-operating-guards"
  gameId := "foundry"
  title := "Proof-carrying operating guards"
  summary :=
    "Idle and active conditions explain start, stop, reactive failure, and repair acceptance or rejection."
  initial := concurrencyState
  program := Refuel.operatingGuardProgram
  presentation := presentation

def workcellPresentation : PresentationView where
  theme := presentation.theme
  resources := presentation.resources
  accounts :=
    (presentation.accounts.map fun account =>
      if account.id = accountKey machineAccount then
        { account with
          label := "Primary machine inventory"
          position := position (-5.4) 0 0 }
      else account) ++
      [{ id := accountKey Workcell.secondaryMachineAccount
         label := "Secondary machine inventory"
         kind := "machine-inventory"
         color := "#6f777d"
         position := position 5.4 0 0 }]
  machines :=
    [{ id := (workcellProjection .primary).machineId
       label := "Primary service machine"
       color := "#555b60"
       position := position (-5.4) 0 0
       modes :=
         [{ mode := "running", activity := some "running" },
          { mode := "broken", activity := some "damaged" }] },
     { id := (workcellProjection .secondary).machineId
       label := "Secondary service machine"
       color := "#6f777d"
       position := position 5.4 0 0
       modes :=
         [{ mode := "running", activity := some "running" },
          { mode := "broken", activity := some "damaged" }] }]
  camera :=
    { position := position 18 18.5 26
      target := position 0 0 0 }

def projectWorkcellState (state : Workcell.State) : StateView :=
  let primary := projectState (workcellProjection .primary)
    (state.primary.toState state.accounts state.primaryBacked)
  let secondary := projectState (workcellProjection .secondary)
    (state.secondary.toState state.accounts state.secondaryBacked)
  { holdings := primary.holdings
    machines := primary.machines ++ secondary.machines
    custody := primary.custody ++ secondary.custody
    nextProcessId := exactNat (max state.primary.nextProcessId
      state.secondary.nextProcessId) }

private def workcellIssueViews : Workcell.Issue → List IssueView
  | .operationRejected _ issues => issues.map issueView
  | .unrelatedInventoryTouched station account =>
      [{ code := "unrelated-inventory-touched"
         detail :=
           s!"{reprStr station} operation touched protected account {account.value}" }]

private def workcellRejectedChecks : Workcell.Issue → List CheckView
  | .operationRejected _ issues => issues.flatMap rejectedCheckViews
  | .unrelatedInventoryTouched _ _ => []

def applyWorkcellIntent
    (state : Workcell.State)
    (intent : Workcell.Intent) : ApplicationStepResult Workcell.State :=
  let selected := workcellProjection intent.station
  let definition := operationLanguage.definition intent.operation.operation
  let operation := selected.operationName intent.operation.operation
  match Workcell.applyIntent state intent with
  | .error issues =>
      { after := state
        operation
        trigger := triggerName definition.trigger
        status := "rejected"
        semanticStatus := "lean-rejected-no-successor"
        checks := issues.flatMap workcellRejectedChecks
        effects := []
        issues := issues.flatMap workcellIssueViews }
  | .ok applied =>
      { after := applied.after
        operation
        trigger := triggerName definition.trigger
        status := "accepted"
        semanticStatus := "lean-proved-direct-replay"
        checks := applied.receipt.operation.checks.map acceptedCheckView
        effects := applied.receipt.operation.effects.map
          (effectView selected.machineId)
        issues := [] }

def workcellProvenance : ProvenanceView where
  engine := leanProvenance.engine
  toolchain := leanProvenance.toolchain
  guarantees := leanProvenance.guarantees ++
    ["Foundry owns the workcell composition",
     "both stations operate over one authoritative account state",
     "a rejected station intent exposes no successor",
     "unique resources cannot occupy two distinct inventory accounts"]

def bodyContention :
    Visualization.ApplicationScenario Workcell.State Workcell.Intent where
  id := "foundry-workcell-body-contention"
  gameId := "foundry"
  title := "Shared-account Body contention"
  summary :=
    "Two Foundry-owned workcell stations share one account state; the first acquires the unique Body and the second rejects without mutation."
  initial := Workcell.initialState
  program := [Workcell.enterPrimary, Workcell.enterSecondary]
  presentation := workcellPresentation
  provenance := workcellProvenance
  projectState := projectWorkcellState
  applyIntent := applyWorkcellIntent

/-! ## Foundry Control Room command projection -/

def controlRoomPresentation : PresentationView :=
  { workcellPresentation with
      theme :=
        { background := "#080d12"
          surface := "#111a20"
          accent := "#6dd7ff" }
      machines :=
        workcellPresentation.machines.map fun machine =>
          if machine.id = (workcellProjection .primary).machineId then
            { machine with label := "Primary service line", color := "#58b8d8" }
          else
            { machine with label := "Secondary service line", color := "#e3a84e" } }

def projectControlRoomState
    (timeline : TimelineState Workcell.State Workcell.Intent) : StateView :=
  { projectWorkcellState timeline.application with
      logicalTick := some (exactNat timeline.tick.value)
      pendingIntents := some (exactNat timeline.pending.length) }

def controlRoomIntentName (intent : Workcell.Intent) : String :=
  let station := match intent.station with
    | .primary => "Primary"
    | .secondary => "Secondary"
  s!"{station}: {operationName intent.operation.operation}"

def controlRoomMachineId (station : Workcell.Station) : String :=
  (workcellProjection station).machineId

def controlRoomCandidate
    (before : Workcell.State)
    (spec : ControlRoom.CandidateSpec) : CommandCandidateView :=
  let selected := workcellProjection spec.candidate.payload.station
  match assessCandidate Workcell.executor before spec.candidate with
  | { assessment := .accepted applied, .. } =>
      let receipt := applied.receipt.operation
      { id := exactNat spec.candidate.id.value
        actor := exactNat spec.candidate.actor.value
        component := selected.machineId
        label := spec.label
        detail := spec.detail
        status := "accepted"
        checks :=
          { kind := "candidate-assessment"
            condition := spec.label
            status := "accepted"
            detail := "the candidate carries a proof-backed successor" } ::
          receipt.operation.checks.map acceptedCheckView
        effects := receipt.operation.effects.map (effectView selected.machineId)
        issues := [] }
  | { assessment := .rejected issues, .. } =>
      { id := exactNat spec.candidate.id.value
        actor := exactNat spec.candidate.actor.value
        component := selected.machineId
        label := spec.label
        detail := spec.detail
        status := "rejected"
        checks :=
          { kind := "candidate-assessment"
            condition := spec.label
            status := "rejected"
            detail := "the candidate exposes every issue and no successor" } ::
          issues.flatMap workcellRejectedChecks
        effects := []
        issues := issues.flatMap workcellIssueViews }

private def inputCount
    (runtime : MachineRuntime schema operationLanguage) : Nat :=
  runtime.machine.inputQueues.foldl
    (fun total queue => total + queue.contents.length) 0

private def processingCount
    (runtime : MachineRuntime schema operationLanguage) : Nat :=
  runtime.machine.processingQueues.foldl
    (fun total queue => total + queue.contents.length) 0

private def metric
    (id label : String)
    (value : Nat)
    (unit : Option String := none) : CommandMetricView where
  id
  label
  value := exactNat value
  unit

def controlRoomMetrics (snapshot : ControlRoom.Snapshot) : List CommandMetricView :=
  let state := snapshot.timeline.application
  let balance := state.accounts.balance
  [metric "fuel-available" "Fuel available" (balance providerAccount fuelId).atoms
      (some "L"),
   metric "fuel-reserved" "Fuel reserved" (balance escrowAccount fuelId).atoms
      (some "L"),
   metric "fuel-delivered" "Fuel delivered"
      ((balance machineAccount fuelId).atoms +
       (balance Workcell.secondaryMachineAccount fuelId).atoms) (some "L"),
   metric "backlog" "Queued backlog"
      (inputCount state.primary + inputCount state.secondary),
   metric "active-work" "Active work"
      (processingCount state.primary + processingCount state.secondary),
   metric "service-credits" "Service credits"
      ((balance operatorAccount serviceCreditId).atoms +
       (balance collectorAccount serviceCreditId).atoms),
   metric "operator-location" "Operator location"
      (if (balance workerAccount workerBodyId).atoms = 1 then 0
       else if (balance machineAccount workerBodyId).atoms = 1 then 1
       else if (balance Workcell.secondaryMachineAccount workerBodyId).atoms = 1 then 2
       else 3)]

def controlRoomStateKey (snapshot : ControlRoom.Snapshot) : String :=
  let state := snapshot.timeline.application
  s!"{snapshot.timeline.tick.value}|{modeName state.primary.mode}|" ++
    s!"{modeName state.secondary.mode}|" ++
    String.intercalate ":" (controlRoomMetrics snapshot |>.map fun item => item.value)

def controlRoomOutcomeName : ControlRoom.Outcome → String
  | .active => "active"
  | .productive => "productive"
  | .recovered => "recovered"
  | .backlog => "backlog"
  | .conserved => "conserved"
  | .deferred => "deferred"
  | .maintained => "maintained"

def projectControlRoomNode (node : ControlRoom.Node) : CommandNodeView where
  id := exactNat node.snapshot.id.value
  stateKey := controlRoomStateKey node.snapshot
  title := node.title
  summary := node.summary
  outcome := controlRoomOutcomeName node.outcome
  state := projectControlRoomState node.snapshot.timeline
  metrics := controlRoomMetrics node.snapshot
  candidates := node.candidates.map
    (controlRoomCandidate node.snapshot.timeline.application)

private def controlRoomRejectionName : IntentRejectionKind → String
  | .invalidAtSnapshot => "snapshot eligibility"
  | .lostConflict => "canonical conflict arbitration"

def controlRoomEventChecks
    (processed : List (ScheduledIntent Workcell.Intent))
    (event : TimelineEvent Workcell.Issue Workcell.ScheduledReceipt) : List CheckView :=
  let label :=
    match processed.find? fun intent => intent.id.value == event.intentId.value with
    | some intent => controlRoomIntentName intent.payload
    | none => s!"intent {event.intentId.value}"
  match event.outcome with
  | .accepted receipt =>
      { kind := "scheduler"
        condition := label
        status := "accepted"
        detail := s!"{label} committed at event sequence {event.sequence}" } ::
      receipt.operation.operation.checks.map acceptedCheckView
  | .rejected kind issues =>
      { kind := "scheduler"
        condition := label
        status := "rejected"
        detail := s!"{label} rejected by {controlRoomRejectionName kind}" } ::
      issues.flatMap workcellRejectedChecks

def controlRoomEventEffects
    (event : TimelineEvent Workcell.Issue Workcell.ScheduledReceipt) : List EffectView :=
  match event.outcome with
  | .accepted receipt =>
      receipt.operation.operation.effects.map
        (effectView (controlRoomMachineId receipt.operation.station))
  | .rejected _ _ => []

def controlRoomEventIssues
    (event : TimelineEvent Workcell.Issue Workcell.ScheduledReceipt) : List IssueView :=
  match event.outcome with
  | .accepted _ => []
  | .rejected _ issues => issues.flatMap workcellIssueViews

def controlRoomEventAccepted
    (event : TimelineEvent Workcell.Issue Workcell.ScheduledReceipt) : Bool :=
  match event.outcome with
  | .accepted _ => true
  | .rejected _ _ => false

def controlRoomTickStatus
    (events : List (TimelineEvent Workcell.Issue Workcell.ScheduledReceipt)) : String :=
  if events.any controlRoomEventAccepted && events.any (!controlRoomEventAccepted ·) then
    "mixed"
  else if events.any (!controlRoomEventAccepted ·) then "rejected"
  else "accepted"

def projectControlRoomStep
    (index : Nat)
    (step : Maquina.CommandGraphStep Workcell.executor ControlRoom.initialState) :
    StepView :=
  let operation :=
    match step.processed.map fun intent => controlRoomIntentName intent.payload with
    | [name] => name
    | names => s!"resolve {names.length} simultaneous station orders"
  { index
    operation
    trigger := "command-fork"
    status := controlRoomTickStatus step.events
    semanticStatus := "lean-proved-command-fork-replay"
    logicalTick := some (exactNat step.parent.timeline.tick.value)
    eventSequences := step.events.map fun event => exactNat event.sequence
    intentIds := step.events.map fun event => exactNat event.intentId.value
    before := projectControlRoomState step.parent.timeline
    after := projectControlRoomState step.child.timeline
    checks := step.events.flatMap (controlRoomEventChecks step.processed)
    effects := step.events.flatMap controlRoomEventEffects
    issues := step.events.flatMap controlRoomEventIssues }

def projectControlRoomResolution
    (resolution : ControlRoom.Resolution) : CommandResolutionView :=
  let proved := resolution.proof
  { id := exactNat proved.id
    source := exactNat proved.source.snapshot.id.value
    target := exactNat proved.target.snapshot.id.value
    label := resolution.label
    summary := resolution.summary
    actionIds := proved.actionIds.map fun id => exactNat id.value
    automaticOrders := resolution.automaticOrders
    steps := proved.steps.mapIdx fun index step => projectControlRoomStep (index + 1) step }

def controlRoomCommandGraph : CommandGraphView :=
  projectCommandGraph (exactNat ControlRoom.operatorActor.value)
    (exactNat ControlRoom.rootSnapshot.id.value)
    ControlRoom.nodes ControlRoom.resolutions projectControlRoomNode
      projectControlRoomResolution

def controlRoomProvenance : ProvenanceView where
  engine := leanProvenance.engine
  toolchain := leanProvenance.toolchain
  guarantees := workcellProvenance.guarantees ++
    ["command nodes store assessment at their exact immutable snapshot",
     "every accepted candidate is covered by a graph resolution",
     "selected actions exactly match the first scheduler tick",
     "every edge is a nonempty connected path of replay-exact logical ticks",
     "terminal nodes are exactly nodes without accepted commands",
     "canonical same-tick arbitration produces deterministic conflict results"]

def controlRoomArtifact : ScenarioArtifact where
  schemaVersion := protocolVersion
  id := "foundry-control-room"
  gameId := "foundry"
  title := "Foundry Control Room"
  summary :=
    "Command two isolated service lines sharing one operator, bounded fuel, labor, queue capacity, output, and deterministic failure recovery."
  presentation := controlRoomPresentation
  provenance := controlRoomProvenance
  initial := projectControlRoomState ControlRoom.initialTimeline
  steps := []
  commandGraph := some controlRoomCommandGraph

def artifacts : List ScenarioArtifact :=
  [projectScenario projection evaluateGuard refuelLifecycle,
   projectScenario projection evaluateGuard activePresence,
   projectScenario projection evaluateGuard operatingGuards,
   projectApplicationScenario bodyContention,
   controlRoomArtifact]

end Maquina.Games.Foundry.Showcase
