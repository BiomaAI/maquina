import FoundrySim.Workcell
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
       position := position (-5.4) 0 0 },
     { id := (workcellProjection .secondary).machineId
       label := "Secondary service machine"
       color := "#6f777d"
       position := position 5.4 0 0 }]
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

def artifacts : List ScenarioArtifact :=
  [projectScenario projection evaluateGuard refuelLifecycle,
   projectScenario projection evaluateGuard activePresence,
   projectScenario projection evaluateGuard operatingGuards,
   projectApplicationScenario bodyContention]

end Maquina.Games.Foundry.Showcase
