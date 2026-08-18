import FoundrySim.Simulation
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

private def position (x y z : Float) : Vec3 := { x, y, z }

def presentation : PresentationView where
  theme :=
    { background := "#07110f"
      surface := "#10201b"
      accent := "#f4b860" }
  resources :=
    [{ id := resourceKey fuelId
       label := "Fuel"
       symbol := "F"
       color := "#f4b860"
       geometry := "cylinder"
       unit := some "L" },
     { id := resourceKey workerBodyId
       label := "Body"
       symbol := "B"
       color := "#65d6ad"
       geometry := "sphere" },
     { id := resourceKey laborCapacityId
       label := "Labor"
       symbol := "L"
       color := "#79a9ff"
       geometry := "octahedron" },
     { id := resourceKey serviceCreditId
       label := "Service credit"
       symbol := "C"
       color := "#df86ff"
       geometry := "cube" }]
  accounts :=
    [{ id := accountKey providerAccount
       label := "Provider"
       kind := "participant"
       color := "#d99a4e"
       position := position (-8) 0 (-3) },
     { id := accountKey escrowAccount
       label := "Process custody"
       kind := "custody"
       color := "#9b794e"
       position := position (-4.7) 0 (-1.5) },
     { id := accountKey machineAccount
       label := "Machine inventory"
       kind := "machine-inventory"
       color := "#5ec4a3"
       position := position 0 0 0 },
     { id := accountKey workerAccount
       label := "Worker"
       kind := "participant"
       color := "#4cbf94"
       position := position (-7.5) 0 4 },
     { id := accountKey workerCustodyAccount
       label := "Worker custody"
       kind := "custody"
       color := "#558dcf"
       position := position (-3.8) 0 3.8 },
     { id := accountKey outputCustodyAccount
       label := "Output custody"
       kind := "custody"
       color := "#a56cc1"
       position := position 4.1 0 (-1.2) },
     { id := accountKey operatorAccount
       label := "Operator"
       kind := "participant"
       color := "#bd70d9"
       position := position 7.4 0 3.5 },
     { id := accountKey collectorAccount
       label := "Collector"
       kind := "participant"
       color := "#d86aa5"
       position := position 7.6 0 (-3.4) }]
  machines :=
    [{ id := projection.machineId
       label := "Foundry service machine"
       color := "#3e806d"
       position := position 0 0 0 }]
  camera :=
    { position := position 13 14 18
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

def artifacts : List ScenarioArtifact :=
  [projectScenario projection evaluateGuard refuelLifecycle,
   projectScenario projection evaluateGuard activePresence]

end Maquina.Games.Foundry.Showcase
