import FoundrySim.Simulation

/-!
# Foundry Trace Demo

An executable observer for the Foundry declarations. State transitions still
come exclusively from `Maquina.applyOperation`; this module only renders the
generic receipts and selected state projections for a human reader.
-/

namespace Maquina.Games.Foundry.Demo

open Refuel Simulation

def operationText {before after : Mode} (operation : Operation before after) : String :=
  (reprStr operation).replace "Maquina.Games.Foundry.Operation." ""

def proposalText (proposal : OperationProposal schema operationLanguage) : String :=
  operationText proposal.operation

def accountText (account : AccountId) : String :=
  if account = providerAccount then "provider"
  else if account = escrowAccount then "process custody"
  else if account = machineAccount then "machine"
  else if account = workerAccount then "worker"
  else if account = workerCustodyAccount then "worker custody"
  else if account = outputCustodyAccount then "output custody"
  else if account = operatorAccount then "operator"
  else if account = collectorAccount then "collector"
  else s!"account#{account.value}"

def resourceText (resourceId : ResourceId) : String :=
  match resourceCatalog.lookup resourceId with
  | some spec => spec.header.name
  | none => s!"resource#{resourceId.value}"

def stageText : QueueStage → String
  | .input => "input"
  | .processing => "processing"
  | .output => "output"

def outputQueueText : Option Nat → String
  | none => "bound inventories"
  | some queueId => s!"output queue {queueId}"

def cancellationText : CancellationDisposition → String
  | .returnInputs => "return inputs"
  | .consumeInputs => "consume inputs"

def renderCheck : OperationCheckReceipt → List String
  | .guard evidence =>
      [s!"check {evidence.condition}: {evidence.detail}"]
  | .possession _ receipt =>
      receipt.lines.map fun line =>
        s!"check possession: {accountText receipt.account} holds " ++
          s!"{line.required.atoms} {resourceText line.resourceId} " ++
          s!"(available {line.available.atoms})"

def renderEffect : SimulatorEffectReceipt → List String
  | .transfer receipt =>
      receipt.lines.map fun line =>
        s!"transfer {line.quantity.atoms} {resourceText line.resourceId}: " ++
          s!"{accountText receipt.source} {line.sourceBefore.atoms}→{line.sourceAfter.atoms}, " ++
          s!"{accountText receipt.destination} " ++
          s!"{line.destinationBefore.atoms}→{line.destinationAfter.atoms}"
  | .transformation receipt =>
      match receipt.delta with
      | .debit account entry =>
          [s!"consume {entry.quantity.atoms} {resourceText entry.resourceId} from " ++
            s!"{accountText account}: {receipt.accountBefore.atoms}→{receipt.accountAfter.atoms} " ++
            s!"(global {receipt.totalBefore.atoms}→{receipt.totalAfter.atoms})"]
      | .credit account entry =>
          [s!"produce {entry.quantity.atoms} {resourceText entry.resourceId} into " ++
            s!"{accountText account}: {receipt.accountBefore.atoms}→{receipt.accountAfter.atoms} " ++
            s!"(global {receipt.totalBefore.atoms}→{receipt.totalAfter.atoms})"]
  | .enqueued queueId ticket processId =>
      [s!"enqueue process {processId} in input queue {queueId} (ticket {ticket})"]
  | .dispatched inputQueueId processingQueueId processId =>
      [s!"dispatch process {processId}: input queue {inputQueueId} → processing queue {processingQueueId}"]
  | .advanced queueId processId before after =>
      [s!"advance process {processId} in processing queue {queueId}: work {before}→{after}"]
  | .completed processingQueueId outputQueueId processId =>
      [s!"complete process {processId}: processing queue {processingQueueId} → " ++
        outputQueueText outputQueueId]
  | .recipientBound account =>
      [s!"bind late output recipient to {accountText account}"]
  | .collected queueId processId =>
      [s!"collect process {processId} from output queue {queueId}"]
  | .allocationCollected queueId processId remaining =>
      [s!"collect one allocation from process {processId} in output queue " ++
        s!"{queueId} ({remaining} remaining)"]
  | .custodyOpened positionId =>
      [s!"open machine custody position {positionId}"]
  | .custodyClosed positionId =>
      [s!"close machine custody position {positionId}"]
  | .custodyDependenciesBound processId positionIds =>
      [s!"bind process {processId} to active custody positions {positionIds}"]
  | .custodyDependenciesReleased processId positionIds =>
      [s!"release process {processId} from active custody positions {positionIds}"]
  | .reservationsReleased processId =>
      [s!"release reserved inputs for process {processId}"]
  | .cancelled stage queueId processId disposition =>
      [s!"cancel process {processId} from {stageText stage} queue {queueId} " ++
        s!"({cancellationText disposition})"]
  | .queueAdded stage queueId =>
      [s!"add {stageText stage} queue {queueId}"]
  | .queueRemoved stage queueId =>
      [s!"remove {stageText stage} queue {queueId}"]

def inputLength
    (state : SimulatorState resourceCatalog schema operationLanguage) : Nat :=
  (state.machine.inputQueue? ⟨0⟩).map
    (fun queue => queue.contents.length) |>.getD 0

def processingLength
    (state : SimulatorState resourceCatalog schema operationLanguage) : Nat :=
  (state.machine.processingQueue? ⟨0⟩).map
    (fun queue => queue.contents.length) |>.getD 0

def outputLength
    (state : SimulatorState resourceCatalog schema operationLanguage) : Nat :=
  (state.machine.outputQueue? ⟨0⟩).map
    (fun queue => queue.contents.length) |>.getD 0

def printState
    (state : SimulatorState resourceCatalog schema operationLanguage) : IO Unit := do
  let balance := state.world.balance
  IO.println
    (s!"    fuel: provider={balance providerAccount fuelId |>.atoms}, " ++
      s!"process-custody={balance escrowAccount fuelId |>.atoms}, " ++
      s!"output-custody={balance outputCustodyAccount fuelId |>.atoms}, " ++
      s!"machine={balance machineAccount fuelId |>.atoms}")
  IO.println
    (s!"    worker: body={balance workerAccount workerBodyId |>.atoms}, " ++
      s!"labor={balance workerAccount laborCapacityId |>.atoms}; " ++
      s!"machine body={balance machineAccount workerBodyId |>.atoms}; " ++
      s!"custody body={balance workerCustodyAccount workerBodyId |>.atoms}, " ++
      s!"labor={balance workerCustodyAccount laborCapacityId |>.atoms}")
  IO.println
    (s!"    credits: custody={balance outputCustodyAccount serviceCreditId |>.atoms}, " ++
      s!"operator={balance operatorAccount serviceCreditId |>.atoms}, " ++
      s!"collector={balance collectorAccount serviceCreditId |>.atoms}")
  IO.println
    (s!"    queues: input={inputLength state}, processing={processingLength state}, " ++
      s!"output={outputLength state}; custody positions={state.custody.positions.length}")

def runSteps :
    Nat →
    SimulatorState resourceCatalog schema operationLanguage →
    List (OperationProposal schema operationLanguage) →
    IO Unit
  | _, state, [] => do
      IO.println "\ncompleted"
      printState state
  | step, state, proposal :: rest => do
      IO.println s!"\n{step}. {proposalText proposal}"
      match applyOperation evaluateGuard state proposal with
      | .error issues =>
          IO.println s!"  rejected: {reprStr issues}"
          printState state
          runSteps (step + 1) state rest
      | .ok applied =>
          for check in applied.checks do
            for line in renderCheck check do
              IO.println s!"  {line}"
          for effect in applied.effects do
            for line in renderEffect effect do
              IO.println s!"  {line}"
          printState applied.after
          runSteps (step + 1) applied.after rest

def sessionBoundaryProgram :
    List (OperationProposal schema operationLanguage) :=
  [Refuel.enterMachine,
   Refuel.reserveFuel,
   Refuel.leaveMachine,
   Refuel.dispatchRefuel,
   Refuel.enterMachine,
   Refuel.dispatchRefuelAt 1,
   Refuel.leaveMachineAt 1,
   Refuel.cancelActiveRefuel,
   Refuel.leaveMachineAt 1]

def run : IO Unit := do
  IO.println "Foundry refueling trace"
  IO.println "\ninitial state"
  printState initialState
  runSteps 1 initialState Refuel.program
  IO.println "\n\nFoundry active-presence boundary trace"
  IO.println "\ninitial state"
  printState concurrencyState
  runSteps 1 concurrencyState sessionBoundaryProgram
  IO.println "\n\nFoundry proof-carrying operating-guard trace"
  IO.println "\ninitial state"
  printState concurrencyState
  runSteps 1 concurrencyState Refuel.operatingGuardProgram

end Maquina.Games.Foundry.Demo

def main : IO Unit :=
  Maquina.Games.Foundry.Demo.run
