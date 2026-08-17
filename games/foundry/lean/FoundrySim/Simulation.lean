import FoundrySim.Refuel

/-!
# Foundry Generic Simulation

This file supplies only initial data. `Maquina.applyOperations` executes the
game without any Foundry-specific transition functions.
-/

namespace Maquina.Games.Foundry.Simulation

open Refuel

def initialDeltas : List InventoryDelta :=
  [ .credit providerAccount
      { resourceId := fuelId, quantity := refuelQuantity, positive := by decide },
    .credit workerAccount
      { resourceId := workerBodyId, quantity := .one, positive := by decide },
    .credit workerAccount
      { resourceId := laborCapacityId, quantity := .one, positive := by decide } ]

def initialWorld : WorldState resourceCatalog :=
  match applyInventoryProgram (WorldState.empty resourceCatalog) initialDeltas with
  | .ok applied => applied.after
  | .error _ => WorldState.empty resourceCatalog

def concurrencyDeltas : List InventoryDelta :=
  [ .credit providerAccount
      { resourceId := fuelId, quantity := ⟨20⟩, positive := by decide },
    .credit workerAccount
      { resourceId := workerBodyId, quantity := .one, positive := by decide },
    .credit workerAccount
      { resourceId := laborCapacityId, quantity := .one, positive := by decide } ]

def concurrencyWorld : WorldState resourceCatalog :=
  match applyInventoryProgram (WorldState.empty resourceCatalog) concurrencyDeltas with
  | .ok applied => applied.after
  | .error _ => WorldState.empty resourceCatalog

def inputQueue : MachineInputQueue schema :=
  MachineInputQueue.empty ⟨0⟩ .service (some 1)

def processingQueue : MachineProcessingQueue schema :=
  MachineProcessingQueue.empty ⟨0⟩ .service (some 1)

def outputQueue : MachineOutputQueue schema :=
  MachineOutputQueue.empty ⟨0⟩ .production (some 1)

def machine : Machine schema where
  inventory := machineAccount
  maximumQueues := 3
  inputQueues := [inputQueue]
  processingQueues := [processingQueue]
  outputQueues := [outputQueue]
  inputIdsUnique := by simp
  processingIdsUnique := by simp
  outputIdsUnique := by simp
  nextInputQueueId := 1
  nextProcessingQueueId := 1
  nextOutputQueueId := 1
  inputIdsBeforeNext := by
    intro queue queueMem
    simp only [List.mem_singleton] at queueMem
    subst queue
    decide
  processingIdsBeforeNext := by
    intro queue queueMem
    simp only [List.mem_singleton] at queueMem
    subst queue
    decide
  outputIdsBeforeNext := by
    intro queue queueMem
    simp only [List.mem_singleton] at queueMem
    subst queue
    decide
  withinQueueLimit := by decide

def initialState : SimulatorState resourceCatalog schema operationLanguage where
  world := initialWorld
  mode := .running
  machine := machine
  custody := MachineCustody.empty machine.inventory
  custodyBacked := MachineCustody.backed_empty initialWorld machine.inventory
  nextProcessId := 0

def evaluateGuard
    (guard : Guard)
    (_state : SimulatorState resourceCatalog schema operationLanguage) : Bool :=
  nomatch guard

def run := applyOperations evaluateGuard initialState Refuel.program

def finalState : SimulatorState resourceCatalog schema operationLanguage :=
  match run with
  | .ok applied => applied.after
  | .error _ => initialState

def productionRun :=
  applyOperations evaluateGuard initialState
    [Refuel.enterMachine, Refuel.reserveFuel, Refuel.dispatchRefuel,
      Refuel.advanceRefuel, Refuel.completeRefuel]

def productionState : SimulatorState resourceCatalog schema operationLanguage :=
  match productionRun with
  | .ok applied => applied.after
  | .error _ => initialState

def partialCollectionRun :=
  applyOperations evaluateGuard productionState [Refuel.collectOperatorAllocation]

def partialCollectionState :
    SimulatorState resourceCatalog schema operationLanguage :=
  match partialCollectionRun with
  | .ok applied => applied.after
  | .error _ => productionState

def finishPartialCollectionRun :=
  applyOperations evaluateGuard partialCollectionState [Refuel.collectRefuel]

def finishedPartialCollectionState :
    SimulatorState resourceCatalog schema operationLanguage :=
  match finishPartialCollectionRun with
  | .ok applied => applied.after
  | .error _ => partialCollectionState

def leaveAfterProductionRun :=
  applyOperations evaluateGuard productionState [Refuel.leaveMachine]

def beforeCollectionState :
    SimulatorState resourceCatalog schema operationLanguage :=
  match leaveAfterProductionRun with
  | .ok applied => applied.after
  | .error _ => productionState

def collectionAfterLeave :=
  operationSuccessor evaluateGuard beforeCollectionState Refuel.collectRefuel

def concurrencyState : SimulatorState resourceCatalog schema operationLanguage :=
  { initialState with world := concurrencyWorld }

def concurrencyOccupancyRun :=
  applyOperations evaluateGuard concurrencyState [Refuel.enterMachine]

def occupiedConcurrencyState :
    SimulatorState resourceCatalog schema operationLanguage :=
  match concurrencyOccupancyRun with
  | .ok applied => applied.after
  | .error _ => concurrencyState

def unrelatedBodyTransfer : Transfer where
  source := machineAccount
  destination := operatorAccount
  basket := workerBody

def queuedCancellationRun :=
  applyOperations evaluateGuard concurrencyState
    [Refuel.enterMachine, Refuel.reserveFuel, Refuel.cancelQueuedRefuel]

def queuedCancellationState :
    SimulatorState resourceCatalog schema operationLanguage :=
  match queuedCancellationRun with
  | .ok applied => applied.after
  | .error _ => concurrencyState

def activeCancellationRun :=
  applyOperations evaluateGuard concurrencyState
    [Refuel.enterMachine, Refuel.reserveFuel, Refuel.dispatchRefuel,
      Refuel.cancelActiveRefuel]

def activeCancellationState :
    SimulatorState resourceCatalog schema operationLanguage :=
  match activeCancellationRun with
  | .ok applied => applied.after
  | .error _ => concurrencyState

def queuedBehindActiveRun :=
  applyOperations evaluateGuard occupiedConcurrencyState
    [Refuel.reserveFuel, Refuel.dispatchRefuel, Refuel.reserveFuel]

def queuedBehindActive :
    SimulatorState resourceCatalog schema operationLanguage :=
  match queuedBehindActiveRun with
  | .ok applied => applied.after
  | .error _ => occupiedConcurrencyState

def operationIssues
    (state : SimulatorState resourceCatalog schema operationLanguage)
    (proposal : OperationProposal schema operationLanguage) :
    Option (List SimulatorIssue) :=
  match applyOperation evaluateGuard state proposal with
  | .error issues => some issues
  | .ok _ => none

def afterFirstCompletionRun :=
  applyOperations evaluateGuard queuedBehindActive
    [Refuel.advanceRefuel, Refuel.completeRefuel]

def afterFirstCompletion :
    SimulatorState resourceCatalog schema operationLanguage :=
  match afterFirstCompletionRun with
  | .ok applied => applied.after
  | .error _ => queuedBehindActive

def secondDispatchRun :=
  applyOperations evaluateGuard afterFirstCompletion
    [Refuel.collectRefuel, Refuel.dispatchRefuel]

def afterSecondDispatch :
    SimulatorState resourceCatalog schema operationLanguage :=
  match secondDispatchRun with
  | .ok applied => applied.after
  | .error _ => afterFirstCompletion

def backpressureReadyRun :=
  applyOperations evaluateGuard concurrencyState
    [Refuel.enterMachine,
     Refuel.reserveFuel,
     Refuel.dispatchRefuel,
     Refuel.reserveFuel,
     Refuel.advanceRefuel,
     Refuel.completeRefuel,
     Refuel.dispatchRefuel,
     Refuel.advanceRefuel]

def backpressureReady :
    SimulatorState resourceCatalog schema operationLanguage :=
  match backpressureReadyRun with
  | .ok applied => applied.after
  | .error _ => concurrencyState

def repeatedProgram : List (OperationProposal schema operationLanguage) :=
  [Refuel.enterMachine,
   Refuel.reserveFuel,
   Refuel.dispatchRefuel,
   Refuel.reserveFuel,
   Refuel.advanceRefuel,
   Refuel.completeRefuel,
   Refuel.collectRefuel,
   Refuel.dispatchRefuel,
   Refuel.advanceRefuel,
   Refuel.completeRefuel,
   Refuel.leaveMachine,
   Refuel.collectRefuel]

def repeatedRun :=
  applyOperations evaluateGuard concurrencyState repeatedProgram

def repeatedFinal :
    SimulatorState resourceCatalog schema operationLanguage :=
  match repeatedRun with
  | .ok applied => applied.after
  | .error _ => concurrencyState

def replayedRepeated :
    Option (SimulatorState resourceCatalog schema operationLanguage) :=
  match repeatedRun with
  | .ok applied =>
      replayOperationReceipts evaluateGuard concurrencyState applied.receipts
  | .error _ => none

def replayedFinal : Option (SimulatorState resourceCatalog schema operationLanguage) :=
  match run with
  | .ok applied => replayOperationReceipts evaluateGuard initialState applied.receipts
  | .error _ => none

def upgradeMachine : Machine schema where
  inventory := machine.inventory
  maximumQueues := 4
  inputQueues := machine.inputQueues
  processingQueues := machine.processingQueues
  outputQueues := machine.outputQueues
  inputIdsUnique := machine.inputIdsUnique
  processingIdsUnique := machine.processingIdsUnique
  outputIdsUnique := machine.outputIdsUnique
  nextInputQueueId := machine.nextInputQueueId
  nextProcessingQueueId := machine.nextProcessingQueueId
  nextOutputQueueId := machine.nextOutputQueueId
  inputIdsBeforeNext := machine.inputIdsBeforeNext
  processingIdsBeforeNext := machine.processingIdsBeforeNext
  outputIdsBeforeNext := machine.outputIdsBeforeNext
  withinQueueLimit := by native_decide

def upgradeState : SimulatorState resourceCatalog schema operationLanguage :=
  { initialState with machine := upgradeMachine }

def topologyRun :=
  applyOperations evaluateGuard upgradeState
    [Refuel.addServiceInput, Refuel.removeServiceInput]

def topologyFinal : SimulatorState resourceCatalog schema operationLanguage :=
  match topologyRun with
  | .ok applied => applied.after
  | .error _ => upgradeState

example : (initialWorld.balance providerAccount fuelId).atoms = 10 := by
  native_decide

example : (finalState.world.balance providerAccount fuelId).atoms = 0 := by
  native_decide

example : (finalState.world.balance escrowAccount fuelId).atoms = 0 := by
  native_decide

example : (finalState.world.balance machineAccount fuelId).atoms = 10 := by
  native_decide

example : (finalState.world.balance workerAccount workerBodyId).atoms = 1 := by
  native_decide

example : (finalState.world.balance workerAccount laborCapacityId).atoms = 1 := by
  native_decide

example :
    (productionState.world.balance workerAccount workerBodyId).atoms = 0 := by
  native_decide

example :
    (productionState.world.balance machineAccount workerBodyId).atoms = 1 := by
  native_decide

example :
    (productionState.custody.position? 0).map CustodyPosition.source =
      some workerAccount := by
  native_decide

example :
    (beforeCollectionState.world.balance workerAccount workerBodyId).atoms = 1 := by
  native_decide

example :
    (beforeCollectionState.world.balance machineAccount workerBodyId).atoms = 0 := by
  native_decide

example :
    (beforeCollectionState.machine.outputQueue? ⟨0⟩).map
      (fun queue => queue.contents.length) = some 1 := by
  native_decide

example :
    collectionAfterLeave.map
      (fun state => (state.world.balance machineAccount fuelId).atoms) = some 10 := by
  native_decide

example :
    collectionAfterLeave.map
      (fun state => (state.world.balance collectorAccount serviceCreditId).atoms) =
      some 1 := by
  native_decide

example :
    (productionState.world.balance workerCustodyAccount workerBodyId).atoms = 0 := by
  native_decide

example :
    (productionState.machine.outputQueue? ⟨0⟩).bind
      (fun queue => queue.contents.front?.map fun ticketed =>
      ticketed.value.process.active.queued.reservations.length) = some 0 := by
  native_decide

example :
    (partialCollectionState.world.balance operatorAccount serviceCreditId).atoms =
      1 := by
  native_decide

example :
    (partialCollectionState.machine.outputQueue? ⟨0⟩).bind
      (fun queue => queue.contents.front?.map fun ticketed =>
        ticketed.value.allocations.length) = some 2 := by
  native_decide

example :
    operationSuccessor evaluateGuard partialCollectionState
      Refuel.collectOperatorAllocation = none := by
  native_decide

example :
    (finishedPartialCollectionState.world.balance machineAccount fuelId).atoms =
      10 := by
  native_decide

example :
    (finishedPartialCollectionState.world.balance collectorAccount
      serviceCreditId).atoms = 1 := by
  native_decide

example :
    (finishedPartialCollectionState.machine.outputQueue? ⟨0⟩).map
      (fun queue => queue.contents.length) = some 0 := by
  native_decide

example :
    operationIssues concurrencyState Refuel.reserveFuel =
      some [.possessionRejected
        [{ account := machineAccount
           issues := [.shortfall workerBodyId 1 0 1] }]] := by
  native_decide

example :
    operationSuccessor evaluateGuard concurrencyState Refuel.reserveFuel = none := by
  native_decide

example :
    (queuedBehindActive.world.balance machineAccount workerBodyId).atoms = 1 := by
  native_decide

example :
    occupiedConcurrencyState.custody.lockedAtoms workerBodyId = 1 := by
  native_decide

example :
    MachineCustody.unlockedAtoms occupiedConcurrencyState.world
      occupiedConcurrencyState.custody workerBodyId = 0 := by
  native_decide

example :
    MachineCustody.custodyTransferSuccessor occupiedConcurrencyState.world
      occupiedConcurrencyState.custody unrelatedBodyTransfer = none := by
  native_decide

example :
    (queuedCancellationState.world.balance providerAccount fuelId).atoms = 20 := by
  native_decide

example :
    (queuedCancellationState.machine.inputQueue? ⟨0⟩).map
      (fun queue => queue.contents.length) = some 0 := by
  native_decide

example :
    (activeCancellationState.world.balance providerAccount fuelId).atoms = 20 := by
  native_decide

example :
    (activeCancellationState.world.balance workerAccount laborCapacityId).atoms =
      1 := by
  native_decide

example :
    (activeCancellationState.machine.processingQueue? ⟨0⟩).map
      (fun queue => queue.contents.length) = some 0 := by
  native_decide

example :
    queuedBehindActive.nextProcessId = 2 := by
  native_decide

example :
    (queuedBehindActive.machine.inputQueue? ⟨0⟩).map
      (fun queue => queue.contents.length) = some 1 := by
  native_decide

example :
    (queuedBehindActive.machine.processingQueue? ⟨0⟩).map
      (fun queue => queue.contents.length) = some 1 := by
  native_decide

example :
    (queuedBehindActive.world.balance workerAccount laborCapacityId).atoms = 0 := by
  native_decide

example :
    operationIssues queuedBehindActive Refuel.dispatchRefuel =
      some [.transferRejected [.shortfall laborCapacityId 1 0 1]] := by
  native_decide

example :
    operationSuccessor evaluateGuard queuedBehindActive Refuel.dispatchRefuel = none := by
  native_decide

example :
    (afterFirstCompletion.world.balance workerAccount laborCapacityId).atoms = 1 := by
  native_decide

example :
    (afterSecondDispatch.world.balance workerAccount laborCapacityId).atoms = 0 := by
  native_decide

example :
    (afterSecondDispatch.machine.inputQueue? ⟨0⟩).map
      (fun queue => queue.contents.length) = some 0 := by
  native_decide

example :
    (afterSecondDispatch.machine.processingQueue? ⟨0⟩).map
      (fun queue => queue.contents.length) = some 1 := by
  native_decide

example :
    (backpressureReady.machine.processingQueue? ⟨0⟩).map
      (fun queue => queue.contents.length) = some 1 := by
  native_decide

example :
    (backpressureReady.machine.outputQueue? ⟨0⟩).map
      (fun queue => queue.contents.length) = some 1 := by
  native_decide

example :
    operationIssues backpressureReady Refuel.completeRefuel =
      some [.queueRejected .output [.full 1 1]] := by
  native_decide

example :
    operationSuccessor evaluateGuard backpressureReady Refuel.completeRefuel =
      none := by
  native_decide

example :
    (repeatedFinal.world.balance machineAccount fuelId).atoms = 20 := by
  native_decide

example :
    (repeatedFinal.world.balance workerAccount workerBodyId).atoms = 1 := by
  native_decide

example :
    (repeatedFinal.world.balance machineAccount workerBodyId).atoms = 0 := by
  native_decide

example : repeatedFinal.custody.positions = [] := by
  native_decide

example : repeatedFinal.custody.nextId = 1 := by
  native_decide

example : repeatedFinal.nextProcessId = 2 := by
  native_decide

example :
    (repeatedFinal.world.balance operatorAccount serviceCreditId).atoms = 2 := by
  native_decide

example :
    (repeatedFinal.world.balance collectorAccount serviceCreditId).atoms = 2 := by
  native_decide

example :
    replayedRepeated.map
      (fun state => (state.world.balance machineAccount fuelId).atoms) = some 20 := by
  native_decide

example :
    operationSuccessor evaluateGuard finalState Refuel.collectRefuel = none := by
  native_decide

example :
    replayedFinal.map
      (fun state => (state.world.balance machineAccount fuelId).atoms) = some 10 := by
  native_decide

example : replayedFinal.map SimulatorState.nextProcessId = some 1 := by
  native_decide

example :
    (finalState.world.balance workerCustodyAccount workerBodyId).atoms = 0 := by
  native_decide

example :
    (finalState.world.balance operatorAccount serviceCreditId).atoms = 1 := by
  native_decide

example :
    (finalState.world.balance collectorAccount serviceCreditId).atoms = 1 := by
  native_decide

example :
    (finalState.machine.inputQueue? ⟨0⟩).map
      (fun queue => queue.contents.length) = some 0 := by
  native_decide

example :
    (finalState.machine.processingQueue? ⟨0⟩).map
      (fun queue => queue.contents.length) = some 0 := by
  native_decide

example :
    (finalState.machine.outputQueue? ⟨0⟩).map
      (fun queue => queue.contents.length) = some 0 := by
  native_decide

example : finalState.nextProcessId = 1 := by
  native_decide

example : topologyFinal.machine.queueCount = 3 := by
  native_decide

example : topologyFinal.machine.nextInputQueueId = 2 := by
  native_decide

example : topologyFinal.machine.inputQueue? ⟨1⟩ = none := by
  native_decide

end Maquina.Games.Foundry.Simulation
