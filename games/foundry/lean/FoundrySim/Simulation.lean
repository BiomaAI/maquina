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
      { resourceId := laborCapacityId, quantity := ⟨2⟩, positive := by decide } ]

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
    [Refuel.reserveFuel, Refuel.dispatchRefuel, Refuel.advanceRefuel,
      Refuel.completeRefuel]

def productionState : SimulatorState resourceCatalog schema operationLanguage :=
  match productionRun with
  | .ok applied => applied.after
  | .error _ => initialState

def concurrencyState : SimulatorState resourceCatalog schema operationLanguage :=
  { initialState with world := concurrencyWorld }

def firstReservationRun :=
  applyOperations evaluateGuard concurrencyState [Refuel.reserveFuel]

def afterFirstReservation :
    SimulatorState resourceCatalog schema operationLanguage :=
  match firstReservationRun with
  | .ok applied => applied.after
  | .error _ => concurrencyState

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
    (productionState.world.balance workerAccount workerBodyId).atoms = 1 := by
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
    (afterFirstReservation.world.balance workerAccount workerBodyId).atoms = 1 := by
  native_decide

example :
    (afterFirstReservation.world.balance workerCustodyAccount workerBodyId).atoms = 0 := by
  native_decide

example :
    operationSuccessor evaluateGuard afterFirstReservation Refuel.reserveFuel = none := by
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
