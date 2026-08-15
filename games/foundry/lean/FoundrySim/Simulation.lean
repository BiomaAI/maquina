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

end Maquina.Games.Foundry.Simulation
