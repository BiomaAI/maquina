import Maquina.MultiMachine
import FoundrySim.Simulation

/-!
# Foundry Multi-Machine World

Two service machines share one authoritative Foundry world and contend for the
same unique Worker Body. The first targeted entry succeeds, the second rejects
without a successor, and a two-intent transaction rolls its accepted prefix
back at the authoritative boundary.
-/

namespace Maquina.Games.Foundry.MultiMachine

open Refuel Simulation

def primaryMachineId : MachineId := ⟨0⟩
def secondaryMachineId : MachineId := ⟨1⟩
def missingMachineId : MachineId := ⟨99⟩

def secondaryMachineAccount : AccountId := ⟨2001⟩

def secondaryMachine : Machine schema :=
  { Simulation.machine with inventory := secondaryMachineAccount }

def secondaryState :
    SimulatorState resourceCatalog schema operationLanguage where
  world := initialWorld
  mode := .running
  machine := secondaryMachine
  custody := MachineCustody.empty secondaryMachine.inventory
  custodyBacked :=
    MachineCustody.backed_empty initialWorld secondaryMachine.inventory
  activeCustodyHeld := by
    simp [Machine.ActiveDependenciesSatisfy, secondaryMachine,
      Simulation.machine, MachineProcessingQueue.DependenciesSatisfy,
      MachineProcessingQueue.activeCustodyDependencies, processingQueue,
      MachineProcessingQueue.empty, Queue.empty]
  nextProcessId := 0

def primaryWorldMachine :
    WorldMachine resourceCatalog schema operationLanguage initialWorld :=
  WorldMachine.ofSimulatorState primaryMachineId initialState

def secondaryWorldMachine :
    WorldMachine resourceCatalog schema operationLanguage initialWorld :=
  WorldMachine.ofSimulatorState secondaryMachineId secondaryState

def initialMultiMachineState :
    MultiMachineState resourceCatalog schema operationLanguage where
  world := initialWorld
  machines := [primaryWorldMachine, secondaryWorldMachine]
  machineIdsUnique := by decide
  machineInventoriesUnique := by decide

def enterPrimary : TargetedOperationProposal schema operationLanguage where
  target := primaryMachineId
  operation := Refuel.enterMachine

def enterSecondary : TargetedOperationProposal schema operationLanguage where
  target := secondaryMachineId
  operation := Refuel.enterMachine

def enterMissing : TargetedOperationProposal schema operationLanguage where
  target := missingMachineId
  operation := Refuel.enterMachine

def primaryEntryRun :=
  applyWorldOperation evaluateGuard initialMultiMachineState enterPrimary

def afterPrimaryEntry :
    MultiMachineState resourceCatalog schema operationLanguage :=
  match primaryEntryRun with
  | .ok applied => applied.after
  | .error _ => initialMultiMachineState

def secondaryEntryRun :=
  applyWorldOperation evaluateGuard afterPrimaryEntry enterSecondary

def secondaryEntryIssues : Option (List MultiMachineIssue) :=
  match secondaryEntryRun with
  | .error issues => some issues
  | .ok _ => none

def missingEntryIssues : Option (List MultiMachineIssue) :=
  match applyWorldOperation evaluateGuard initialMultiMachineState enterMissing with
  | .error issues => some issues
  | .ok _ => none

def contendedEntryTransaction : WorldTransaction schema operationLanguage where
  intents := [enterPrimary, enterSecondary]

def contendedTransactionRun :=
  applyWorldTransaction evaluateGuard initialMultiMachineState
    contendedEntryTransaction

def contendedTransactionIssues : Option (List WorldTransactionIssue) :=
  match contendedTransactionRun with
  | .error issues => some issues
  | .ok _ => none

example :
    initialMultiMachineState.machines.map WorldMachine.id =
      [primaryMachineId, secondaryMachineId] := rfl

example :
    (afterPrimaryEntry.world.balance machineAccount workerBodyId).atoms = 1 := by
  native_decide

example :
    (afterPrimaryEntry.world.balance secondaryMachineAccount workerBodyId).atoms = 0 := by
  native_decide

example :
    (afterPrimaryEntry.world.balance workerAccount workerBodyId).atoms = 0 := by
  native_decide

example :
    secondaryEntryIssues =
      some [.operationRejected secondaryMachineId
        [.transferRejected [.shortfall workerBodyId 1 0 1]]] := by
  native_decide

example :
    worldOperationSuccessor evaluateGuard afterPrimaryEntry enterSecondary =
      none := by
  native_decide

example :
    missingEntryIssues = some [.machineMissing missingMachineId] := by
  native_decide

example :
    contendedTransactionIssues =
      some [.intentRejected 1 secondaryMachineId
        [.operationRejected secondaryMachineId
          [.transferRejected [.shortfall workerBodyId 1 0 1]]]] := by
  native_decide

example :
    worldTransactionSuccessor evaluateGuard initialMultiMachineState
      contendedEntryTransaction = none := by
  native_decide

/-- The closed world inherits the universal unique-resource exclusion theorem. -/
example
    (left right : WorldMachine resourceCatalog schema operationLanguage
      afterPrimaryEntry.world)
    (leftMem : left ∈ afterPrimaryEntry.machines)
    (rightMem : right ∈ afterPrimaryEntry.machines)
    (different : left.id ≠ right.id)
    (leftHeld :
      (afterPrimaryEntry.world.balance left.inventory workerBodyId).atoms = 1)
    (rightHeld :
      (afterPrimaryEntry.world.balance right.inventory workerBodyId).atoms = 1) :
    False :=
  afterPrimaryEntry.uniqueResource_not_held_by_distinctMachines
    { id := workerBodyId, name := "worker body" }
    (by rfl) left right leftMem rightMem different leftHeld rightHeld

end Maquina.Games.Foundry.MultiMachine
