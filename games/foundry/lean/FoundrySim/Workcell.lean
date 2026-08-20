import FoundrySim.Simulation

/-!
# Foundry Workcell

Foundry owns this composition of two independent service runtimes over one
account state. Maquina supplies single-machine execution and account proofs;
it does not define a multiple-machine aggregate.
-/

namespace Maquina.Games.Foundry.Workcell

open Refuel Simulation

inductive Station where
  | primary
  | secondary
  deriving DecidableEq, Repr

def secondaryMachineAccount : AccountId := ⟨2001⟩

def secondaryMachine : Machine schema :=
  { Simulation.machine with inventory := secondaryMachineAccount }

def stationMachineAccount : Station → AccountId
  | .primary => machineAccount
  | .secondary => secondaryMachineAccount

/-- Bind the same declarative operation vocabulary to the targeted station. -/
def processBindingsFor (station : Station) : ProcessBindings Label where
  source
    | .provider => providerAccount
    | .machine => stationMachineAccount station
    | .worker => workerAccount
    | .operator => operatorAccount
    | .collector => collectorAccount
  custody
    | .provider => escrowAccount
    | .machine => outputCustodyAccount
    | .worker => workerCustodyAccount
    | .operator => outputCustodyAccount
    | .collector => outputCustodyAccount
  output
    | .provider => some providerAccount
    | .machine => some (stationMachineAccount station)
    | .worker => some workerAccount
    | .operator => some operatorAccount
    | .collector => none

def possessionBindingsFor (station : Station) : PossessionBindings Label where
  resolve := (processBindingsFor station).source

/--
Targeting is applied at the game boundary. Maquina still receives an ordinary
single-runtime operation plus account bindings; no multi-machine kernel state
is introduced.
-/
def proposalFor
    (station : Station)
    (proposal : OperationProposal schema operationLanguage) :
    OperationProposal schema operationLanguage :=
  { proposal with
      possessionBindings := possessionBindingsFor station
      processBindings := proposal.processBindings.map fun _ => processBindingsFor station }

def secondarySimulatorState :
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

/-- Game-owned composition; the fields may have unrelated runtime types in other games. -/
structure State where
  accounts : WorldState resourceCatalog
  primary : MachineRuntime schema operationLanguage
  secondary : MachineRuntime schema operationLanguage
  primaryBacked : MachineCustody.Backed accounts primary.custody
  secondaryBacked : MachineCustody.Backed accounts secondary.custody

def initialState : State where
  accounts := Simulation.initialWorld
  primary := MachineRuntime.ofState Simulation.initialState
  secondary := MachineRuntime.ofState secondarySimulatorState
  primaryBacked := Simulation.initialState.custodyBacked
  secondaryBacked := secondarySimulatorState.custodyBacked

structure Intent where
  station : Station
  operation : OperationProposal schema operationLanguage

def enterPrimary : Intent where
  station := .primary
  operation := proposalFor .primary Refuel.enterMachine

def enterSecondary : Intent where
  station := .secondary
  operation := proposalFor .secondary Refuel.enterMachine

inductive Issue where
  | operationRejected (station : Station) (issues : List SimulatorIssue)
  | unrelatedInventoryTouched (station : Station) (account : AccountId)
  deriving DecidableEq, Repr

structure Receipt where
  station : Station
  operation : OperationReceipt schema operationLanguage
  direct : DirectEffectReceipt schema operationLanguage

structure AppliedIntent (before : State) (intent : Intent) where
  after : State
  receipt : Receipt
  worldEffects : List WorldEffectReceipt
  worldReplayExact :
    replayWorldEffectReceipts worldEffects before.accounts.holdings =
      after.accounts.holdings

def applyIntent
    (before : State)
    (intent : Intent) : Except (List Issue) (AppliedIntent before intent) :=
  let proposal := proposalFor intent.station intent.operation
  match intent.station with
  | .primary =>
      match applyRuntimeOperation evaluateGuard before.accounts before.primary
          before.primaryBacked proposal with
      | .error issues => .error [.operationRejected .primary issues]
      | .ok applied =>
          if untouched : worldEffectsLeaveAccountUntouched applied.worldEffects
              before.secondary.machine.inventory = true then
            let secondaryBacked :=
              before.secondaryBacked.replayWorldEffects_untouched
                applied.worldEffects applied.worldReplayExact
                (worldEffectsLeaveAccountUntouched_each applied.worldEffects
                  before.secondary.machine.inventory untouched)
            .ok
              { after :=
                  { accounts := applied.afterWorld
                    primary := applied.afterRuntime
                    secondary := before.secondary
                    primaryBacked := applied.afterCustodyBacked
                    secondaryBacked := secondaryBacked }
                receipt :=
                  { station := .primary
                    operation := applied.receipt
                    direct := applied.directReceipt }
                worldEffects := applied.worldEffects
                worldReplayExact := applied.worldReplayExact }
          else
            .error [.unrelatedInventoryTouched .secondary
              before.secondary.machine.inventory]
  | .secondary =>
      match applyRuntimeOperation evaluateGuard before.accounts before.secondary
          before.secondaryBacked proposal with
      | .error issues => .error [.operationRejected .secondary issues]
      | .ok applied =>
          if untouched : worldEffectsLeaveAccountUntouched applied.worldEffects
              before.primary.machine.inventory = true then
            let primaryBacked :=
              before.primaryBacked.replayWorldEffects_untouched
                applied.worldEffects applied.worldReplayExact
                (worldEffectsLeaveAccountUntouched_each applied.worldEffects
                  before.primary.machine.inventory untouched)
            .ok
              { after :=
                  { accounts := applied.afterWorld
                    primary := before.primary
                    secondary := applied.afterRuntime
                    primaryBacked := primaryBacked
                    secondaryBacked := applied.afterCustodyBacked }
                receipt :=
                  { station := .secondary
                    operation := applied.receipt
                    direct := applied.directReceipt }
                worldEffects := applied.worldEffects
                worldReplayExact := applied.worldReplayExact }
          else
            .error [.unrelatedInventoryTouched .primary
              before.primary.machine.inventory]

def intentSuccessor (before : State) (intent : Intent) : Option State :=
  match applyIntent before intent with
  | .error _ => none
  | .ok applied => some applied.after

structure ScheduledReceipt where
  after : State
  operation : Receipt

def replayReceipt (receipt : ScheduledReceipt) (_ : State) : State := receipt.after

def executor : IntentExecutor State Intent Issue ScheduledReceipt where
  replay := replayReceipt
  apply := fun before intent =>
    match applyIntent before intent with
    | .error issues => .error issues
    | .ok applied =>
        .ok
          { after := applied.after
            receipt := { after := applied.after, operation := applied.receipt }
            replayExact := rfl }

theorem intentSuccessor_rejected
    (before : State)
    (intent : Intent)
    (issues : List Issue)
    (rejected : applyIntent before intent = .error issues) :
    intentSuccessor before intent = none := by
  simp [intentSuccessor, rejected]

def primaryEntryRun := applyIntent initialState enterPrimary

def afterPrimaryEntry : State :=
  match primaryEntryRun with
  | .ok applied => applied.after
  | .error _ => initialState

def secondaryEntryRun := applyIntent afterPrimaryEntry enterSecondary

def secondaryEntryIssues : Option (List Issue) :=
  match secondaryEntryRun with
  | .error issues => some issues
  | .ok _ => none

example :
    (afterPrimaryEntry.accounts.balance machineAccount workerBodyId).atoms = 1 := by
  native_decide

example :
    (afterPrimaryEntry.accounts.balance secondaryMachineAccount workerBodyId).atoms = 0 := by
  native_decide

example :
    (afterPrimaryEntry.accounts.balance workerAccount workerBodyId).atoms = 0 := by
  native_decide

example :
    secondaryEntryIssues =
      some [.operationRejected .secondary
        [.transferRejected [.shortfall workerBodyId 1 0 1]]] := by
  native_decide

example : intentSuccessor afterPrimaryEntry enterSecondary = none := by
  native_decide

def secondaryModeAfterPrimaryEntry : Option Mode :=
  match primaryEntryRun with
  | .ok applied => some applied.after.secondary.mode
  | .error _ => none

example : secondaryModeAfterPrimaryEntry = some .running := by native_decide

/-- Unique-resource exclusion is an account theorem, specialized by the game. -/
example
    (leftHeld :
      (afterPrimaryEntry.accounts.balance machineAccount workerBodyId).atoms = 1)
    (rightHeld :
      (afterPrimaryEntry.accounts.balance secondaryMachineAccount workerBodyId).atoms = 1) :
    False :=
  afterPrimaryEntry.accounts.unique_not_held_by_distinct_accounts
    { id := workerBodyId, name := "worker body" }
    (by rfl) machineAccount secondaryMachineAccount (by decide)
    leftHeld rightHeld

end Maquina.Games.Foundry.Workcell
