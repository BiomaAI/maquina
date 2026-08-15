import FoundrySim.Domain

/-!
# Foundry Refueling Definitions

Only declarative data lives here. A future generic Maquina simulator will
interpret these bindings and operation proposals.
-/

namespace Maquina.Games.Foundry.Refuel

def providerAccount : AccountId := ⟨1000⟩
def escrowAccount : AccountId := ⟨1001⟩
def machineAccount : AccountId := ⟨2000⟩

def processBindings : ProcessBindings Label where
  input
    | .provider => providerAccount
    | .machine => machineAccount
  custody
    | .provider => escrowAccount
    | .machine => machineAccount
  output
    | .provider => providerAccount
    | .machine => machineAccount

/-- Refueling uses service queues and has no bound output queue. -/
def queueBindings : QueueBindings QueuePort where
  resolve
    | .serviceInput => some ⟨0⟩
    | .serviceProcessing => some ⟨0⟩
    | .productionOutput => none

def reserveFuel : OperationProposal schema operationLanguage where
  before := .running
  after := .running
  operation := .reserveFuel
  processBindings := some processBindings
  queueBindings := queueBindings

def dispatchRefuel : OperationProposal schema operationLanguage where
  before := .running
  after := .running
  operation := .dispatchRefuel
  processBindings := none
  queueBindings := queueBindings

def advanceRefuel : OperationProposal schema operationLanguage where
  before := .running
  after := .running
  operation := .advanceRefuel
  processBindings := none
  queueBindings := queueBindings

def completeRefuel : OperationProposal schema operationLanguage where
  before := .running
  after := .running
  operation := .completeRefuel
  processBindings := none
  queueBindings := queueBindings

/-- A definition-only program that a generic simulator can consume in order. -/
def program : List (OperationProposal schema operationLanguage) :=
  [reserveFuel, dispatchRefuel, advanceRefuel, completeRefuel]

example :
    (operationDefinition reserveFuel.operation).processKind = some .refuel := rfl

example :
    (operationDefinition completeRefuel.operation).effects.length = 1 := rfl

end Maquina.Games.Foundry.Refuel
