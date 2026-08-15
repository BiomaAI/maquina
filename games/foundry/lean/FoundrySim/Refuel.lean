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
  source
    | .provider => providerAccount
    | .machine => machineAccount
  custody
    | .provider => escrowAccount
    | .machine => machineAccount
  output
    | .provider => some providerAccount
    | .machine => some machineAccount

/-- Refueling uses service queues and has no bound output queue. -/
def queueBindings : QueueBindings QueuePort where
  resolve
    | .serviceInput => some ⟨0⟩
    | .serviceProcessing => some ⟨0⟩
    | .productionOutput => none

def recipientBindings : RecipientBindings Label where
  resolve := fun _ => none

def reserveFuel : OperationProposal schema operationLanguage where
  before := .running
  after := .running
  operation := .reserveFuel
  processBindings := some processBindings
  queueBindings := queueBindings
  recipientBindings := recipientBindings

def dispatchRefuel : OperationProposal schema operationLanguage where
  before := .running
  after := .running
  operation := .dispatchRefuel
  processBindings := none
  queueBindings := queueBindings
  recipientBindings := recipientBindings

def advanceRefuel : OperationProposal schema operationLanguage where
  before := .running
  after := .running
  operation := .advanceRefuel
  processBindings := none
  queueBindings := queueBindings
  recipientBindings := recipientBindings

def completeRefuel : OperationProposal schema operationLanguage where
  before := .running
  after := .running
  operation := .completeRefuel
  processBindings := none
  queueBindings := queueBindings
  recipientBindings := recipientBindings

/-- A definition-only program that a generic simulator can consume in order. -/
def program : List (OperationProposal schema operationLanguage) :=
  [reserveFuel, dispatchRefuel, advanceRefuel, completeRefuel]

example :
    (operationDefinition reserveFuel.operation).processKind = some .refuel := rfl

example :
    (operationDefinition completeRefuel.operation).effects.length = 1 := rfl

end Maquina.Games.Foundry.Refuel
