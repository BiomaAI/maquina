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
def workerAccount : AccountId := ⟨3000⟩
def workerCustodyAccount : AccountId := ⟨3001⟩
def outputCustodyAccount : AccountId := ⟨4000⟩
def operatorAccount : AccountId := ⟨5000⟩
def collectorAccount : AccountId := ⟨6000⟩

def processBindings : ProcessBindings Label where
  source
    | .provider => providerAccount
    | .machine => machineAccount
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
    | .machine => some machineAccount
    | .worker => some workerAccount
    | .operator => some operatorAccount
    | .collector => none

/-- Refueling uses service queues and has no bound output queue. -/
def queueBindings : QueueBindings QueuePort where
  resolve
    | .serviceInput => some ⟨0⟩
    | .auxiliaryInput => some ⟨1⟩
    | .serviceProcessing => some ⟨0⟩
    | .productionOutput => some ⟨0⟩

def noRecipientBindings : RecipientBindings Label where
  resolve := fun _ => none

def collectorRecipientBindings : RecipientBindings Label where
  resolve
    | .collector => some collectorAccount
    | _ => none

def reserveFuel : OperationProposal schema operationLanguage where
  before := .running
  after := .running
  operation := .reserveFuel
  processBindings := some processBindings
  queueBindings := queueBindings
  recipientBindings := noRecipientBindings

def dispatchRefuel : OperationProposal schema operationLanguage where
  before := .running
  after := .running
  operation := .dispatchRefuel
  processBindings := none
  queueBindings := queueBindings
  recipientBindings := noRecipientBindings

def advanceRefuel : OperationProposal schema operationLanguage where
  before := .running
  after := .running
  operation := .advanceRefuel
  processBindings := none
  queueBindings := queueBindings
  recipientBindings := noRecipientBindings

def completeRefuel : OperationProposal schema operationLanguage where
  before := .running
  after := .running
  operation := .completeRefuel
  processBindings := none
  queueBindings := queueBindings
  recipientBindings := noRecipientBindings

def collectRefuel : OperationProposal schema operationLanguage where
  before := .running
  after := .running
  operation := .collectRefuel
  processBindings := none
  queueBindings := queueBindings
  recipientBindings := collectorRecipientBindings

def addServiceInput : OperationProposal schema operationLanguage where
  before := .running
  after := .running
  operation := .addServiceInput
  processBindings := none
  queueBindings := queueBindings
  recipientBindings := noRecipientBindings

def removeServiceInput : OperationProposal schema operationLanguage where
  before := .running
  after := .running
  operation := .removeServiceInput
  processBindings := none
  queueBindings := queueBindings
  recipientBindings := noRecipientBindings

/-- A definition-only program that a generic simulator can consume in order. -/
def program : List (OperationProposal schema operationLanguage) :=
  [reserveFuel, dispatchRefuel, advanceRefuel, completeRefuel, collectRefuel]

example :
    (operationDefinition reserveFuel.operation).processKind = some .refuel := rfl

example :
    (operationDefinition completeRefuel.operation).effects.length = 1 := rfl

example :
    refuelProcess.reserved.map ProcessPort.label = [.worker] := rfl

example :
    processBindings.output .collector = none := rfl

example :
    collectorRecipientBindings.resolve .collector = some collectorAccount := rfl

example :
    (operationDefinition collectRefuel.operation).effects.length = 2 := rfl

end Maquina.Games.Foundry.Refuel
