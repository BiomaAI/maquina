import FoundrySim.Domain

/-!
# Foundry Refueling Definitions

Only declarative data lives here. The generic Maquina simulator interprets
these bindings and operation proposals.
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

def possessionBindings : PossessionBindings Label where
  resolve := processBindings.source

def noCustodyBindings : CustodyBindings Label where
  resolve := fun _ => none

def workerCustodyBindings : CustodyBindings Label where
  resolve
    | .worker => some 0
    | _ => none

def enterMachine : OperationProposal schema operationLanguage where
  before := .running
  after := .running
  operation := .enterMachine
  possessionBindings := possessionBindings
  custodyBindings := noCustodyBindings
  processBindings := none
  queueBindings := queueBindings
  recipientBindings := noRecipientBindings

def reserveFuel : OperationProposal schema operationLanguage where
  before := .running
  after := .running
  operation := .reserveFuel
  possessionBindings := possessionBindings
  custodyBindings := noCustodyBindings
  processBindings := some processBindings
  queueBindings := queueBindings
  recipientBindings := noRecipientBindings

def dispatchRefuel : OperationProposal schema operationLanguage where
  before := .running
  after := .running
  operation := .dispatchRefuel
  possessionBindings := possessionBindings
  custodyBindings := noCustodyBindings
  processBindings := none
  queueBindings := queueBindings
  recipientBindings := noRecipientBindings

def advanceRefuel : OperationProposal schema operationLanguage where
  before := .running
  after := .running
  operation := .advanceRefuel
  possessionBindings := possessionBindings
  custodyBindings := noCustodyBindings
  processBindings := none
  queueBindings := queueBindings
  recipientBindings := noRecipientBindings

def completeRefuel : OperationProposal schema operationLanguage where
  before := .running
  after := .running
  operation := .completeRefuel
  possessionBindings := possessionBindings
  custodyBindings := noCustodyBindings
  processBindings := none
  queueBindings := queueBindings
  recipientBindings := noRecipientBindings

def collectRefuel : OperationProposal schema operationLanguage where
  before := .running
  after := .running
  operation := .collectRefuel
  possessionBindings := possessionBindings
  custodyBindings := noCustodyBindings
  processBindings := none
  queueBindings := queueBindings
  recipientBindings := collectorRecipientBindings

def cancelQueuedRefuel : OperationProposal schema operationLanguage where
  before := .running
  after := .running
  operation := .cancelQueuedRefuel
  possessionBindings := possessionBindings
  custodyBindings := noCustodyBindings
  processBindings := none
  queueBindings := queueBindings
  recipientBindings := noRecipientBindings

def cancelActiveRefuel : OperationProposal schema operationLanguage where
  before := .running
  after := .running
  operation := .cancelActiveRefuel
  possessionBindings := possessionBindings
  custodyBindings := noCustodyBindings
  processBindings := none
  queueBindings := queueBindings
  recipientBindings := noRecipientBindings

def leaveMachine : OperationProposal schema operationLanguage where
  before := .running
  after := .running
  operation := .leaveMachine
  possessionBindings := possessionBindings
  custodyBindings := workerCustodyBindings
  processBindings := none
  queueBindings := queueBindings
  recipientBindings := noRecipientBindings

def addServiceInput : OperationProposal schema operationLanguage where
  before := .running
  after := .running
  operation := .addServiceInput
  possessionBindings := possessionBindings
  custodyBindings := noCustodyBindings
  processBindings := none
  queueBindings := queueBindings
  recipientBindings := noRecipientBindings

def removeServiceInput : OperationProposal schema operationLanguage where
  before := .running
  after := .running
  operation := .removeServiceInput
  possessionBindings := possessionBindings
  custodyBindings := noCustodyBindings
  processBindings := none
  queueBindings := queueBindings
  recipientBindings := noRecipientBindings

/-- A definition-only program that a generic simulator can consume in order. -/
def program : List (OperationProposal schema operationLanguage) :=
  [enterMachine, reserveFuel, dispatchRefuel, advanceRefuel, completeRefuel,
    leaveMachine, collectRefuel]

example :
    (operationDefinition reserveFuel.operation).processKind = some .refuel := rfl

example :
    (operationDefinition completeRefuel.operation).effects.length = 1 := rfl

example : refuelProcess.reserved.map ProcessPort.label = [.worker] := rfl

example :
    (operationDefinition reserveFuel.operation).requirements = [bodyPresence] := rfl

example :
    (operationDefinition collectRefuel.operation).requirements = [] := rfl

example :
    processBindings.output .collector = none := rfl

example :
    collectorRecipientBindings.resolve .collector = some collectorAccount := rfl

example :
    (operationDefinition collectRefuel.operation).effects.length = 2 := rfl

end Maquina.Games.Foundry.Refuel
