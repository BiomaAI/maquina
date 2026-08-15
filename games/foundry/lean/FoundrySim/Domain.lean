import Maquina

/-!
# Foundry Domain

Game-owned vocabulary for the Foundry formal simulation. The generic Maquina
kernel does not know any of these domain-specific names.
-/

namespace Maquina.Games.Foundry

inductive Mode where
  | off
  | running
  | broken
  deriving DecidableEq, Repr

inductive ProcessKind where
  | refuel
  deriving DecidableEq, Repr

inductive Label where
  | provider
  | machine
  deriving DecidableEq, Repr

inductive InputQueueKind where
  | service
  deriving DecidableEq, Repr

inductive ProcessingQueueKind where
  | service
  deriving DecidableEq, Repr

inductive OutputQueueKind where
  | production
  deriving DecidableEq, Repr

/-- Foundry names ports; a machine instance later binds them to queue IDs. -/
inductive QueuePort : QueueStage → Type where
  | serviceInput : QueuePort .input
  | serviceProcessing : QueuePort .processing
  | productionOutput : QueuePort .output
  deriving Repr

/-- Foundry currently needs no additional domain-specific operation guards. -/
inductive Guard : Type

/-! ## Foundry resources and process definitions -/

def fuelId : ResourceId := ⟨100⟩

def fuelHeader : ResourceHeader :=
  { id := fuelId, name := "fuel" }

def oneLiter : PositiveRat where
  value := 1
  positive := by decide

def fuelSpec : ResourceSpec :=
  ResourceSpec.measured fuelHeader Dimension.volume
    (.named "foundry" "fuel") oneLiter

def fuelCatalog : ResourceCatalog := ResourceCatalog.singleton fuelSpec

def refuelQuantity : Quantity := ⟨10⟩

def refuelBasket : Basket :=
  Basket.singleton fuelId refuelQuantity (by decide)

def refuelProcess : Process Label where
  consumed :=
    [{ label := .provider
       basket := refuelBasket
       nonempty := by simp [refuelBasket, Basket.singleton] }]
  reserved := []
  outputs :=
    [{ label := .machine
       basket := refuelBasket
       nonempty := by simp [refuelBasket, Basket.singleton] }]
  consumedLabelsUnique := by simp
  reservedLabelsUnique := by simp
  outputLabelsUnique := by simp
  requiredWork := 1

def processDefinition : ProcessKind → Process Label
  | .refuel => refuelProcess

def acceptsInput : InputQueueKind → ProcessKind → Prop
  | .service, processKind => processKind = .refuel

def acceptsProcessing : ProcessingQueueKind → ProcessKind → Prop
  | .service, processKind => processKind = .refuel

def acceptsOutput : OutputQueueKind → ProcessKind → Prop
  | .production, _ => False

def schema : MachineSchema where
  ProcessKind := ProcessKind
  Label := Label
  InputQueueKind := InputQueueKind
  ProcessingQueueKind := ProcessingQueueKind
  OutputQueueKind := OutputQueueKind
  acceptsInput := acceptsInput
  acceptsProcessing := acceptsProcessing
  acceptsOutput := acceptsOutput
  process := processDefinition
  acceptsInputDecidable := fun queueKind _ => by
    cases queueKind <;> simp only [acceptsInput] <;> exact inferInstance
  acceptsProcessingDecidable := fun queueKind _ => by
    cases queueKind <;> simp only [acceptsProcessing] <;> exact inferInstance
  acceptsOutputDecidable := fun queueKind _ => by
    cases queueKind <;> simp only [acceptsOutput] <;> exact inferInstance

/-
The indices encode Foundry's static operation dependencies. The generic
operation routes and effects are attached separately.
-/
inductive Operation : Mode → Mode → Type where
  | start : Operation .off .running
  | reserveFuel : Operation .running .running
  | dispatchRefuel : Operation .running .running
  | advanceRefuel : Operation .running .running
  | completeRefuel : Operation .running .running
  | stop : Operation .running .off
  | fail : Operation .running .broken
  | repair : Operation .broken .off
  deriving Repr

theorem noOperationFromOffToOff : ¬ Nonempty (Operation .off .off) := by
  intro possible
  obtain ⟨operation⟩ := possible
  cases operation

theorem noOperationFromBrokenToBroken :
    ¬ Nonempty (Operation .broken .broken) := by
  intro possible
  obtain ⟨operation⟩ := possible
  cases operation

def operationDefinition
    {before after : Mode} :
    Operation before after →
      OperationDefinition schema QueuePort Guard
  | .start =>
      { trigger := .commanded
        guards := []
        processKind := none
        effects := [] }
  | .reserveFuel =>
      { trigger := .commanded
        guards := []
        processKind := some .refuel
        effects :=
          [.reserveProcessInputs,
           .enqueue .serviceInput] }
  | .dispatchRefuel =>
      { trigger := .reactive
        guards := []
        processKind := some .refuel
        effects :=
          [.moveToProcessing .serviceInput .serviceProcessing] }
  | .advanceRefuel =>
      { trigger := .scheduled
        guards := []
        processKind := some .refuel
        effects :=
          [.advance .serviceProcessing 1 (by decide)] }
  | .completeRefuel =>
      { trigger := .reactive
        guards := []
        processKind := some .refuel
        effects :=
          [.completeToInventories .serviceProcessing] }
  | .stop =>
      { trigger := .commanded
        guards := []
        processKind := none
        effects := [] }
  | .fail =>
      { trigger := .reactive
        guards := []
        processKind := none
        effects := [] }
  | .repair =>
      { trigger := .commanded
        guards := []
        processKind := none
        effects := [] }

def operationLanguage : OperationLanguage schema where
  Mode := Mode
  Operation := Operation
  QueuePort := QueuePort
  Guard := Guard
  definition := operationDefinition

end Maquina.Games.Foundry
