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
  | worker
  | operator
  | collector
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
  | auxiliaryInput : QueuePort .input
  | serviceProcessing : QueuePort .processing
  | productionOutput : QueuePort .output
  deriving Repr

/-- Foundry currently needs no additional domain-specific operation guards. -/
inductive Guard : Type

/-! ## Foundry resources and process definitions -/

def fuelId : ResourceId := ⟨100⟩
def workerBodyId : ResourceId := ⟨101⟩
def laborCapacityId : ResourceId := ⟨102⟩
def serviceCreditId : ResourceId := ⟨103⟩

def fuelHeader : ResourceHeader :=
  { id := fuelId, name := "fuel" }

def oneLiter : PositiveRat where
  value := 1
  positive := by decide

def fuelSpec : ResourceSpec :=
  ResourceSpec.measured fuelHeader Dimension.volume
    (.named "foundry" "fuel") oneLiter

def workerBodySpec : ResourceSpec :=
  ResourceSpec.unique { id := workerBodyId, name := "worker body" }

def laborCapacitySpec : ResourceSpec :=
  ResourceSpec.edition
    { id := laborCapacityId, name := "labor capacity" }
    2
    (by decide)

def serviceCreditSpec : ResourceSpec :=
  ResourceSpec.discrete { id := serviceCreditId, name := "service credit" }

def resourceCatalog : ResourceCatalog :=
  ResourceCatalog.ofList
    [fuelSpec, workerBodySpec, laborCapacitySpec, serviceCreditSpec]

def refuelQuantity : Quantity := ⟨10⟩

def refuelBasket : Basket :=
  Basket.singleton fuelId refuelQuantity (by decide)

def workerReservation : Basket where
  entries :=
    [ { resourceId := workerBodyId
        quantity := .one
        positive := by decide },
      { resourceId := laborCapacityId
        quantity := .one
        positive := by decide } ]
  resourcesUnique := by native_decide

def serviceCredit : Basket :=
  Basket.singleton serviceCreditId .one (by decide)

def refuelProcess : Process Label where
  consumed :=
    [{ label := .provider
       basket := refuelBasket
       nonempty := by simp [refuelBasket, Basket.singleton] }]
  reserved :=
    [{ label := .worker
       basket := workerReservation
       nonempty := by simp [workerReservation] }]
  outputs :=
    [{ label := .machine
       basket := refuelBasket
       nonempty := by simp [refuelBasket, Basket.singleton] },
     { label := .operator
       basket := serviceCredit
       nonempty := by simp [serviceCredit, Basket.singleton] },
     { label := .collector
       basket := serviceCredit
       nonempty := by simp [serviceCredit, Basket.singleton] }]
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
  | .production, processKind => processKind = .refuel

def schema : MachineSchema where
  ProcessKind := ProcessKind
  Label := Label
  InputQueueKind := InputQueueKind
  ProcessingQueueKind := ProcessingQueueKind
  OutputQueueKind := OutputQueueKind
  processKindDecidableEq := inferInstance
  labelDecidableEq := inferInstance
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
  | collectRefuel : Operation .running .running
  | addServiceInput : Operation .running .running
  | removeServiceInput : Operation .running .running
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
        requirements := []
        processKind := none
        effects := [] }
  | .reserveFuel =>
      { trigger := .commanded
        guards := []
        requirements := []
        processKind := some .refuel
        effects :=
          [.reserveConsumedInputs,
           .enqueue .serviceInput] }
  | .dispatchRefuel =>
      { trigger := .reactive
        guards := []
        requirements := []
        processKind := some .refuel
        effects :=
          [.reserveReservedInputs .serviceInput,
           .moveToProcessing .serviceInput .serviceProcessing] }
  | .advanceRefuel =>
      { trigger := .scheduled
        guards := []
        requirements := []
        processKind := some .refuel
        effects :=
          [.advance .serviceProcessing 1 (by decide)] }
  | .completeRefuel =>
      { trigger := .reactive
        guards := []
        requirements := []
        processKind := some .refuel
        effects :=
          [.completeToOutput .serviceProcessing .productionOutput] }
  | .collectRefuel =>
      { trigger := .commanded
        guards := []
        requirements := []
        processKind := some .refuel
        effects :=
          [.bindOutput .collector,
           .collect .productionOutput] }
  | .addServiceInput =>
      { trigger := .commanded
        guards := []
        requirements := []
        processKind := none
        effects := [.addInputQueue .auxiliaryInput .service (some 1)] }
  | .removeServiceInput =>
      { trigger := .commanded
        guards := []
        requirements := []
        processKind := none
        effects := [.removeInputQueue .auxiliaryInput] }
  | .stop =>
      { trigger := .commanded
        guards := []
        requirements := []
        processKind := none
        effects := [] }
  | .fail =>
      { trigger := .reactive
        guards := []
        requirements := []
        processKind := none
        effects := [] }
  | .repair =>
      { trigger := .commanded
        guards := []
        requirements := []
        processKind := none
        effects := [] }

def operationLanguage : OperationLanguage schema where
  Mode := Mode
  Operation := Operation
  QueuePort := QueuePort
  Guard := Guard
  modeDecidableEq := inferInstance
  definition := operationDefinition

end Maquina.Games.Foundry
