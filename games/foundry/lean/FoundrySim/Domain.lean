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
  | smelt
  | refuel
  deriving DecidableEq, Repr

inductive Label where
  | provider
  | machine
  | consumer
  deriving DecidableEq, Repr

inductive InputQueueKind where
  | production
  | service
  deriving DecidableEq, Repr

inductive ProcessingQueueKind where
  | production
  | service
  deriving DecidableEq, Repr

inductive OutputQueueKind where
  | production
  deriving DecidableEq, Repr

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
  inputs :=
    [{ label := .provider
       basket := refuelBasket
       nonempty := by simp [refuelBasket, Basket.singleton] }]
  outputs :=
    [{ label := .machine
       basket := refuelBasket
       nonempty := by simp [refuelBasket, Basket.singleton] }]
  inputLabelsUnique := by simp
  outputLabelsUnique := by simp
  requiredWork := 1

/-- The smelting recipe will gain its resource ports in the process slice. -/
def smeltProcess : Process Label := Process.empty 1

def processDefinition : ProcessKind → Process Label
  | .smelt => smeltProcess
  | .refuel => refuelProcess

def acceptsInput : InputQueueKind → ProcessKind → Prop
  | .production, processKind => processKind = .smelt
  | .service, processKind => processKind = .refuel

def acceptsProcessing : ProcessingQueueKind → ProcessKind → Prop
  | .production, processKind => processKind = .smelt
  | .service, processKind => processKind = .refuel

def acceptsOutput : OutputQueueKind → ProcessKind → Prop
  | .production, processKind => processKind = .smelt

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
  | smelt : Operation .running .running
  | admitRefuel : Operation .running .running
  | dispatchRefuel : Operation .running .running
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

def smeltOperation : Operation .running .running := .smelt

end Maquina.Games.Foundry
