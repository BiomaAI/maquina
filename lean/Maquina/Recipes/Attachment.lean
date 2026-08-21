import Maquina.Recipes.Support

/-!
# Recipe: Attachment

Two open endpoint Resources are consumed to produce one Link Resource and its
lease. Detachment is the inverse Process. There is no graph mutation helper.
-/

namespace Maquina.Recipes.Attachment

open Support

inductive Label where | left | right | link | lease
  deriving DecidableEq, Repr
inductive ProcessKind where | attach | detach
  deriving DecidableEq, Repr
inductive Mode where | detached | attached
  deriving DecidableEq, Repr
inductive Operation : Mode → Mode → Type where
  | attach : Operation .detached .attached
  | detach : Operation .attached .detached
  deriving Repr
inductive Guard deriving DecidableEq, Repr
inductive QueuePort : QueueStage → Type deriving Repr

def endpointBasket (key : Nat) : Basket :=
  Basket.singleton (endpointFamily.encode key) .one (by decide)
def leftEndpointId : ResourceId := endpointFamily.encode 0
def rightEndpointId : ResourceId := endpointFamily.encode 1
def linkBasket : Basket :=
  Basket.singleton (linkFamily.encode 0) .one (by decide)
def leaseBasket : Basket := relationLeaseBasket relationModel 0

def attachProcess : Process Label where
  consumed :=
    [{ label := .left, basket := endpointBasket 0,
       nonempty := by simp [endpointBasket, Basket.singleton] },
     { label := .right, basket := endpointBasket 1,
       nonempty := by simp [endpointBasket, Basket.singleton] }]
  reserved := []
  activeCustody := []
  outputs :=
    [{ label := .link, basket := linkBasket,
       nonempty := by simp [linkBasket, Basket.singleton] },
     { label := .lease, basket := leaseBasket,
       nonempty := by simp [leaseBasket, relationLeaseBasket, Basket.singleton] }]
  consumedLabelsUnique := by simp
  reservedLabelsUnique := by simp
  activeCustodyLabelsUnique := by simp
  outputLabelsUnique := by simp
  requiredWork := 0

def detachProcess : Process Label where
  consumed :=
    [{ label := .link, basket := linkBasket,
       nonempty := by simp [linkBasket, Basket.singleton] },
     { label := .lease, basket := leaseBasket,
       nonempty := by simp [leaseBasket, relationLeaseBasket, Basket.singleton] }]
  reserved := []
  activeCustody := []
  outputs :=
    [{ label := .left, basket := endpointBasket 0,
       nonempty := by simp [endpointBasket, Basket.singleton] },
     { label := .right, basket := endpointBasket 1,
       nonempty := by simp [endpointBasket, Basket.singleton] }]
  consumedLabelsUnique := by simp
  reservedLabelsUnique := by simp
  activeCustodyLabelsUnique := by simp
  outputLabelsUnique := by simp
  requiredWork := 0

def schema : MachineSchema where
  ProcessKind := ProcessKind
  Label := Label
  InputQueueKind := Unit
  ProcessingQueueKind := Unit
  OutputQueueKind := Unit
  processKindDecidableEq := inferInstance
  labelDecidableEq := inferInstance
  acceptsInput := fun _ _ => False
  acceptsProcessing := fun _ _ => False
  acceptsOutput := fun _ _ => False
  process | .attach => attachProcess | .detach => detachProcess
  acceptsInputDecidable := fun _ _ => inferInstance
  acceptsProcessingDecidable := fun _ _ => inferInstance
  acceptsOutputDecidable := fun _ _ => inferInstance

def requirement (label : Label) (basket : Basket)
    (nonempty : basket.entries ≠ []) : PossessionPort Label where
  label := label
  basket := basket
  nonempty := nonempty

def definition {before after} : Operation before after →
    OperationDefinition schema QueuePort Guard
  | .attach =>
      { trigger := .commanded, guards := [],
        requirements :=
          [requirement .left (endpointBasket 0)
            (by simp [endpointBasket, Basket.singleton]),
           requirement .right (endpointBasket 1)
            (by simp [endpointBasket, Basket.singleton])],
        processKind := some .attach, effects := [.executeProcess] }
  | .detach =>
      { trigger := .commanded, guards := [],
        requirements :=
          [requirement .link linkBasket
            (by simp [linkBasket, Basket.singleton]),
           requirement .lease leaseBasket
            (by simp [leaseBasket, relationLeaseBasket, Basket.singleton])],
        processKind := some .detach, effects := [.executeProcess] }

def language : OperationLanguage schema where
  Mode := Mode
  Operation := Operation
  QueuePort := QueuePort
  Guard := Guard
  modeDecidableEq := inferInstance
  definition := definition

def machine : Machine schema := Machine.empty chassisAccount 0 chassisBody

def genesis : GenesisPlan where
  grants :=
    [{ account := chassisAccount,
       entry := { resourceId := chassisBody, quantity := .one, positive := by decide } },
     { account := wheelAccount,
       entry := { resourceId := wheelBody, quantity := .one, positive := by decide } },
     { account := chassisAccount,
       entry := { resourceId := leftEndpointId, quantity := .one,
                  positive := by decide } },
     { account := wheelAccount,
       entry := { resourceId := rightEndpointId, quantity := .one,
                  positive := by decide } }]
  keysUnique := by native_decide

def initialWorld : WorldState recipeCatalog :=
  match applyGenesis recipeCatalog genesis with
  | .ok applied => applied.after
  | .error _ => WorldState.empty recipeCatalog

def machineBodyBacked : Machine.BodyBacked initialWorld machine where
  header := { id := chassisBody, name := "chassis Body" }
  headerId := rfl
  catalogExact := rfl
  held := by native_decide

def runtime : MachineRuntime schema language where
  mode := .detached
  machine := machine
  custody := MachineCustody.empty machine.inventory
  activeCustodyHeld := by
    simp [Machine.ActiveDependenciesSatisfy, machine, Machine.empty]
  nextProcessId := 0

def noGuards : GuardEvaluator recipeCatalog schema language where
  condition := fun guard _ => nomatch guard
  issues := fun guard _ => nomatch guard
  evidence := fun guard _ => nomatch guard
  issuesEmptyIff := by intro guard; exact nomatch guard

def bindings (kind : ProcessKind) : ProcessBindings Label where
  source := fun label => match kind, label with
    | .attach, .left => chassisAccount | .attach, .right => wheelAccount
    | .detach, .link | .detach, .lease => ledger
    | _, _ => custodyAccount
  custody := fun _ => custodyAccount
  output := fun label => match kind, label with
    | .attach, .link | .attach, .lease => some ledger
    | .detach, .left => some chassisAccount
    | .detach, .right => some wheelAccount
    | _, _ => none

def proposal {before after} (operation : Operation before after)
    (kind : ProcessKind) : OperationProposal schema language where
  before := before
  after := after
  operation := operation
  possessionBindings := { resolve := (bindings kind).source }
  custodyBindings := { resolve := fun _ => none }
  processBindings := some (bindings kind)
  queueBindings := { resolve := fun port => nomatch port }
  recipientBindings := { resolve := fun _ => none }

def attachRun := applyRuntimeOperation noGuards initialWorld runtime
  (MachineCustody.backed_empty initialWorld machine.inventory)
  (proposal .attach .attach)

def attachedWorld : WorldState recipeCatalog :=
  match attachRun with | .ok applied => applied.afterWorld | .error _ => initialWorld

example : (attachedWorld.balance ledger (linkFamily.encode 0)).atoms = 1 := by
  native_decide

example : (attachedWorld.balance chassisAccount (endpointFamily.encode 0)).atoms = 0 := by
  native_decide

end Maquina.Recipes.Attachment
