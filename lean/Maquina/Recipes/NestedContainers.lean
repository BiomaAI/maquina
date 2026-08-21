import Maquina.Recipes.Support

/-!
# Recipe: Nested Containers

Containing a pouch consumes the bag's open interior endpoint and the pouch's
open exterior endpoint. The resulting containment Link is the only nesting
fact; contents remain in their own Machine inventory and manifests derive them.
-/

namespace Maquina.Recipes.NestedContainers
open Support

inductive Label where | bag | pouch | link | lease deriving DecidableEq, Repr
inductive ProcessKind where | insert | extract deriving DecidableEq, Repr
inductive Mode where | separate | nested deriving DecidableEq, Repr
inductive Operation : Mode → Mode → Type where
  | insert : Operation .separate .nested
  | extract : Operation .nested .separate
  deriving Repr
inductive Guard deriving DecidableEq, Repr
inductive Port : QueueStage → Type deriving Repr

def endpointBasket (key : Nat) :=
  Basket.singleton (endpointFamily.encode key) .one (by decide)
def linkBasket := Basket.singleton (linkFamily.encode 1) .one (by decide)
def leaseBasket := relationLeaseBasket relationModel 1

def bagRequirement : PossessionPort Label :=
  { label := .bag, basket := endpointBasket 2,
    nonempty := by simp [endpointBasket, Basket.singleton] }
def pouchRequirement : PossessionPort Label :=
  { label := .pouch, basket := endpointBasket 3,
    nonempty := by simp [endpointBasket, Basket.singleton] }
def linkRequirement : PossessionPort Label :=
  { label := .link, basket := linkBasket,
    nonempty := by simp [linkBasket, Basket.singleton] }
def leaseRequirement : PossessionPort Label :=
  { label := .lease, basket := leaseBasket,
    nonempty := by simp [leaseBasket, relationLeaseBasket, Basket.singleton] }

def process : ProcessKind → Process Label
  | .insert =>
      { consumed :=
          [{ label := .bag, basket := endpointBasket 2,
             nonempty := by simp [endpointBasket, Basket.singleton] },
           { label := .pouch, basket := endpointBasket 3,
             nonempty := by simp [endpointBasket, Basket.singleton] }]
        reserved := [], activeCustody := []
        outputs :=
          [{ label := .link, basket := linkBasket,
             nonempty := by simp [linkBasket, Basket.singleton] },
           { label := .lease, basket := leaseBasket,
             nonempty := by simp [leaseBasket, relationLeaseBasket, Basket.singleton] }]
        consumedLabelsUnique := by simp
        reservedLabelsUnique := by simp
        activeCustodyLabelsUnique := by simp
        outputLabelsUnique := by simp
        requiredWork := 0 }
  | .extract =>
      { consumed :=
          [{ label := .link, basket := linkBasket,
             nonempty := by simp [linkBasket, Basket.singleton] },
           { label := .lease, basket := leaseBasket,
             nonempty := by simp [leaseBasket, relationLeaseBasket, Basket.singleton] }]
        reserved := [], activeCustody := []
        outputs :=
          [{ label := .bag, basket := endpointBasket 2,
             nonempty := by simp [endpointBasket, Basket.singleton] },
           { label := .pouch, basket := endpointBasket 3,
             nonempty := by simp [endpointBasket, Basket.singleton] }]
        consumedLabelsUnique := by simp
        reservedLabelsUnique := by simp
        activeCustodyLabelsUnique := by simp
        outputLabelsUnique := by simp
        requiredWork := 0 }

def schema : MachineSchema where
  ProcessKind := ProcessKind; Label := Label
  InputQueueKind := Unit; ProcessingQueueKind := Unit; OutputQueueKind := Unit
  processKindDecidableEq := inferInstance; labelDecidableEq := inferInstance
  acceptsInput := fun _ _ => False
  acceptsProcessing := fun _ _ => False
  acceptsOutput := fun _ _ => False
  process := process
  acceptsInputDecidable := fun _ _ => inferInstance
  acceptsProcessingDecidable := fun _ _ => inferInstance
  acceptsOutputDecidable := fun _ _ => inferInstance

def definition {before after} : Operation before after →
    OperationDefinition schema Port Guard
  | .insert =>
      { trigger := .commanded
        guards := []
        requirements := [bagRequirement, pouchRequirement]
        processKind := some .insert
        effects := [.executeProcess] }
  | .extract =>
      { trigger := .commanded
        guards := []
        requirements := [linkRequirement, leaseRequirement]
        processKind := some .extract
        effects := [.executeProcess] }

def language : OperationLanguage schema where
  Mode := Mode
  Operation := Operation
  QueuePort := Port
  Guard := Guard
  modeDecidableEq := inferInstance
  definition := definition

def machine : Machine schema := Machine.empty bagAccount 0 bagBody

def genesis : GenesisPlan where
  grants :=
    [{ account := bagAccount,
       entry := { resourceId := bagBody, quantity := .one, positive := by decide } },
     { account := pouchAccount,
       entry := { resourceId := pouchBody, quantity := .one, positive := by decide } },
     { account := bagAccount,
       entry := { resourceId := endpointFamily.encode 2, quantity := .one,
                  positive := by decide } },
     { account := pouchAccount,
       entry := { resourceId := endpointFamily.encode 3, quantity := .one,
                  positive := by decide } },
     { account := pouchAccount,
       entry := { resourceId := cargoId, quantity := ⟨3⟩, positive := by decide } }]
  keysUnique := by native_decide

def world : WorldState recipeCatalog :=
  match applyGenesis recipeCatalog genesis with
  | .ok applied => applied.after | .error _ => WorldState.empty recipeCatalog

def runtime : MachineRuntime schema language where
  mode := .separate; machine := machine
  custody := MachineCustody.empty machine.inventory
  activeCustodyHeld := by simp [Machine.ActiveDependenciesSatisfy, machine, Machine.empty]
  nextProcessId := 0

def evaluator : GuardEvaluator recipeCatalog schema language where
  condition := fun guard _ => nomatch guard
  issues := fun guard _ => nomatch guard
  evidence := fun guard _ => nomatch guard
  issuesEmptyIff := by intro guard; exact nomatch guard

def bindings (kind : ProcessKind) : ProcessBindings Label where
  source := fun label => match kind, label with
    | .insert, .bag => bagAccount | .insert, .pouch => pouchAccount
    | .extract, .link | .extract, .lease => ledger | _, _ => custodyAccount
  custody := fun _ => custodyAccount
  output := fun label => match kind, label with
    | .insert, .link | .insert, .lease => some ledger
    | .extract, .bag => some bagAccount | .extract, .pouch => some pouchAccount
    | _, _ => none

def proposal {before after} (operation : Operation before after) (kind : ProcessKind) :
    OperationProposal schema language where
  before := before; after := after; operation := operation
  possessionBindings := { resolve := (bindings kind).source }
  custodyBindings := { resolve := fun _ => none }
  processBindings := some (bindings kind)
  queueBindings := { resolve := fun port => nomatch port }
  recipientBindings := { resolve := fun _ => none }

def insertRun := applyRuntimeOperation evaluator world runtime
  (MachineCustody.backed_empty world machine.inventory) (proposal .insert .insert)

def nestedWorld : WorldState recipeCatalog :=
  match insertRun with | .ok applied => applied.afterWorld | .error _ => world

def path : RelationPath Nat where
  origin := describeEndpoint 2
  hops := [{ link := 1, forward := true }]
  linksUnique := by simp

example : relationPathIssues relationModel relationPolicy nestedWorld path = [] := by
  native_decide

end Maquina.Recipes.NestedContainers
