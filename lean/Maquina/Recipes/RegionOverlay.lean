import Maquina.Recipes.Support

/-!
# Recipe: Region Overlay

Rain is a Region Machine Operation. Its Process creates an overlay Link and
Humidity Resources in affected Machine inventories; the relation projection
then explains why that context is reachable.
-/

namespace Maquina.Recipes.RegionOverlay
open Support

inductive Label where | region | target | phase | link | lease | humidity
  deriving DecidableEq, Repr
inductive ProcessKind where | beginRain deriving DecidableEq, Repr
inductive Mode where | dry | raining deriving DecidableEq, Repr
inductive Operation : Mode → Mode → Type where
  | beginRain : Operation .dry .raining deriving Repr
inductive Guard deriving DecidableEq, Repr
inductive Port : QueueStage → Type deriving Repr

def endpointBasket (key : Nat) := Basket.singleton (endpointFamily.encode key) .one (by decide)
def phaseBasket := Basket.singleton phaseOpenId .one (by decide)
def linkBasket := Basket.singleton (linkFamily.encode 5) .one (by decide)
def leaseBasket := relationLeaseBasket relationModel 5
def humidityBasket := Basket.singleton humidityId ⟨5⟩ (by decide)
def regionRequirement : PossessionPort Label :=
  { label := .region, basket := endpointBasket 7,
    nonempty := by simp [endpointBasket, Basket.singleton] }
def targetRequirement : PossessionPort Label :=
  { label := .target, basket := endpointBasket 4,
    nonempty := by simp [endpointBasket, Basket.singleton] }
def phaseRequirement : PossessionPort Label :=
  { label := .phase, basket := phaseBasket,
    nonempty := by simp [phaseBasket, Basket.singleton] }

def rainProcess : Process Label where
  consumed :=
    [{ label := .region, basket := endpointBasket 7,
       nonempty := by simp [endpointBasket, Basket.singleton] },
     { label := .target, basket := endpointBasket 4,
       nonempty := by simp [endpointBasket, Basket.singleton] },
     { label := .phase, basket := phaseBasket,
       nonempty := by simp [phaseBasket, Basket.singleton] }]
  reserved := []
  activeCustody := []
  outputs :=
    [{ label := .link, basket := linkBasket,
       nonempty := by simp [linkBasket, Basket.singleton] },
     { label := .lease, basket := leaseBasket,
       nonempty := by simp [leaseBasket, relationLeaseBasket, Basket.singleton] },
     { label := .humidity, basket := humidityBasket,
       nonempty := by simp [humidityBasket, Basket.singleton] }]
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
  process := fun _ => rainProcess
  acceptsInputDecidable := fun _ _ => inferInstance
  acceptsProcessingDecidable := fun _ _ => inferInstance
  acceptsOutputDecidable := fun _ _ => inferInstance
def language : OperationLanguage schema where
  Mode := Mode
  Operation := Operation
  QueuePort := Port
  Guard := Guard
  modeDecidableEq := inferInstance
  definition := fun operation => match operation with
    | .beginRain =>
        { trigger := .reactive
          guards := []
          requirements := [regionRequirement, targetRequirement, phaseRequirement]
          processKind := some .beginRain
          effects := [.executeProcess] }

def machine : Machine schema := Machine.empty regionAccount 0 regionBody
def genesis : GenesisPlan where
  grants :=
    [{ account := regionAccount,
       entry := { resourceId := regionBody, quantity := .one, positive := by decide } },
     { account := vehicleAccount,
       entry := { resourceId := vehicleBody, quantity := .one, positive := by decide } },
     { account := regionAccount,
       entry := { resourceId := endpointFamily.encode 7, quantity := .one,
                  positive := by decide } },
     { account := vehicleAccount,
       entry := { resourceId := endpointFamily.encode 4, quantity := .one,
                  positive := by decide } },
     { account := regionAccount,
       entry := { resourceId := phaseOpenId, quantity := .one, positive := by decide } }]
  keysUnique := by native_decide
def world : WorldState recipeCatalog := match applyGenesis recipeCatalog genesis with
  | .ok applied => applied.after | .error _ => WorldState.empty recipeCatalog
def runtime : MachineRuntime schema language where
  mode := .dry
  machine := machine
  custody := MachineCustody.empty machine.inventory
  activeCustodyHeld := by simp [Machine.ActiveDependenciesSatisfy, machine, Machine.empty]
  nextProcessId := 0
def evaluator : GuardEvaluator recipeCatalog schema language where
  condition := fun guard _ => nomatch guard
  issues := fun guard _ => nomatch guard
  evidence := fun guard _ => nomatch guard
  issuesEmptyIff := by intro guard; exact nomatch guard
def bindings : ProcessBindings Label where
  source
    | .region | .phase => regionAccount
    | .target => vehicleAccount
    | _ => custodyAccount
  custody := fun _ => custodyAccount
  output
    | .link | .lease => some ledger
    | .humidity => some vehicleAccount
    | _ => none
def proposal : OperationProposal schema language where
  before := .dry
  after := .raining
  operation := .beginRain
  possessionBindings := { resolve := bindings.source }
  custodyBindings := { resolve := fun _ => none }
  processBindings := some bindings
  queueBindings := { resolve := fun port => nomatch port }
  recipientBindings := { resolve := fun _ => none }
def run := applyRuntimeOperation evaluator world runtime
  (MachineCustody.backed_empty world machine.inventory) proposal
def rainingWorld : WorldState recipeCatalog :=
  match run with | .ok applied => applied.afterWorld | .error _ => world

def directory : MachineDirectory where
  entries := [{ body := regionBody, inventory := regionAccount },
    { body := vehicleBody, inventory := vehicleAccount }]
  bodiesUnique := by native_decide
def path : RelationPath Nat where
  origin := describeEndpoint 7
  hops := [{ link := 5, forward := true }]
  linksUnique := by simp
def humidityRequirement : ReachableResourceRequirement Nat where
  root := regionBody
  path := path
  resourceId := humidityId
  minimum := ⟨5⟩
  positive := by decide

example : reachableResourceIssues relationModel relationPolicy directory
    rainingWorld humidityRequirement = [] := by native_decide

end Maquina.Recipes.RegionOverlay
