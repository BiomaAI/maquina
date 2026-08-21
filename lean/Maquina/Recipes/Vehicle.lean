import Maquina.Recipes.Support

/-!
# Recipe: Vehicle Assembly

A vehicle is a Machine whose component relation is formed by a declared
assembly Process. Selling or transferring the chassis requires disassembly
first because assembly consumes its open endpoint Resource.
-/

namespace Maquina.Recipes.Vehicle
open Support

inductive Label where | vehicle | chassis | link | lease deriving DecidableEq, Repr
inductive ProcessKind where | assemble deriving DecidableEq, Repr
inductive Mode where | frameOpen | assembled deriving DecidableEq, Repr
inductive Operation : Mode → Mode → Type where
  | assemble : Operation .frameOpen .assembled deriving Repr
inductive Guard deriving DecidableEq, Repr
inductive Port : QueueStage → Type deriving Repr

def endpointBasket (key : Nat) := Basket.singleton (endpointFamily.encode key) .one (by decide)
def linkBasket := Basket.singleton (linkFamily.encode 2) .one (by decide)
def leaseBasket := relationLeaseBasket relationModel 2
def vehicleRequirement : PossessionPort Label :=
  { label := .vehicle, basket := endpointBasket 4,
    nonempty := by simp [endpointBasket, Basket.singleton] }
def chassisRequirement : PossessionPort Label :=
  { label := .chassis, basket := endpointBasket 0,
    nonempty := by simp [endpointBasket, Basket.singleton] }

def assembleProcess : Process Label where
  consumed :=
    [{ label := .vehicle, basket := endpointBasket 4,
       nonempty := by simp [endpointBasket, Basket.singleton] },
     { label := .chassis, basket := endpointBasket 0,
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
  process := fun _ => assembleProcess
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
    | .assemble =>
        { trigger := .commanded
          guards := []
          requirements := [vehicleRequirement, chassisRequirement]
          processKind := some .assemble
          effects := [.executeProcess] }

def machine : Machine schema := Machine.empty vehicleAccount 0 vehicleBody

def genesis : GenesisPlan where
  grants :=
    [{ account := vehicleAccount,
       entry := { resourceId := vehicleBody, quantity := .one, positive := by decide } },
     { account := chassisAccount,
       entry := { resourceId := chassisBody, quantity := .one, positive := by decide } },
     { account := vehicleAccount,
       entry := { resourceId := endpointFamily.encode 4, quantity := .one,
                  positive := by decide } },
     { account := chassisAccount,
       entry := { resourceId := endpointFamily.encode 0, quantity := .one,
                  positive := by decide } }]
  keysUnique := by native_decide

def world : WorldState recipeCatalog := match applyGenesis recipeCatalog genesis with
  | .ok applied => applied.after | .error _ => WorldState.empty recipeCatalog

def runtime : MachineRuntime schema language where
  mode := .frameOpen; machine := machine; custody := MachineCustody.empty machine.inventory
  activeCustodyHeld := by simp [Machine.ActiveDependenciesSatisfy, machine, Machine.empty]
  nextProcessId := 0

def evaluator : GuardEvaluator recipeCatalog schema language where
  condition := fun guard _ => nomatch guard; issues := fun guard _ => nomatch guard
  evidence := fun guard _ => nomatch guard
  issuesEmptyIff := by intro guard; exact nomatch guard

def processBindings : ProcessBindings Label where
  source | .vehicle => vehicleAccount | .chassis => chassisAccount | _ => custodyAccount
  custody := fun _ => custodyAccount
  output | .link | .lease => some ledger | _ => none

def proposal : OperationProposal schema language where
  before := .frameOpen; after := .assembled; operation := .assemble
  possessionBindings := { resolve := processBindings.source }
  custodyBindings := { resolve := fun _ => none }
  processBindings := some processBindings
  queueBindings := { resolve := fun port => nomatch port }
  recipientBindings := { resolve := fun _ => none }

def run := applyRuntimeOperation evaluator world runtime
  (MachineCustody.backed_empty world machine.inventory) proposal

def assembledWorld : WorldState recipeCatalog :=
  match run with | .ok applied => applied.afterWorld | .error _ => world

example : (assembledWorld.balance ledger (linkFamily.encode 2)).atoms = 1 := by
  native_decide

end Maquina.Recipes.Vehicle
