import Maquina.Recipes.Support

/-!
# Recipe: Crew Membership

Mounting a crew into a vehicle is a membership relation formed by a Machine
Operation and Process. The crew remains a separately identified Machine.
-/

namespace Maquina.Recipes.Crew
open Support

inductive Label where | vehicle | crew | link | lease deriving DecidableEq, Repr
inductive ProcessKind where | mount deriving DecidableEq, Repr
inductive Mode where | awaiting | mounted deriving DecidableEq, Repr
inductive Operation : Mode → Mode → Type where | mount : Operation .awaiting .mounted deriving Repr
inductive Guard deriving DecidableEq, Repr
inductive Port : QueueStage → Type deriving Repr

def endpointBasket (key : Nat) := Basket.singleton (endpointFamily.encode key) .one (by decide)
def linkBasket := Basket.singleton (linkFamily.encode 3) .one (by decide)
def leaseBasket := relationLeaseBasket relationModel 3
def vehicleRequirement : PossessionPort Label :=
  { label := .vehicle, basket := endpointBasket 4,
    nonempty := by simp [endpointBasket, Basket.singleton] }
def crewRequirement : PossessionPort Label :=
  { label := .crew, basket := endpointBasket 5,
    nonempty := by simp [endpointBasket, Basket.singleton] }

def mountProcess : Process Label where
  consumed :=
    [{ label := .vehicle, basket := endpointBasket 4,
       nonempty := by simp [endpointBasket, Basket.singleton] },
     { label := .crew, basket := endpointBasket 5,
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
  process := fun _ => mountProcess
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
    | .mount =>
        { trigger := .commanded
          guards := []
          requirements := [vehicleRequirement, crewRequirement]
          processKind := some .mount
          effects := [.executeProcess] }

def machine : Machine schema := Machine.empty vehicleAccount 0 vehicleBody
def genesis : GenesisPlan where
  grants :=
    [{ account := vehicleAccount,
       entry := { resourceId := vehicleBody, quantity := .one, positive := by decide } },
     { account := crewAccount,
       entry := { resourceId := crewBody, quantity := .one, positive := by decide } },
     { account := vehicleAccount,
       entry := { resourceId := endpointFamily.encode 4, quantity := .one,
                  positive := by decide } },
     { account := crewAccount,
       entry := { resourceId := endpointFamily.encode 5, quantity := .one,
                  positive := by decide } },
     { account := crewAccount,
       entry := { resourceId := driverSeatId, quantity := .one, positive := by decide } }]
  keysUnique := by native_decide
def world : WorldState recipeCatalog := match applyGenesis recipeCatalog genesis with
  | .ok applied => applied.after | .error _ => WorldState.empty recipeCatalog

def runtime : MachineRuntime schema language where
  mode := .awaiting; machine := machine; custody := MachineCustody.empty machine.inventory
  activeCustodyHeld := by simp [Machine.ActiveDependenciesSatisfy, machine, Machine.empty]
  nextProcessId := 0
def evaluator : GuardEvaluator recipeCatalog schema language where
  condition := fun guard _ => nomatch guard; issues := fun guard _ => nomatch guard
  evidence := fun guard _ => nomatch guard
  issuesEmptyIff := by intro guard; exact nomatch guard
def bindings : ProcessBindings Label where
  source | .vehicle => vehicleAccount | .crew => crewAccount | _ => custodyAccount
  custody := fun _ => custodyAccount
  output | .link | .lease => some ledger | _ => none
def proposal : OperationProposal schema language where
  before := .awaiting; after := .mounted; operation := .mount
  possessionBindings := { resolve := bindings.source }
  custodyBindings := { resolve := fun _ => none }; processBindings := some bindings
  queueBindings := { resolve := fun port => nomatch port }
  recipientBindings := { resolve := fun _ => none }
def run := applyRuntimeOperation evaluator world runtime
  (MachineCustody.backed_empty world machine.inventory) proposal
def mountedWorld : WorldState recipeCatalog :=
  match run with | .ok applied => applied.afterWorld | .error _ => world
example : RelationModel.LinkActive relationModel mountedWorld 3 := by
  change (mountedWorld.balance ledger (linkFamily.encode 3)).atoms = 1
  native_decide

end Maquina.Recipes.Crew
