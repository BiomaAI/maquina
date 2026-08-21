import Maquina.Recipes.Support

/-!
# Recipe: Shared Capability and Active Path Dependency

An operation uses a capability held by a related tool Machine. Reachability is
a structured guard over an active Link. Dispatch reserves that Link's lease as
ordinary Process input; a concurrent detach Operation then rejects because the
lease is unavailable. The Link itself remains authoritative and active.
-/

namespace Maquina.Recipes.SharedCapability
open Support

inductive Label where | capability | lease | link | vehicleEndpoint | toolEndpoint
  deriving DecidableEq, Repr
inductive ProcessKind where | useCapability | detach deriving DecidableEq, Repr
inductive Mode where | available | queued | active deriving DecidableEq, Repr
inductive Operation : Mode → Mode → Type where
  | beginUse : Operation .available .queued
  | dispatchUse : Operation .queued .active
  | detachWhileActive : Operation .active .active
  deriving Repr
inductive Guard where | capabilityReachable deriving DecidableEq, Repr
inductive InputKind where | capabilityUse deriving DecidableEq, Repr
inductive ProcessingKind where | capabilityUse deriving DecidableEq, Repr
inductive OutputKind deriving DecidableEq, Repr
inductive Port : QueueStage → Type where
  | input : Port .input
  | processing : Port .processing
  deriving Repr

def capabilityBasket := Basket.singleton capabilityId .one (by decide)
def leaseBasket := relationLeaseBasket relationModel 6
def linkBasket := Basket.singleton (linkFamily.encode 6) .one (by decide)
def vehicleEndpointBasket := Basket.singleton (endpointFamily.encode 4) .one (by decide)
def toolEndpointBasket := Basket.singleton (endpointFamily.encode 8) .one (by decide)

def useProcess : Process Label where
  consumed := []
  reserved :=
    [{ label := .lease, basket := leaseBasket,
       nonempty := by simp [leaseBasket, relationLeaseBasket, Basket.singleton] }]
  activeCustody := []
  outputs := []
  consumedLabelsUnique := by simp
  reservedLabelsUnique := by simp
  activeCustodyLabelsUnique := by simp
  outputLabelsUnique := by simp
  requiredWork := 1

def detachProcess : Process Label where
  consumed :=
    [{ label := .link, basket := linkBasket,
       nonempty := by simp [linkBasket, Basket.singleton] },
     { label := .lease, basket := leaseBasket,
       nonempty := by simp [leaseBasket, relationLeaseBasket, Basket.singleton] }]
  reserved := []
  activeCustody := []
  outputs :=
    [{ label := .vehicleEndpoint, basket := vehicleEndpointBasket,
       nonempty := by simp [vehicleEndpointBasket, Basket.singleton] },
     { label := .toolEndpoint, basket := toolEndpointBasket,
       nonempty := by simp [toolEndpointBasket, Basket.singleton] }]
  consumedLabelsUnique := by simp
  reservedLabelsUnique := by simp
  activeCustodyLabelsUnique := by simp
  outputLabelsUnique := by simp
  requiredWork := 0

def schema : MachineSchema where
  ProcessKind := ProcessKind
  Label := Label
  InputQueueKind := InputKind
  ProcessingQueueKind := ProcessingKind
  OutputQueueKind := OutputKind
  processKindDecidableEq := inferInstance
  labelDecidableEq := inferInstance
  acceptsInput := fun _ kind => kind = .useCapability
  acceptsProcessing := fun _ kind => kind = .useCapability
  acceptsOutput := fun kind => nomatch kind
  process | .useCapability => useProcess | .detach => detachProcess
  acceptsInputDecidable := fun _ _ => inferInstance
  acceptsProcessingDecidable := fun _ _ => inferInstance
  acceptsOutputDecidable := fun kind => nomatch kind

def capabilityRequirement : PossessionPort Label where
  label := .capability
  basket := capabilityBasket
  nonempty := by simp [capabilityBasket, Basket.singleton]
def linkRequirement : PossessionPort Label where
  label := .link
  basket := linkBasket
  nonempty := by simp [linkBasket, Basket.singleton]
def leaseRequirement : PossessionPort Label where
  label := .lease
  basket := leaseBasket
  nonempty := by simp [leaseBasket, relationLeaseBasket, Basket.singleton]

def definition {before after} : Operation before after →
    OperationDefinition schema Port Guard
  | .beginUse =>
      { trigger := .commanded
        guards := [.capabilityReachable]
        requirements := [capabilityRequirement]
        processKind := some .useCapability
        effects := [.reserveConsumedInputs, .enqueue .input] }
  | .dispatchUse =>
      { trigger := .reactive
        guards := [.capabilityReachable]
        requirements := [capabilityRequirement]
        processKind := some .useCapability
        effects := [.reserveReservedInputs .input,
          .moveToProcessing .input .processing] }
  | .detachWhileActive =>
      { trigger := .commanded
        guards := []
        requirements := [linkRequirement, leaseRequirement]
        processKind := some .detach
        effects := [.executeProcess] }

def language : OperationLanguage schema where
  Mode := Mode
  Operation := Operation
  QueuePort := Port
  Guard := Guard
  modeDecidableEq := inferInstance
  definition := definition

def inputQueue : MachineInputQueue schema :=
  MachineInputQueue.empty ⟨0⟩ .capabilityUse (some 1)
def processingQueue : MachineProcessingQueue schema :=
  MachineProcessingQueue.empty ⟨0⟩ .capabilityUse (some 1)
def machine : Machine schema where
  inventory := vehicleAccount
  body := vehicleBody
  maximumQueues := 2
  inputQueues := [inputQueue]
  processingQueues := [processingQueue]
  outputQueues := []
  inputIdsUnique := by simp
  processingIdsUnique := by simp
  outputIdsUnique := by simp
  nextInputQueueId := 1
  nextProcessingQueueId := 1
  nextOutputQueueId := 0
  inputIdsBeforeNext := by
    intro queue member
    simp only [List.mem_singleton] at member
    subst queue
    decide
  processingIdsBeforeNext := by
    intro queue member
    simp only [List.mem_singleton] at member
    subst queue
    decide
  outputIdsBeforeNext := by simp
  withinQueueLimit := by decide

def genesis : GenesisPlan where
  grants :=
    [{ account := vehicleAccount,
       entry := { resourceId := vehicleBody, quantity := .one, positive := by decide } },
     { account := toolAccount,
       entry := { resourceId := toolBody, quantity := .one, positive := by decide } },
     { account := toolAccount,
       entry := { resourceId := capabilityId, quantity := .one, positive := by decide } },
     { account := ledger,
       entry := { resourceId := linkFamily.encode 6, quantity := .one,
                  positive := by decide } },
     { account := ledger,
       entry := { resourceId := leaseFamily.encode 6, quantity := .one,
                  positive := by decide } }]
  keysUnique := by native_decide

def world : WorldState recipeCatalog := match applyGenesis recipeCatalog genesis with
  | .ok applied => applied.after | .error _ => WorldState.empty recipeCatalog

def directory : MachineDirectory where
  entries := [{ body := vehicleBody, inventory := vehicleAccount },
    { body := toolBody, inventory := toolAccount }]
  bodiesUnique := by native_decide
def path : RelationPath Nat where
  origin := describeEndpoint 4
  hops := [{ link := 6, forward := true }]
  linksUnique := by simp
def reachableCapability : ReachableResourceRequirement Nat where
  root := vehicleBody
  path := path
  resourceId := capabilityId
  minimum := .one
  positive := by decide

example : RelationPathDependenciesExact relationModel path useProcess.reserved := by
  simp [RelationPathDependenciesExact, RelationPathDependency, path, useProcess,
    leaseBasket]

def guardCondition
    (_ : Guard)
    (state : SimulatorState recipeCatalog schema language) : Prop :=
  reachableResourceIssues relationModel relationPolicy directory state.world
    reachableCapability = []
def guardIssues
    (_ : Guard)
    (state : SimulatorState recipeCatalog schema language) : List GuardIssue :=
  let failures := reachableResourceIssues relationModel relationPolicy directory
    state.world reachableCapability
  if failures = [] then [] else
    [{ condition := "capability-reachable"
       code := "relation-path-rejected"
       detail := "the declared relation path or reachable holding is unavailable" }]
def guardEvidence
    (_ : Guard)
    (_ : SimulatorState recipeCatalog schema language) : GuardEvidence :=
  { condition := "capability-reachable"
    detail := "the capability is held by a Machine on an active relation path" }
theorem guardIssues_empty_iff (guard : Guard)
    (state : SimulatorState recipeCatalog schema language) :
    guardIssues guard state = [] ↔ guardCondition guard state := by
  simp only [guardIssues, guardCondition]
  split <;> simp_all
def evaluator : GuardEvaluator recipeCatalog schema language where
  condition := guardCondition
  issues := guardIssues
  evidence := guardEvidence
  issuesEmptyIff := guardIssues_empty_iff

def runtime : MachineRuntime schema language where
  mode := .available
  machine := machine
  custody := MachineCustody.empty machine.inventory
  activeCustodyHeld := by
    simp [Machine.ActiveDependenciesSatisfy, machine,
      MachineProcessingQueue.DependenciesSatisfy,
      MachineProcessingQueue.activeCustodyDependencies, processingQueue,
      MachineProcessingQueue.empty, Queue.empty]
  nextProcessId := 0

def queueBindings : QueueBindings Port where
  resolve | .input => some ⟨0⟩ | .processing => some ⟨0⟩
def useBindings : ProcessBindings Label where
  source | .lease => ledger | .capability => toolAccount | _ => vehicleAccount
  custody := fun _ => custodyAccount
  output := fun _ => none
def detachBindings : ProcessBindings Label where
  source | .link | .lease => ledger | _ => custodyAccount
  custody := fun _ => custodyAccount
  output
    | .vehicleEndpoint => some vehicleAccount
    | .toolEndpoint => some toolAccount
    | _ => none
def proposal {before after} (operation : Operation before after)
    (bindings : ProcessBindings Label) : OperationProposal schema language where
  before := before
  after := after
  operation := operation
  possessionBindings := { resolve := bindings.source }
  custodyBindings := { resolve := fun _ => none }
  processBindings := some bindings
  queueBindings := queueBindings
  recipientBindings := { resolve := fun _ => none }

def initialState : SimulatorState recipeCatalog schema language :=
  runtime.toState world (MachineCustody.backed_empty world machine.inventory)
def beginRun := applyOperation evaluator initialState (proposal .beginUse useBindings)
def queuedState : SimulatorState recipeCatalog schema language :=
  match beginRun with | .ok applied => applied.after | .error _ => initialState
def dispatchRun := applyOperation evaluator queuedState
  (proposal .dispatchUse useBindings)
def activeState : SimulatorState recipeCatalog schema language :=
  match dispatchRun with | .ok applied => applied.after | .error _ => queuedState
def activeWorld : WorldState recipeCatalog := activeState.world

def detachRun := applyOperation evaluator activeState
  (proposal .detachWhileActive detachBindings)
def detachIssues : Option (List SimulatorIssue) :=
  match detachRun with | .error issues => some issues | .ok _ => none

example : (activeWorld.balance ledger (linkFamily.encode 6)).atoms = 1 := by
  native_decide
example : (activeWorld.balance ledger (leaseFamily.encode 6)).atoms = 0 := by
  native_decide
example : detachIssues = some [.possessionRejected
    [{ requirementIndex := 1, account := ledger,
       issues := [.shortfall (leaseFamily.encode 6) 1 0 1] }]] := by
  native_decide

end Maquina.Recipes.SharedCapability
