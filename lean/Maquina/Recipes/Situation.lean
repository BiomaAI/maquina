import Maquina.Recipes.Support

/-!
# Recipe: Emergent Situation

A Situation is an ordinary Machine configuration. Its phase is a Resource and
its Operations only manifest opportunities. Agents decide whether to consume
those opportunities. De-escalation requires all opportunity tokens returned.
-/

namespace Maquina.Recipes.Situation
open Support

inductive Label where | phase | opportunities deriving DecidableEq, Repr
inductive ProcessKind where | escalate | deescalate deriving DecidableEq, Repr
inductive Mode where | open | active deriving DecidableEq, Repr
inductive Operation : Mode → Mode → Type where
  | escalate : Operation .open .active
  | deescalate : Operation .active .open
  deriving Repr
inductive Guard deriving DecidableEq, Repr
inductive Port : QueueStage → Type deriving Repr

def openPhase := Basket.singleton phaseOpenId .one (by decide)
def activePhase := Basket.singleton phaseActiveId .one (by decide)
def opportunities := Basket.singleton violenceId ⟨3⟩ (by decide)
def openRequirement : PossessionPort Label :=
  { label := .phase, basket := openPhase,
    nonempty := by simp [openPhase, Basket.singleton] }
def activeRequirement : PossessionPort Label :=
  { label := .phase, basket := activePhase,
    nonempty := by simp [activePhase, Basket.singleton] }
def opportunitiesRequirement : PossessionPort Label :=
  { label := .opportunities, basket := opportunities,
    nonempty := by simp [opportunities, Basket.singleton] }

def process : ProcessKind → Process Label
  | .escalate =>
      { consumed := [{ label := .phase, basket := openPhase,
                       nonempty := by simp [openPhase, Basket.singleton] }]
        reserved := []
        activeCustody := []
        outputs :=
          [{ label := .phase, basket := activePhase,
             nonempty := by simp [activePhase, Basket.singleton] },
           { label := .opportunities, basket := opportunities,
             nonempty := by simp [opportunities, Basket.singleton] }]
        consumedLabelsUnique := by simp
        reservedLabelsUnique := by simp
        activeCustodyLabelsUnique := by simp
        outputLabelsUnique := by simp
        requiredWork := 0 }
  | .deescalate =>
      { consumed :=
          [{ label := .phase, basket := activePhase,
             nonempty := by simp [activePhase, Basket.singleton] },
           { label := .opportunities, basket := opportunities,
             nonempty := by simp [opportunities, Basket.singleton] }]
        reserved := []
        activeCustody := []
        outputs := [{ label := .phase, basket := openPhase,
                      nonempty := by simp [openPhase, Basket.singleton] }]
        consumedLabelsUnique := by simp
        reservedLabelsUnique := by simp
        activeCustodyLabelsUnique := by simp
        outputLabelsUnique := by simp
        requiredWork := 0 }

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
  process := process
  acceptsInputDecidable := fun _ _ => inferInstance
  acceptsProcessingDecidable := fun _ _ => inferInstance
  acceptsOutputDecidable := fun _ _ => inferInstance

def definition {before after} : Operation before after →
    OperationDefinition schema Port Guard
  | .escalate =>
      { trigger := .reactive
        guards := []
        requirements := [openRequirement]
        processKind := some .escalate
        effects := [.executeProcess] }
  | .deescalate =>
      { trigger := .reactive
        guards := []
        requirements := [activeRequirement, opportunitiesRequirement]
        processKind := some .deescalate
        effects := [.executeProcess] }

def language : OperationLanguage schema where
  Mode := Mode
  Operation := Operation
  QueuePort := Port
  Guard := Guard
  modeDecidableEq := inferInstance
  definition := definition

def machine : Machine schema := Machine.empty situationAccount 0 situationBody
def genesis : GenesisPlan where
  grants :=
    [{ account := situationAccount,
       entry := { resourceId := situationBody, quantity := .one, positive := by decide } },
     { account := situationAccount,
       entry := { resourceId := phaseOpenId, quantity := .one, positive := by decide } }]
  keysUnique := by native_decide
def world : WorldState recipeCatalog := match applyGenesis recipeCatalog genesis with
  | .ok applied => applied.after | .error _ => WorldState.empty recipeCatalog
def runtime : MachineRuntime schema language where
  mode := .open
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
  source := fun _ => situationAccount
  custody := fun _ => custodyAccount
  output := fun _ => some situationAccount
def proposal : OperationProposal schema language where
  before := .open
  after := .active
  operation := .escalate
  possessionBindings := { resolve := fun _ => situationAccount }
  custodyBindings := { resolve := fun _ => none }
  processBindings := some bindings
  queueBindings := { resolve := fun port => nomatch port }
  recipientBindings := { resolve := fun _ => none }
def run := applyRuntimeOperation evaluator world runtime
  (MachineCustody.backed_empty world machine.inventory) proposal
def activeWorld : WorldState recipeCatalog :=
  match run with | .ok applied => applied.afterWorld | .error _ => world
example : (activeWorld.balance situationAccount violenceId).atoms = 3 := by
  native_decide
example : (activeWorld.balance situationAccount phaseActiveId).atoms = 1 := by
  native_decide

end Maquina.Recipes.Situation
