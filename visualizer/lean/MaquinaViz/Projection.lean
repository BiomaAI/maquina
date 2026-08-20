import Maquina.Simulator
import MaquinaViz.Protocol

/-!
# Generic Maquina Trace Projection

The projector executes only the generic simulator and converts its proof-backed
results into the versioned visualization protocol. Games provide vocabulary and
declarative presentation, but no transition or rendering code.
-/

namespace Maquina.Visualization

open Maquina

def accountKey (account : AccountId) : String :=
  s!"account:{account.value}"

def resourceKey (resource : ResourceId) : String :=
  s!"resource:{resource.value}"

def processKey (processId : Nat) : String :=
  s!"process:{processId}"

def queueKey (machineId stage : String) (queueId : Nat) : String :=
  s!"{machineId}:queue:{stage}:{queueId}"

def custodyKey (machineId : String) (positionId : Nat) : String :=
  s!"{machineId}:custody:{positionId}"

/-- The only game-specific functions required by the shared projector. -/
structure Projection
    (schema : MachineSchema)
    (language : OperationLanguage schema) where
  machineId : String
  modeName : language.Mode → String
  operationName : {before after : language.Mode} →
    language.Operation before after → String
  processKindName : schema.ProcessKind → String
  inputQueueKindName : schema.InputQueueKind → String
  processingQueueKindName : schema.ProcessingQueueKind → String
  outputQueueKindName : schema.OutputQueueKind → String

def stageName : QueueStage → String
  | .input => "input"
  | .processing => "processing"
  | .output => "output"

def triggerName : OperationTrigger → String
  | .commanded => "commanded"
  | .scheduled => "scheduled"
  | .reactive => "reactive"

def cancellationName : CancellationDisposition → String
  | .returnInputs => "return-inputs"
  | .consumeInputs => "consume-inputs"

private def queuedProcessView
    (projection : Projection schema language)
    (ticket : Nat)
    (process : QueuedProcess schema)
    (progress : Nat) : ProcessView where
  ticket := exactNat ticket
  id := processKey process.id
  kind := projection.processKindName process.kind
  progress := exactNat progress
  requiredWork := exactNat (schema.process process.kind).requiredWork

private def inputQueueView
    (projection : Projection schema language)
    (queue : MachineInputQueue schema) : QueueView where
  id := queueKey projection.machineId "input" queue.id.value
  stage := "input"
  capacity := queue.contents.capacity.map exactNat
  entries := queue.contents.entries.map fun entry =>
    queuedProcessView projection entry.ticket entry.value.process 0

private def processingQueueView
    (projection : Projection schema language)
    (queue : MachineProcessingQueue schema) : QueueView where
  id := queueKey projection.machineId "processing" queue.id.value
  stage := "processing"
  capacity := queue.contents.capacity.map exactNat
  entries := queue.contents.entries.map fun entry =>
    queuedProcessView projection entry.ticket entry.value.process.queued
      entry.value.process.progress

private def outputQueueView
    (projection : Projection schema language)
    (queue : MachineOutputQueue schema) : QueueView where
  id := queueKey projection.machineId "output" queue.id.value
  stage := "output"
  capacity := queue.contents.capacity.map exactNat
  entries := queue.contents.entries.map fun entry =>
    queuedProcessView projection entry.ticket entry.value.process.active.queued
      entry.value.process.active.progress

def projectState
    (projection : Projection schema language)
    (state : SimulatorState resourceCatalog schema language) : StateView :=
  let inputQueues := state.machine.inputQueues.map (inputQueueView projection)
  let processingQueues :=
    state.machine.processingQueues.map (processingQueueView projection)
  let outputQueues := state.machine.outputQueues.map (outputQueueView projection)
  { holdings := state.world.holdings.map fun holding =>
      { account := accountKey holding.account
        resource := resourceKey holding.resourceId
        quantity := exactNat holding.quantity.atoms }
    machines :=
      [{ id := projection.machineId
         inventory := accountKey state.machine.inventory
         mode := projection.modeName state.mode
         maximumQueues := exactNat state.machine.maximumQueues
         queues := inputQueues ++ processingQueues ++ outputQueues }]
    custody := state.custody.positions.map fun position =>
      { id := custodyKey projection.machineId position.id
        source := accountKey position.source
        destination := accountKey position.destination
        contents := position.basket.entries.map fun entry =>
          { resource := resourceKey entry.resourceId
            quantity := exactNat entry.quantity.atoms }
        active := decide (position.id ∈ state.machine.activeCustodyPositionIds) }
    nextProcessId := exactNat state.nextProcessId }

private def issueCode : SimulatorIssue → String
  | .wrongMode => "wrong-mode"
  | .guardRejected _ => "guard-rejected"
  | .missingProcessKind => "missing-process-kind"
  | .missingProcessBindings => "missing-process-bindings"
  | .pendingProcessAlreadyExists => "pending-process-already-exists"
  | .pendingProcessMissing => "pending-process-missing"
  | .pendingProcessNotEnqueued => "pending-process-not-enqueued"
  | .consumedInputsMissing => "consumed-inputs-missing"
  | .reservedInputsAlreadyExist => "reserved-inputs-already-exist"
  | .reservedInputsMissing => "reserved-inputs-missing"
  | .queueBindingMissing _ => "queue-binding-missing"
  | .queueMissing _ _ => "queue-missing"
  | .queueRejected _ _ => "queue-rejected"
  | .queueRejectsProcess _ => "queue-rejects-process"
  | .processKindMismatch => "process-kind-mismatch"
  | .possessionRejected _ => "possession-rejected"
  | .transferRejected _ => "transfer-rejected"
  | .transformationRejected _ => "transformation-rejected"
  | .insufficientWork _ _ => "insufficient-work"
  | .recipientBindingMissing => "recipient-binding-missing"
  | .recipientAlreadyBound => "recipient-already-bound"
  | .custodyBindingMissing => "custody-binding-missing"
  | .activeCustodyRejected _ => "active-custody-rejected"
  | .custodyPositionMissing _ => "custody-position-missing"
  | .custodyPositionInUse _ => "custody-position-in-use"
  | .outputLabelMissing => "output-label-missing"
  | .outputRecipientMissing => "output-recipient-missing"
  | .machineQueueLimit => "machine-queue-limit"
  | .queueNotEmpty _ => "queue-not-empty"

def issueView (issue : SimulatorIssue) : IssueView where
  code := issueCode issue
  detail := reprStr issue

private def possessionIssueCode : PossessionIssue → String
  | .unknownResource _ => "unknown-resource"
  | .shortfall _ _ _ _ => "shortfall"

def acceptedCheckView : OperationCheckReceipt → CheckView
  | .guard evidence =>
      { kind := "guard"
        condition := evidence.condition
        status := "accepted"
        detail := evidence.detail }
  | .possession requirementIndex receipt =>
      { kind := "requirement"
        condition := "possession"
        status := "accepted"
        detail := "the bound account holds every declared resource quantity"
        requirementIndex := some requirementIndex
        account := some (accountKey receipt.account)
        observations := receipt.lines.map fun line =>
          { account := accountKey receipt.account
            resource := resourceKey line.resourceId
            required := exactNat line.required.atoms
            available := exactNat line.available.atoms } }

def rejectedCheckViews : SimulatorIssue → List CheckView
  | .guardRejected issues =>
      issues.map fun issue =>
        { kind := "guard"
          condition := issue.condition
          status := "rejected"
          detail := issue.detail
          issues := [{ code := issue.code, detail := issue.detail }] }
  | .possessionRejected failures =>
      failures.map fun failure =>
        { kind := "requirement"
          condition := "possession"
          status := "rejected"
          detail := "the bound account does not satisfy the declared basket"
          requirementIndex := some failure.requirementIndex
          account := some (accountKey failure.account)
          issues := failure.issues.map fun issue =>
            { code := possessionIssueCode issue, detail := reprStr issue } }
  | _ => []

def effectView
    (machineId : String) : SimulatorEffectReceipt → EffectView
  | .transfer receipt =>
      { kind := "transfer"
        movements := receipt.lines.map fun line =>
          { source := accountKey receipt.source
            destination := accountKey receipt.destination
            resource := resourceKey line.resourceId
            quantity := exactNat line.quantity.atoms
            sourceBefore := exactNat line.sourceBefore.atoms
            sourceAfter := exactNat line.sourceAfter.atoms
            destinationBefore := exactNat line.destinationBefore.atoms
            destinationAfter := exactNat line.destinationAfter.atoms } }
  | .transformation receipt =>
      match receipt.delta with
      | .debit account entry =>
          { kind := "transformation"
            account := some (accountKey account)
            changes :=
              [{ direction := "debit"
                 account := accountKey account
                 resource := resourceKey entry.resourceId
                 quantity := exactNat entry.quantity.atoms
                 accountBefore := exactNat receipt.accountBefore.atoms
                 accountAfter := exactNat receipt.accountAfter.atoms
                 totalBefore := exactNat receipt.totalBefore.atoms
                 totalAfter := exactNat receipt.totalAfter.atoms }] }
      | .credit account entry =>
          { kind := "transformation"
            account := some (accountKey account)
            changes :=
              [{ direction := "credit"
                 account := accountKey account
                 resource := resourceKey entry.resourceId
                 quantity := exactNat entry.quantity.atoms
                 accountBefore := exactNat receipt.accountBefore.atoms
                 accountAfter := exactNat receipt.accountAfter.atoms
                 totalBefore := exactNat receipt.totalBefore.atoms
                 totalAfter := exactNat receipt.totalAfter.atoms }] }
  | .enqueued queueId ticket processId =>
      { kind := "enqueued"
        destinationQueue := some (queueKey machineId "input" queueId)
        process := some (processKey processId)
        ticket := some (exactNat ticket) }
  | .dispatched inputQueueId processingQueueId processId =>
      { kind := "dispatched"
        sourceQueue := some (queueKey machineId "input" inputQueueId)
        destinationQueue := some (queueKey machineId "processing" processingQueueId)
        process := some (processKey processId) }
  | .advanced queueId processId before after =>
      { kind := "advanced"
        sourceQueue := some (queueKey machineId "processing" queueId)
        process := some (processKey processId)
        before := some (exactNat before)
        after := some (exactNat after) }
  | .completed processingQueueId outputQueueId processId =>
      { kind := "completed"
        sourceQueue := some (queueKey machineId "processing" processingQueueId)
        destinationQueue := outputQueueId.map (queueKey machineId "output")
        process := some (processKey processId) }
  | .recipientBound account =>
      { kind := "recipient-bound", account := some (accountKey account) }
  | .collected queueId processId =>
      { kind := "collected"
        sourceQueue := some (queueKey machineId "output" queueId)
        process := some (processKey processId) }
  | .allocationCollected queueId processId remaining =>
      { kind := "allocation-collected"
        sourceQueue := some (queueKey machineId "output" queueId)
        process := some (processKey processId)
        remaining := some (exactNat remaining) }
  | .custodyOpened positionId =>
      { kind := "custody-opened"
        position := some (custodyKey machineId positionId) }
  | .custodyClosed positionId =>
      { kind := "custody-closed"
        position := some (custodyKey machineId positionId) }
  | .custodyDependenciesBound processId positionIds =>
      { kind := "custody-dependencies-bound"
        process := some (processKey processId)
        positions := positionIds.map (custodyKey machineId) }
  | .custodyDependenciesReleased processId positionIds =>
      { kind := "custody-dependencies-released"
        process := some (processKey processId)
        positions := positionIds.map (custodyKey machineId) }
  | .reservationsReleased processId =>
      { kind := "reservations-released", process := some (processKey processId) }
  | .cancelled stage queueId processId disposition =>
      { kind := "cancelled"
        stage := some (stageName stage)
        sourceQueue := some (queueKey machineId (stageName stage) queueId)
        process := some (processKey processId)
        disposition := some (cancellationName disposition) }
  | .queueAdded stage queueId =>
      { kind := "queue-added"
        stage := some (stageName stage)
        destinationQueue := some (queueKey machineId (stageName stage) queueId) }
  | .queueRemoved stage queueId =>
      { kind := "queue-removed"
        stage := some (stageName stage)
        sourceQueue := some (queueKey machineId (stageName stage) queueId) }

structure Scenario
    (resourceCatalog : ResourceCatalog)
    (schema : MachineSchema)
    (language : OperationLanguage schema) where
  id : String
  gameId : String
  title : String
  summary : String
  initial : SimulatorState resourceCatalog schema language
  program : List (OperationProposal schema language)
  presentation : PresentationView

private def projectSteps
    (projection : Projection schema language)
    (evaluateGuard : GuardEvaluator resourceCatalog schema language) :
    Nat →
    SimulatorState resourceCatalog schema language →
    List (OperationProposal schema language) → List StepView
  | _, _, [] => []
  | index, state, proposal :: rest =>
      let definition := language.definition proposal.operation
      let beforeView := projectState projection state
      let operation := projection.operationName proposal.operation
      match applyOperation evaluateGuard state proposal with
      | .error issues =>
          { index
            operation
            trigger := triggerName definition.trigger
            status := "rejected"
            semanticStatus := "lean-rejected-no-successor"
            before := beforeView
            after := beforeView
            checks := issues.flatMap rejectedCheckViews
            effects := []
            issues := issues.map issueView } ::
          projectSteps projection evaluateGuard (index + 1) state rest
      | .ok applied =>
          { index
            operation
            trigger := triggerName definition.trigger
            status := "accepted"
            semanticStatus := "lean-proved-direct-replay"
            before := beforeView
            after := projectState projection applied.after
            checks := applied.checks.map acceptedCheckView
            effects := applied.effects.map (effectView projection.machineId)
            issues := [] } ::
          projectSteps projection evaluateGuard (index + 1) applied.after rest

def projectScenario
    (projection : Projection schema language)
    (evaluateGuard : GuardEvaluator resourceCatalog schema language)
    (scenario : Scenario resourceCatalog schema language) : ScenarioArtifact where
  schemaVersion := protocolVersion
  id := scenario.id
  gameId := scenario.gameId
  title := scenario.title
  summary := scenario.summary
  presentation := scenario.presentation
  provenance := leanProvenance
  initial := projectState projection scenario.initial
  steps := projectSteps projection evaluateGuard 1 scenario.initial scenario.program

/-! ## Application-owned state projection -/

/-- One already-assessed application transition rendered through the protocol. -/
structure ApplicationStepResult (State : Type) where
  after : State
  operation : String
  trigger : String
  status : String
  semanticStatus : String
  logicalTick : Option ExactNat := none
  eventSequences : List ExactNat := []
  intentIds : List ExactNat := []
  checks : List CheckView := []
  effects : List EffectView := []
  issues : List IssueView := []

/--
Generic adapter for a game-owned composite state. The visualizer neither knows
how components are stored nor how intents are executed.
-/
structure ApplicationScenario (State Intent : Type) where
  id : String
  gameId : String
  title : String
  summary : String
  initial : State
  program : List Intent
  presentation : PresentationView
  provenance : ProvenanceView
  projectState : State → StateView
  applyIntent : State → Intent → ApplicationStepResult State

private def projectApplicationSteps
    (projectState : State → StateView)
    (applyIntent : State → Intent → ApplicationStepResult State) :
    Nat → State → List Intent → List StepView
  | _, _, [] => []
  | index, state, intent :: rest =>
      let result := applyIntent state intent
      { index
        operation := result.operation
        trigger := result.trigger
        status := result.status
        semanticStatus := result.semanticStatus
        logicalTick := result.logicalTick
        eventSequences := result.eventSequences
        intentIds := result.intentIds
        before := projectState state
        after := projectState result.after
        checks := result.checks
        effects := result.effects
        issues := result.issues } ::
      projectApplicationSteps projectState applyIntent (index + 1)
        result.after rest

def projectApplicationScenario
    (scenario : ApplicationScenario State Intent) : ScenarioArtifact where
  schemaVersion := protocolVersion
  id := scenario.id
  gameId := scenario.gameId
  title := scenario.title
  summary := scenario.summary
  presentation := scenario.presentation
  provenance := scenario.provenance
  initial := scenario.projectState scenario.initial
  steps := projectApplicationSteps scenario.projectState scenario.applyIntent 1
    scenario.initial scenario.program

/-!
## Shared command-graph assembly

Games retain their vocabulary and receipt projection, while this adapter owns
the protocol-level graph assembly. A game cannot accidentally choose a root or
edge endpoint different from the proof-backed values passed to these callbacks.
-/

def projectCommandGraph
    (actor root : String)
    (nodes : List Node)
    (resolutions : List Resolution)
    (projectNode : Node → CommandNodeView)
    (projectResolution : Resolution → CommandResolutionView) : CommandGraphView where
  actor
  root
  nodes := nodes.map projectNode
  resolutions := resolutions.map projectResolution

end Maquina.Visualization
