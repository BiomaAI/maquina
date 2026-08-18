import Maquina.CustodyTransformation
import Maquina.Operation
import Maquina.Session

/-!
# Maquina Generic Simulator

The simulator interprets generic operation effects. It has no knowledge of
game modes, process names, participant labels, or resource meanings.
-/

namespace Maquina

/-- One stable, game-authored explanation for a failed operation guard. -/
structure GuardIssue where
  condition : String
  code : String
  detail : String
  deriving DecidableEq, Repr

/-- Inspectable positive evidence emitted when a declared guard holds. -/
structure GuardEvidence where
  condition : String
  detail : String
  deriving DecidableEq, Repr

structure SimulatorState
    (resourceCatalog : ResourceCatalog)
    (schema : MachineSchema)
    (language : OperationLanguage schema) where
  world : WorldState resourceCatalog
  mode : language.Mode
  machine : Machine schema
  custody : MachineCustody machine.inventory
  custodyBacked : MachineCustody.Backed world custody
  activeCustodyHeld : machine.ActiveDependenciesSatisfy
    (ActiveCustodyDependency.HeldBy custody)
  nextProcessId : Nat

namespace SimulatorState

/-- Every dependency carried by active work resolves to an open covering position. -/
theorem activeDependency_held
    {state : SimulatorState resourceCatalog schema language}
    {queue : MachineProcessingQueue schema}
    {dependency : ActiveCustodyDependency schema.Label}
    (queueMem : queue ∈ state.machine.processingQueues)
    (dependencyMem : dependency ∈ queue.activeCustodyDependencies) :
    dependency.HeldBy state.custody :=
  state.activeCustodyHeld queue queueMem dependency dependencyMem

/-- Any dependency carried by active work marks its position as in use. -/
theorem activeDependency_positionInUse
    {state : SimulatorState resourceCatalog schema language}
    {queue : MachineProcessingQueue schema}
    {dependency : ActiveCustodyDependency schema.Label}
    (queueMem : queue ∈ state.machine.processingQueues)
    (dependencyMem : dependency ∈ queue.activeCustodyDependencies) :
    state.machine.CustodyPositionInUse dependency.positionId :=
  state.machine.positionId_mem_of_activeDependency queueMem dependencyMem

end SimulatorState

/--
A game declares the proposition denoted by each guard, its exhaustive issue
list on an exact state, and human-readable evidence for acceptance. The
equivalence field connects the computational explanation to the proposition,
so generic acceptance carries proof of the game-declared condition rather
than merely remembering an opaque boolean.
-/
structure GuardEvaluator
    (resourceCatalog : ResourceCatalog)
    (schema : MachineSchema)
    (language : OperationLanguage schema) where
  condition :
    language.Guard → SimulatorState resourceCatalog schema language → Prop
  issues :
    language.Guard → SimulatorState resourceCatalog schema language →
      List GuardIssue
  evidence :
    language.Guard → SimulatorState resourceCatalog schema language →
      GuardEvidence
  issuesEmptyIff : ∀ guard state,
    issues guard state = [] ↔ condition guard state

/-- Canonical exhaustive issues for all guards, in declaration order. -/
def operationGuardIssues
    (evaluator : GuardEvaluator resourceCatalog schema language)
    (state : SimulatorState resourceCatalog schema language)
    (guards : List language.Guard) : List GuardIssue :=
  guards.flatMap fun guard => evaluator.issues guard state

/-- Proof that every guard declared by an operation holds in the exact state. -/
structure AcceptedOperationGuards
    (evaluator : GuardEvaluator resourceCatalog schema language)
    (state : SimulatorState resourceCatalog schema language)
    (guards : List language.Guard) : Prop where
  issuesEmpty : operationGuardIssues evaluator state guards = []

namespace AcceptedOperationGuards

/-- Proof-carrying guard acceptance covers every declared guard. -/
theorem holds
    {evaluator : GuardEvaluator resourceCatalog schema language}
    {state : SimulatorState resourceCatalog schema language}
    {guards : List language.Guard}
    (accepted : AcceptedOperationGuards evaluator state guards)
    (guard : language.Guard)
    (guardMem : guard ∈ guards) :
    evaluator.condition guard state := by
  have issueListEmpty : evaluator.issues guard state = [] :=
    (List.flatMap_eq_nil_iff.mp accepted.issuesEmpty) guard guardMem
  exact (evaluator.issuesEmptyIff guard state).mp issueListEmpty

end AcceptedOperationGuards

/-- Exhaustive assessment of every declared operation guard. -/
inductive OperationGuardAssessment
    (evaluator : GuardEvaluator resourceCatalog schema language)
    (state : SimulatorState resourceCatalog schema language)
    (guards : List language.Guard) where
  | accepted
      (witness : AcceptedOperationGuards evaluator state guards)
      (evidence : List GuardEvidence)
  | rejected
      (issues : List GuardIssue)
      (issuesExact : issues = operationGuardIssues evaluator state guards)
      (nonempty : issues ≠ [])

def assessOperationGuards
    (evaluator : GuardEvaluator resourceCatalog schema language)
    (state : SimulatorState resourceCatalog schema language)
    (guards : List language.Guard) :
    OperationGuardAssessment evaluator state guards :=
  let issues := operationGuardIssues evaluator state guards
  if empty : issues = [] then
    .accepted ⟨empty⟩ (guards.map fun guard => evaluator.evidence guard state)
  else
    .rejected issues rfl empty

inductive SimulatorIssue where
  | wrongMode
  | guardRejected (issues : List GuardIssue)
  | missingProcessKind
  | missingProcessBindings
  | pendingProcessAlreadyExists
  | pendingProcessMissing
  | pendingProcessNotEnqueued
  | consumedInputsMissing
  | reservedInputsAlreadyExist
  | reservedInputsMissing
  | queueBindingMissing (stage : QueueStage)
  | queueMissing (stage : QueueStage) (id : Nat)
  | queueRejected (stage : QueueStage) (issues : List Queue.QueueIssue)
  | queueRejectsProcess (stage : QueueStage)
  | processKindMismatch
  | possessionRejected (failures : List PossessionFailure)
  | transferRejected (issues : List TransferIssue)
  | transformationRejected (issues : List InventoryDeltaIssue)
  | insufficientWork (required actual : Nat)
  | recipientBindingMissing
  | recipientAlreadyBound
  | custodyBindingMissing
  | activeCustodyRejected (failures : List ActiveCustodyFailure)
  | custodyPositionMissing (id : Nat)
  | custodyPositionInUse (id : Nat)
  | outputLabelMissing
  | outputRecipientMissing
  | machineQueueLimit
  | queueNotEmpty (stage : QueueStage)
  deriving DecidableEq, Repr

inductive SimulatorEffectReceipt where
  | transfer (receipt : TransferReceipt)
  | transformation (receipt : InventoryDeltaReceipt)
  | enqueued (queueId ticket processId : Nat)
  | dispatched (inputQueueId processingQueueId processId : Nat)
  | advanced (queueId processId before after : Nat)
  | completed (processingQueueId : Nat) (outputQueueId : Option Nat)
      (processId : Nat)
  | recipientBound (account : AccountId)
  | collected (queueId processId : Nat)
  | allocationCollected (queueId processId remaining : Nat)
  | custodyOpened (positionId : Nat)
  | custodyClosed (positionId : Nat)
  | custodyDependenciesBound (processId : Nat) (positionIds : List Nat)
  | custodyDependenciesReleased (processId : Nat) (positionIds : List Nat)
  | reservationsReleased (processId : Nat)
  | cancelled (stage : QueueStage) (queueId processId : Nat)
      (disposition : CancellationDisposition)
  | queueAdded (stage : QueueStage) (queueId : Nat)
  | queueRemoved (stage : QueueStage) (queueId : Nat)
  deriving Repr

/-- Non-mutating evidence gathered before operation effects are interpreted. -/
inductive OperationCheckReceipt where
  | guard (evidence : GuardEvidence)
  | possession (requirementIndex : Nat) (receipt : PossessionReceipt)
  deriving Repr

inductive WorldEffectReceipt where
  | transfer (receipt : TransferReceipt)
  | transformation (receipt : InventoryDeltaReceipt)
  deriving Repr

def replayWorldEffectReceipts
    (receipts : List WorldEffectReceipt)
    (holdings : List (Holding AccountId)) : List (Holding AccountId) :=
  receipts.foldl (fun current receipt =>
    match receipt with
    | .transfer moved => replayReceipt moved current
    | .transformation changed => replayInventoryDeltaReceipt changed current)
    holdings

theorem replayWorldEffectReceipts_append
    (earlier later : List WorldEffectReceipt)
    (holdings : List (Holding AccountId)) :
    replayWorldEffectReceipts (earlier ++ later) holdings =
      replayWorldEffectReceipts later
        (replayWorldEffectReceipts earlier holdings) := by
  simp [replayWorldEffectReceipts, List.foldl_append]

theorem replayWorldEffectReceipts_transformations
    (receipts : List InventoryDeltaReceipt)
    (holdings : List (Holding AccountId)) :
    replayWorldEffectReceipts
        (receipts.map WorldEffectReceipt.transformation) holdings =
      replayInventoryProgram receipts holdings := by
  induction receipts generalizing holdings with
  | nil => rfl
  | cons receipt rest ih =>
      change replayWorldEffectReceipts
          (rest.map WorldEffectReceipt.transformation)
          (replayInventoryDeltaReceipt receipt holdings) =
        replayInventoryProgram rest
          (replayInventoryDeltaReceipt receipt holdings)
      exact ih _

structure OperationReceipt
    (schema : MachineSchema)
    (language : OperationLanguage schema) where
  proposal : OperationProposal schema language
  checks : List OperationCheckReceipt
  effects : List SimulatorEffectReceipt

structure AppliedOperation
    {resourceCatalog : ResourceCatalog}
    {schema : MachineSchema}
    {language : OperationLanguage schema}
    (before : SimulatorState resourceCatalog schema language)
    (proposal : OperationProposal schema language) where
  after : SimulatorState resourceCatalog schema language
  checks : List OperationCheckReceipt
  effects : List SimulatorEffectReceipt
  worldEffects : List WorldEffectReceipt
  worldReplayExact :
    replayWorldEffectReceipts worldEffects before.world.holdings =
      after.world.holdings

namespace AppliedOperation

def receipt
    {resourceCatalog : ResourceCatalog}
    {schema : MachineSchema}
    {language : OperationLanguage schema}
    {before : SimulatorState resourceCatalog schema language}
    {proposal : OperationProposal schema language}
    (applied : AppliedOperation before proposal) : OperationReceipt schema language :=
  { proposal, checks := applied.checks, effects := applied.effects }

end AppliedOperation

/-- Serializable computational data reconstructed without proof fields. -/
structure SimulatorData
    (schema : MachineSchema)
    (language : OperationLanguage schema) where
  holdings : List (Holding AccountId)
  mode : language.Mode
  machine : Machine schema
  custody : MachineCustody machine.inventory
  nextProcessId : Nat

namespace SimulatorData

def ofState
    {resourceCatalog : ResourceCatalog}
    (state : SimulatorState resourceCatalog schema language) :
    SimulatorData schema language where
  holdings := state.world.holdings
  mode := state.mode
  machine := state.machine
  custody := state.custody
  nextProcessId := state.nextProcessId

end SimulatorData

/-- World receipts plus exact non-world patches; no proposal is retained. -/
structure DirectEffectReceipt
    (schema : MachineSchema)
    (language : OperationLanguage schema) where
  effects : List SimulatorEffectReceipt
  worldEffects : List WorldEffectReceipt
  modeAfter : language.Mode
  machineAfter : Machine schema
  custodyAfter : MachineCustody machineAfter.inventory
  nextProcessIdAfter : Nat

def replayDirectEffectReceipt
    (before : SimulatorData schema language)
    (receipt : DirectEffectReceipt schema language) :
    SimulatorData schema language where
  holdings := replayWorldEffectReceipts receipt.worldEffects before.holdings
  mode := receipt.modeAfter
  machine := receipt.machineAfter
  custody := receipt.custodyAfter
  nextProcessId := receipt.nextProcessIdAfter

def replayDirectEffectReceipts
    (before : SimulatorData schema language) :
    List (DirectEffectReceipt schema language) → SimulatorData schema language
  | [] => before
  | receipt :: rest =>
      replayDirectEffectReceipts (replayDirectEffectReceipt before receipt) rest

def AppliedOperation.directReceipt
    {resourceCatalog : ResourceCatalog}
    {schema : MachineSchema}
    {language : OperationLanguage schema}
    {before : SimulatorState resourceCatalog schema language}
    {proposal : OperationProposal schema language}
    (applied : AppliedOperation before proposal) :
    DirectEffectReceipt schema language where
  effects := applied.effects
  worldEffects := applied.worldEffects
  modeAfter := applied.after.mode
  machineAfter := applied.after.machine
  custodyAfter := applied.after.custody
  nextProcessIdAfter := applied.after.nextProcessId

theorem AppliedOperation.replayDirect_exact
    {resourceCatalog : ResourceCatalog}
    {schema : MachineSchema}
    {language : OperationLanguage schema}
    {before : SimulatorState resourceCatalog schema language}
    {proposal : OperationProposal schema language}
    (applied : AppliedOperation before proposal) :
    replayDirectEffectReceipt (SimulatorData.ofState before)
        applied.directReceipt =
      SimulatorData.ofState applied.after := by
  cases applied with
  | mk after checks effects worldEffects worldReplayExact =>
      simp only [replayDirectEffectReceipt, directReceipt, SimulatorData.ofState]
      rw [worldReplayExact]

private structure OperationRequirementChecks where
  receipts : List PossessionReceipt
  failures : List PossessionFailure

/-- Evaluate every requirement independently against the unchanged world. -/
private def operationRequirementChecksFrom
    {resourceCatalog : ResourceCatalog}
    {Label : Type}
    (world : WorldState resourceCatalog)
    (bindings : PossessionBindings Label) :
    Nat → List (PossessionPort Label) → OperationRequirementChecks
  | _, [] => { receipts := [], failures := [] }
  | requirementIndex, port :: rest =>
      let requirement : PossessionRequirement :=
        { account := bindings.resolve port.label
          basket := port.basket }
      let current := assessPossession world requirement
      let suffix :=
        operationRequirementChecksFrom world bindings (requirementIndex + 1) rest
      match current with
      | .accepted accepted =>
          { receipts := possessionReceipt accepted :: suffix.receipts
            failures := suffix.failures }
      | .rejected issues _ _ =>
          { receipts := suffix.receipts
            failures :=
              { requirementIndex, account := requirement.account, issues } ::
                suffix.failures }

/-- Canonical complete requirement failures, preserving declaration order. -/
def operationRequirementFailures
    {resourceCatalog : ResourceCatalog}
    {Label : Type}
    (world : WorldState resourceCatalog)
    (bindings : PossessionBindings Label)
    (requirements : List (PossessionPort Label)) : List PossessionFailure :=
  (operationRequirementChecksFrom world bindings 0 requirements).failures

def assessOperationRequirements
    {resourceCatalog : ResourceCatalog}
    {Label : Type}
    (world : WorldState resourceCatalog)
    (bindings : PossessionBindings Label)
    (requirements : List (PossessionPort Label)) :
    Except (List PossessionFailure) (List PossessionReceipt) :=
  let checks := operationRequirementChecksFrom world bindings 0 requirements
  if _empty : checks.failures = [] then .ok checks.receipts
  else .error checks.failures

/-- Every rejected requirement assessment returns the exact canonical failures. -/
theorem assessOperationRequirements_rejected_exact
    {resourceCatalog : ResourceCatalog}
    {Label : Type}
    (world : WorldState resourceCatalog)
    (bindings : PossessionBindings Label)
    (requirements : List (PossessionPort Label))
    (failures : List PossessionFailure)
    (rejected :
      assessOperationRequirements world bindings requirements = .error failures) :
    failures = operationRequirementFailures world bindings requirements := by
  simp only [assessOperationRequirements] at rejected
  split at rejected
  · contradiction
  · exact (Except.error.inj rejected).symm

/-- A rejected requirement assessment always explains at least one failure. -/
theorem assessOperationRequirements_rejected_nonempty
    {resourceCatalog : ResourceCatalog}
    {Label : Type}
    (world : WorldState resourceCatalog)
    (bindings : PossessionBindings Label)
    (requirements : List (PossessionPort Label))
    (failures : List PossessionFailure)
    (rejected :
      assessOperationRequirements world bindings requirements = .error failures) :
    failures ≠ [] := by
  simp only [assessOperationRequirements] at rejected
  split at rejected
  · contradiction
  · rename_i notEmpty
    exact (Except.error.inj rejected) ▸ notEmpty

private theorem operationRequirementChecksFrom_complete
    {resourceCatalog : ResourceCatalog}
    {Label : Type}
    (world : WorldState resourceCatalog)
    (bindings : PossessionBindings Label)
    (start : Nat)
    (earlier later : List (PossessionPort Label))
    (port : PossessionPort Label)
    (issues : List PossessionIssue)
    (issuesExact :
      possessionIssues world
        { account := bindings.resolve port.label, basket := port.basket } = issues)
    (nonempty : issues ≠ []) :
    { requirementIndex := start + earlier.length
      account := bindings.resolve port.label
      issues } ∈
      (operationRequirementChecksFrom world bindings start
        (earlier ++ port :: later)).failures := by
  induction earlier generalizing start with
  | nil =>
      simp [operationRequirementChecksFrom, assessPossession, issuesExact,
        nonempty]
  | cons head rest ih =>
      cases current : assessPossession world
          { account := bindings.resolve head.label, basket := head.basket } <;>
        simpa [operationRequirementChecksFrom, current, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm] using ih (start + 1)

/-- Every independently failing declared requirement occurs in the report. -/
theorem operationRequirementFailures_complete
    {resourceCatalog : ResourceCatalog}
    {Label : Type}
    (world : WorldState resourceCatalog)
    (bindings : PossessionBindings Label)
    (earlier later : List (PossessionPort Label))
    (port : PossessionPort Label)
    (issues : List PossessionIssue)
    (issuesExact :
      possessionIssues world
        { account := bindings.resolve port.label, basket := port.basket } = issues)
    (nonempty : issues ≠ []) :
    { requirementIndex := earlier.length
      account := bindings.resolve port.label
      issues } ∈
      operationRequirementFailures world bindings (earlier ++ port :: later) := by
  simpa [operationRequirementFailures] using
    operationRequirementChecksFrom_complete world bindings 0 earlier later port
      issues issuesExact nonempty

private structure ReservationRun
    (resourceCatalog : ResourceCatalog)
    {Label : Type}
    (bindings : ProcessBindings Label)
    (use : ProcessInputUse)
    (ports : List (ProcessPort Label))
    {inventory : AccountId}
    (custody : MachineCustody inventory)
    (before : WorldState resourceCatalog) where
  world : WorldState resourceCatalog
  backed : MachineCustody.Backed world custody
  reservations : List (Reservation Label)
  receipts : List SimulatorEffectReceipt
  worldEffects : List WorldEffectReceipt
  replayExact :
    replayWorldEffectReceipts worldEffects before.holdings = world.holdings
  usesExact : ∀ reservation, reservation ∈ reservations → reservation.use = use
  sourcesExact : ∀ reservation, reservation ∈ reservations →
    reservation.source = bindings.source reservation.label
  custodyExact : ∀ reservation, reservation ∈ reservations →
    reservation.custody = bindings.custody reservation.label
  portsExact : ∀ reservation, reservation ∈ reservations →
    ∃ port ∈ ports,
      reservation.label = port.label ∧ reservation.basket = port.basket
  portsCovered : ∀ port, port ∈ ports →
    ∃ reservation ∈ reservations,
      reservation.use = use ∧
      reservation.label = port.label ∧
      reservation.basket = port.basket

private def reservePorts
    {resourceCatalog : ResourceCatalog}
    {Label : Type}
    {inventory : AccountId}
    (bindings : ProcessBindings Label)
    (use : ProcessInputUse)
    (custody : MachineCustody inventory) :
    (world : WorldState resourceCatalog) →
    MachineCustody.Backed world custody →
    (ports : List (ProcessPort Label)) →
      Except SimulatorIssue
        (ReservationRun resourceCatalog bindings use ports custody world)
  | world, backed, [] =>
      .ok
        { world
          backed
          reservations := []
          receipts := []
          worldEffects := []
          replayExact := rfl
          usesExact := by simp
          sourcesExact := by simp
          custodyExact := by simp
          portsExact := by simp
          portsCovered := by simp }
  | world, backed, port :: rest =>
      let proposal : Transfer :=
        { source := bindings.source port.label
          destination := bindings.custody port.label
          basket := port.basket }
      match MachineCustody.assessCustodyTransfer world custody proposal with
      | .rejected issues _ _ => .error (.transferRejected issues)
      | .accepted accepted =>
          let after := applyTransferState accepted.transferAccepted
          let afterBacked := backed.applyCustodyTransfer accepted
          match reservePorts bindings use custody after afterBacked rest with
          | .error issue => .error issue
          | .ok suffix =>
              .ok
                { world := suffix.world
                  backed := suffix.backed
                  reservations :=
                    Reservation.ofAccepted use port.label accepted.transferAccepted ::
                      suffix.reservations
                  receipts :=
                    .transfer (transferReceipt accepted.transferAccepted) ::
                      suffix.receipts
                  worldEffects :=
                    .transfer (transferReceipt accepted.transferAccepted) ::
                      suffix.worldEffects
                  replayExact := by
                    change replayWorldEffectReceipts suffix.worldEffects
                        (replayReceipt
                          (transferReceipt accepted.transferAccepted)
                          world.holdings) = suffix.world.holdings
                    rw [replay_transferReceipt accepted.transferAccepted]
                    exact suffix.replayExact
                  usesExact := by
                    intro reservation reservationMem
                    simp only [List.mem_cons] at reservationMem
                    rcases reservationMem with isHead | inRest
                    · subst reservation
                      rfl
                    · exact suffix.usesExact reservation inRest
                  sourcesExact := by
                    intro reservation reservationMem
                    simp only [List.mem_cons] at reservationMem
                    rcases reservationMem with isHead | inRest
                    · subst reservation
                      exact Reservation.ofAccepted_source use port.label
                        accepted.transferAccepted
                    · exact suffix.sourcesExact reservation inRest
                  custodyExact := by
                    intro reservation reservationMem
                    simp only [List.mem_cons] at reservationMem
                    rcases reservationMem with isHead | inRest
                    · subst reservation
                      exact Reservation.ofAccepted_custody use port.label
                        accepted.transferAccepted
                    · exact suffix.custodyExact reservation inRest
                  portsExact := by
                    intro reservation reservationMem
                    simp only [List.mem_cons] at reservationMem
                    rcases reservationMem with isHead | inRest
                    · subst reservation
                      exact ⟨port, by simp, rfl, rfl⟩
                    · obtain ⟨matched, matchedMem, labelEq, basketEq⟩ :=
                        suffix.portsExact reservation inRest
                      exact ⟨matched, by simp [matchedMem], labelEq, basketEq⟩
                  portsCovered := by
                    intro queried queriedMem
                    simp only [List.mem_cons] at queriedMem
                    rcases queriedMem with isHead | inRest
                    · subst queried
                      exact ⟨Reservation.ofAccepted use port.label
                        accepted.transferAccepted,
                        by simp, rfl, rfl, rfl⟩
                    · obtain ⟨reservation, reservationMem, useEq, labelEq,
                        basketEq⟩ := suffix.portsCovered queried inRest
                      exact ⟨reservation, by simp [reservationMem], useEq,
                        labelEq, basketEq⟩ }

private structure ProcessReservationRun
    (resourceCatalog : ResourceCatalog)
    {Label : Type}
    (process : Process Label)
    (bindings : ProcessBindings Label)
    {inventory : AccountId}
    (custody : MachineCustody inventory)
    (before : WorldState resourceCatalog) where
  world : WorldState resourceCatalog
  backed : MachineCustody.Backed world custody
  reservations : List (Reservation Label)
  receipts : List SimulatorEffectReceipt
  worldEffects : List WorldEffectReceipt
  replayExact :
    replayWorldEffectReceipts worldEffects before.holdings = world.holdings
  reservationsValid : ReservationsValid process bindings reservations
  consumedComplete : ConsumedInputStatus process reservations
  reservedComplete : ReservedInputStatus process reservations

private theorem ReservationRun.consumedValid
    {resourceCatalog : ResourceCatalog}
    {Label : Type}
    {process : Process Label}
    {bindings : ProcessBindings Label}
    {inventory : AccountId}
    {custody : MachineCustody inventory}
    {before : WorldState resourceCatalog}
    (run : ReservationRun resourceCatalog bindings .consumed process.consumed
      custody before) :
    ReservationsValid process bindings run.reservations := by
  intro reservation reservationMem
  have useEq := run.usesExact reservation reservationMem
  have sourceEq := run.sourcesExact reservation reservationMem
  have custodyEq := run.custodyExact reservation reservationMem
  obtain ⟨port, portMem, labelEq, basketEq⟩ :=
    run.portsExact reservation reservationMem
  exact ⟨sourceEq, custodyEq, by
    rw [useEq]
    exact ⟨port, portMem, labelEq, basketEq⟩⟩

private theorem ReservationRun.reservedValid
    {resourceCatalog : ResourceCatalog}
    {Label : Type}
    {process : Process Label}
    {bindings : ProcessBindings Label}
    {inventory : AccountId}
    {custody : MachineCustody inventory}
    {before : WorldState resourceCatalog}
    (run : ReservationRun resourceCatalog bindings .reserved process.reserved
      custody before) :
    ReservationsValid process bindings run.reservations := by
  intro reservation reservationMem
  have useEq := run.usesExact reservation reservationMem
  have sourceEq := run.sourcesExact reservation reservationMem
  have custodyEq := run.custodyExact reservation reservationMem
  obtain ⟨port, portMem, labelEq, basketEq⟩ :=
    run.portsExact reservation reservationMem
  exact ⟨sourceEq, custodyEq, by
    rw [useEq]
    exact ⟨port, portMem, labelEq, basketEq⟩⟩

private def reserveConsumedProcess
    {resourceCatalog : ResourceCatalog}
    {Label : Type}
    {inventory : AccountId}
    (custody : MachineCustody inventory)
    (world : WorldState resourceCatalog)
    (backed : MachineCustody.Backed world custody)
    (process : Process Label)
    (bindings : ProcessBindings Label) :
    Except SimulatorIssue
      (ProcessReservationRun resourceCatalog process bindings custody world) :=
  match reservePorts bindings .consumed custody world backed process.consumed with
  | .error issue => .error issue
  | .ok consumed =>
      .ok
        { world := consumed.world
          backed := consumed.backed
          reservations := consumed.reservations
          receipts := consumed.receipts
          worldEffects := consumed.worldEffects
          replayExact := consumed.replayExact
          reservationsValid := consumed.consumedValid
          consumedComplete := .complete (by
            intro port portMem
            exact consumed.portsCovered port portMem)
          reservedComplete := .missing }

private def reserveReservedProcess
    {resourceCatalog : ResourceCatalog}
    {Label : Type}
    {inventory : AccountId}
    (custody : MachineCustody inventory)
    (world : WorldState resourceCatalog)
    (backed : MachineCustody.Backed world custody)
    (process : Process Label)
    (bindings : ProcessBindings Label) :
    Except SimulatorIssue
      (ProcessReservationRun resourceCatalog process bindings custody world) :=
  match reservePorts bindings .reserved custody world backed process.reserved with
  | .error issue => .error issue
  | .ok reserved =>
      .ok
        { world := reserved.world
          backed := reserved.backed
          reservations := reserved.reservations
          receipts := reserved.receipts
          worldEffects := reserved.worldEffects
          replayExact := reserved.replayExact
          reservationsValid := reserved.reservedValid
          consumedComplete := .missing
          reservedComplete := .complete (by
            intro port portMem
            exact reserved.portsCovered port portMem) }

def completionDeltas
    {schema : MachineSchema}
    (process : QueuedProcess schema) : List InventoryDelta :=
  let consumed := process.reservations.filterMap fun reservation =>
    if reservation.use = .consumed then
      some (reservation.basket.entries.map fun entry =>
        InventoryDelta.debit reservation.custody entry)
    else none
  let produced := (schema.process process.processKind).outputs.map fun port =>
    port.basket.entries.map fun entry =>
      InventoryDelta.credit (process.bindings.custody port.label) entry
  consumed.flatten ++ produced.flatten

/-- Every staged consumed entry has one exact debit in the completion plan. -/
theorem completionDeltas_consumes
    {schema : MachineSchema}
    (process : QueuedProcess schema)
    (reservation : Reservation schema.Label)
    (reservationMem : reservation ∈ process.reservations)
    (consumed : reservation.use = .consumed)
    (entry : BasketEntry)
    (entryMem : entry ∈ reservation.basket.entries) :
    .debit reservation.custody entry ∈ completionDeltas process := by
  apply List.mem_append_left
  apply List.mem_flatten.mpr
  refine ⟨reservation.basket.entries.map fun item =>
    InventoryDelta.debit reservation.custody item, ?_, ?_⟩
  · apply List.mem_filterMap.mpr
    exact ⟨reservation, reservationMem, by simp [consumed]⟩
  · exact List.mem_map.mpr ⟨entry, entryMem, rfl⟩

/-- Every canonical output entry has one exact credit in the completion plan. -/
theorem completionDeltas_produces
    {schema : MachineSchema}
    (process : QueuedProcess schema)
    (port : ProcessPort schema.Label)
    (portMem : port ∈ (schema.process process.processKind).outputs)
    (entry : BasketEntry)
    (entryMem : entry ∈ port.basket.entries) :
    .credit (process.bindings.custody port.label) entry ∈
      completionDeltas process := by
  apply List.mem_append_right
  apply List.mem_flatten.mpr
  refine ⟨port.basket.entries.map fun item =>
    InventoryDelta.credit (process.bindings.custody port.label) item, ?_, ?_⟩
  · exact List.mem_map.mpr ⟨port, portMem, rfl⟩
  · exact List.mem_map.mpr ⟨entry, entryMem, rfl⟩

/-- One output allocation is either already at its recipient or transferred exactly. -/
def AllocationDelivered
    (allocation : OutputAllocation Label)
    (receipts : List SimulatorEffectReceipt) : Prop :=
  ∃ recipient, allocation.recipient = some recipient ∧
    (allocation.custody = recipient ∨
      ∃ receipt, SimulatorEffectReceipt.transfer receipt ∈ receipts ∧
        receipt.source = allocation.custody ∧
        receipt.destination = recipient ∧
        receipt.lines.map TransferReceiptLine.toEntry = allocation.basket.entries)

def AllocationsDelivered
    (allocations : List (OutputAllocation Label))
    (receipts : List SimulatorEffectReceipt) : Prop :=
  ∀ allocation ∈ allocations, AllocationDelivered allocation receipts

def AllocationReceiptMatches
    (receipt : TransferReceipt)
    (allocation : OutputAllocation Label) : Prop :=
  ∃ recipient, allocation.recipient = some recipient ∧
    receipt.source = allocation.custody ∧
    receipt.destination = recipient ∧
    receipt.lines.map TransferReceiptLine.toEntry = allocation.basket.entries

def AllocationReceiptsSound
    (allocations : List (OutputAllocation Label))
    (receipts : List SimulatorEffectReceipt) : Prop :=
  ∀ receipt, SimulatorEffectReceipt.transfer receipt ∈ receipts →
    ∃ allocation ∈ allocations, AllocationReceiptMatches receipt allocation

structure AllocationDelivery
    (resourceCatalog : ResourceCatalog)
    {inventory : AccountId}
    (custody : MachineCustody inventory)
    (before : WorldState resourceCatalog)
    {Label : Type}
    (allocations : List (OutputAllocation Label)) where
  world : WorldState resourceCatalog
  backed : MachineCustody.Backed world custody
  receipts : List SimulatorEffectReceipt
  worldEffects : List WorldEffectReceipt
  replayExact :
    replayWorldEffectReceipts worldEffects before.holdings = world.holdings
  delivered : AllocationsDelivered allocations receipts
  sound : AllocationReceiptsSound allocations receipts

/-- One transfer receipt reverses one temporary reservation exactly. -/
def ReturnsReservation
    (receipt : TransferReceipt)
    (reservation : Reservation Label) : Prop :=
  receipt.source = reservation.custody ∧
  receipt.destination = reservation.source ∧
  receipt.lines.map TransferReceiptLine.toEntry = reservation.basket.entries

/-- Every temporary reservation has an exact reverse-transfer receipt. -/
def ReservedInputsReturned
    (reservations : List (Reservation Label))
    (receipts : List SimulatorEffectReceipt) : Prop :=
  ∀ reservation ∈ reservations,
    reservation.use = .reserved →
    ∃ receipt, SimulatorEffectReceipt.transfer receipt ∈ receipts ∧
      ReturnsReservation receipt reservation

/-- Every emitted return receipt belongs to a declared temporary reservation. -/
def ReservedReturnReceiptsSound
    (reservations : List (Reservation Label))
    (receipts : List SimulatorEffectReceipt) : Prop :=
  ∀ receipt, SimulatorEffectReceipt.transfer receipt ∈ receipts →
    ∃ reservation ∈ reservations,
      reservation.use = .reserved ∧ ReturnsReservation receipt reservation

def Reservation.TouchesReturnKey
    (reservation : Reservation Label)
    (account : AccountId)
    (resourceId : ResourceId) : Prop :=
  reservation.use = .reserved ∧
  resourceId ∈ reservation.basket.entries.map BasketEntry.resourceId ∧
  (reservation.source = account ∨ reservation.custody = account)

private structure ReservationReturnRun
    (resourceCatalog : ResourceCatalog)
    {inventory : AccountId}
    (custody : MachineCustody inventory)
    (before : WorldState resourceCatalog)
    {Label : Type}
    (reservations : List (Reservation Label)) where
  world : WorldState resourceCatalog
  backed : MachineCustody.Backed world custody
  receipts : List SimulatorEffectReceipt
  worldEffects : List WorldEffectReceipt
  replayExact :
    replayWorldEffectReceipts worldEffects before.holdings = world.holdings
  returned : ReservedInputsReturned reservations receipts
  sound : ReservedReturnReceiptsSound reservations receipts
  balanceUntouched :
    ∀ account resourceId,
      (∀ reservation ∈ reservations,
        ¬reservation.TouchesReturnKey account resourceId) →
      (world.balance account resourceId).atoms =
        (before.balance account resourceId).atoms

private def returnReservations
    {resourceCatalog : ResourceCatalog}
    {Label : Type}
    {inventory : AccountId}
    (custody : MachineCustody inventory) :
    (world : WorldState resourceCatalog) →
    MachineCustody.Backed world custody →
    (reservations : List (Reservation Label)) →
      Except SimulatorIssue
        (ReservationReturnRun resourceCatalog custody world reservations)
  | world, backed, [] =>
      .ok
        { world, backed, receipts := []
          worldEffects := []
          replayExact := rfl
          returned := by simp [ReservedInputsReturned]
          sound := by simp [ReservedReturnReceiptsSound]
          balanceUntouched := by simp }
  | world, backed, reservation :: rest =>
      if reservedUse : reservation.use = .reserved then
        let proposal : Transfer :=
          { source := reservation.custody
            destination := reservation.source
            basket := reservation.basket }
        match MachineCustody.assessCustodyTransfer world custody proposal with
        | .rejected issues _ _ => .error (.transferRejected issues)
        | .accepted accepted =>
            let after := applyTransferState accepted.transferAccepted
            let afterBacked := backed.applyCustodyTransfer accepted
            match returnReservations custody after afterBacked rest with
            | .error issue => .error issue
            | .ok suffix =>
                .ok
                  { world := suffix.world
                    backed := suffix.backed
                    receipts :=
                      .transfer (transferReceipt accepted.transferAccepted) ::
                        suffix.receipts
                    worldEffects :=
                      .transfer (transferReceipt accepted.transferAccepted) ::
                        suffix.worldEffects
                    replayExact := by
                      change replayWorldEffectReceipts suffix.worldEffects
                          (replayReceipt
                            (transferReceipt accepted.transferAccepted)
                            world.holdings) = suffix.world.holdings
                      rw [replay_transferReceipt accepted.transferAccepted]
                      exact suffix.replayExact
                    returned := by
                      intro queried queriedMem queriedUse
                      simp only [List.mem_cons] at queriedMem
                      rcases queriedMem with isHead | inRest
                      · subst queried
                        let receipt := transferReceipt accepted.transferAccepted
                        exact ⟨receipt, List.mem_cons_self, rfl, rfl,
                          transferReceipt_entries accepted.transferAccepted⟩
                      · obtain ⟨receipt, receiptMem, exactReturn⟩ :=
                        suffix.returned queried inRest queriedUse
                        exact ⟨receipt, by simp [receiptMem], exactReturn⟩
                    sound := by
                      intro receipt receiptMem
                      simp only [List.mem_cons] at receiptMem
                      rcases receiptMem with isHead | inRest
                      · cases isHead
                        exact ⟨reservation, by simp, reservedUse, rfl, rfl,
                          transferReceipt_entries accepted.transferAccepted⟩
                      · obtain ⟨returnedReservation, returnedMem, returnedUse,
                          exactReturn⟩ := suffix.sound receipt inRest
                        exact ⟨returnedReservation, by simp [returnedMem],
                          returnedUse, exactReturn⟩
                    balanceUntouched := by
                      intro account resourceId untouched
                      have suffixUntouched := suffix.balanceUntouched account
                        resourceId (by
                          intro queried queriedMem
                          exact untouched queried (by simp [queriedMem]))
                      rw [suffixUntouched]
                      by_cases resourcePresent : resourceId ∈
                          reservation.basket.entries.map BasketEntry.resourceId
                      · have custodyDifferent : reservation.custody ≠ account := by
                          intro same
                          exact untouched reservation (by simp)
                            ⟨reservedUse, resourcePresent, Or.inr same⟩
                        have sourceDifferent : reservation.source ≠ account := by
                          intro same
                          exact untouched reservation (by simp)
                            ⟨reservedUse, resourcePresent, Or.inl same⟩
                        exact applyTransferState_otherAccount
                          accepted.transferAccepted account resourceId
                          custodyDifferent sourceDifferent
                      · exact applyTransferState_unlistedResource
                          accepted.transferAccepted account resourceId
                          resourcePresent }
      else
        match returnReservations custody world backed rest with
        | .error issue => .error issue
        | .ok suffix =>
            .ok
              { world := suffix.world
                backed := suffix.backed
                receipts := suffix.receipts
                worldEffects := suffix.worldEffects
                replayExact := suffix.replayExact
                returned := by
                  intro queried queriedMem queriedUse
                  simp only [List.mem_cons] at queriedMem
                  rcases queriedMem with isHead | inRest
                  · subst queried
                    exact False.elim (reservedUse queriedUse)
                  · exact suffix.returned queried inRest queriedUse
                sound := by
                  intro receipt receiptMem
                  obtain ⟨returnedReservation, returnedMem, returnedUse,
                      exactReturn⟩ := suffix.sound receipt receiptMem
                  exact ⟨returnedReservation, by simp [returnedMem],
                    returnedUse, exactReturn⟩
                balanceUntouched := by
                  intro account resourceId untouched
                  apply suffix.balanceUntouched
                  intro queried queriedMem
                  exact untouched queried (by simp [queriedMem]) }

private structure CancellationRun
    (resourceCatalog : ResourceCatalog)
    {inventory : AccountId}
    (custody : MachineCustody inventory)
    (before : WorldState resourceCatalog) where
  world : WorldState resourceCatalog
  backed : MachineCustody.Backed world custody
  receipts : List SimulatorEffectReceipt
  worldEffects : List WorldEffectReceipt
  replayExact :
    replayWorldEffectReceipts worldEffects before.holdings = world.holdings

private def returnEveryReservation
    {resourceCatalog : ResourceCatalog}
    {Label : Type}
    {inventory : AccountId}
    (custody : MachineCustody inventory) :
    (world : WorldState resourceCatalog) →
    MachineCustody.Backed world custody →
    List (Reservation Label) →
      Except SimulatorIssue (CancellationRun resourceCatalog custody world)
  | world, backed, [] =>
      .ok { world, backed, receipts := [], worldEffects := [], replayExact := rfl }
  | world, backed, reservation :: rest =>
      let proposal : Transfer :=
        { source := reservation.custody
          destination := reservation.source
          basket := reservation.basket }
      match MachineCustody.assessCustodyTransfer world custody proposal with
      | .rejected issues _ _ => .error (.transferRejected issues)
      | .accepted accepted =>
          let after := applyTransferState accepted.transferAccepted
          let afterBacked := backed.applyCustodyTransfer accepted
          match returnEveryReservation custody after afterBacked rest with
          | .error issue => .error issue
          | .ok suffix =>
              .ok
                { world := suffix.world
                  backed := suffix.backed
                  receipts :=
                    .transfer (transferReceipt accepted.transferAccepted) ::
                      suffix.receipts
                  worldEffects :=
                    .transfer (transferReceipt accepted.transferAccepted) ::
                      suffix.worldEffects
                  replayExact := by
                    change replayWorldEffectReceipts suffix.worldEffects
                        (replayReceipt
                          (transferReceipt accepted.transferAccepted)
                          world.holdings) = suffix.world.holdings
                    rw [replay_transferReceipt accepted.transferAccepted]
                    exact suffix.replayExact }

def cancellationDeltas
    {schema : MachineSchema}
    (process : QueuedProcess schema) : List InventoryDelta :=
  (process.reservations.filterMap fun reservation =>
    if reservation.use = .consumed then
      some (reservation.basket.entries.map fun entry =>
        InventoryDelta.debit reservation.custody entry)
    else none).flatten

private def cancelInventory
    {resourceCatalog : ResourceCatalog}
    {schema : MachineSchema}
    {inventory : AccountId}
    (custody : MachineCustody inventory)
    (world : WorldState resourceCatalog)
    (backed : MachineCustody.Backed world custody)
    (process : QueuedProcess schema) :
    CancellationDisposition →
      Except SimulatorIssue (CancellationRun resourceCatalog custody world)
  | .returnInputs =>
      returnEveryReservation custody world backed process.reservations
  | .consumeInputs =>
      match MachineCustody.applyCustodyInventoryProgram world custody backed
          (cancellationDeltas process) with
      | .error issues => .error (.transformationRejected issues)
      | .ok transformed =>
          match returnReservations custody transformed.after
              transformed.backedAfter process.reservations with
          | .error issue => .error issue
          | .ok returned =>
              .ok
                { world := returned.world
                  backed := returned.backed
                  receipts :=
                    transformed.receipts.map
                      SimulatorEffectReceipt.transformation ++ returned.receipts
                  worldEffects :=
                    transformed.receipts.map WorldEffectReceipt.transformation ++
                      returned.worldEffects
                  replayExact := by
                    rw [replayWorldEffectReceipts_append]
                    rw [replayWorldEffectReceipts_transformations,
                      transformed.replayExact]
                    exact returned.replayExact }

structure ProcessCompletion
    (resourceCatalog : ResourceCatalog)
    (initialWorld : WorldState resourceCatalog)
    {schema : MachineSchema}
    (before : QueuedProcess schema)
    {inventory : AccountId}
    (custody : MachineCustody inventory) where
  world : WorldState resourceCatalog
  backed : MachineCustody.Backed world custody
  process : QueuedProcess schema
  kindPreserved : process.processKind = before.processKind
  reservationsCleared : process.reservations = []
  transformations : List InventoryDeltaReceipt
  transformationsExact :
    transformations.map InventoryDeltaReceipt.delta = completionDeltas before
  returnReceipts : List SimulatorEffectReceipt
  reservedInputsReturned :
    ReservedInputsReturned before.reservations returnReceipts
  returnReceiptsSound :
    ReservedReturnReceiptsSound before.reservations returnReceipts
  balanceUntouched :
    ∀ account resourceId,
      (∀ delta ∈ completionDeltas before,
        ¬delta.TouchesKey account resourceId) →
      (∀ reservation ∈ before.reservations,
        ¬reservation.TouchesReturnKey account resourceId) →
      (world.balance account resourceId).atoms =
        (initialWorld.balance account resourceId).atoms
  receipts : List SimulatorEffectReceipt
  worldEffects : List WorldEffectReceipt
  replayExact :
    replayWorldEffectReceipts worldEffects initialWorld.holdings = world.holdings

def completeInventory
    {resourceCatalog : ResourceCatalog}
    {schema : MachineSchema}
    {inventory : AccountId}
    (custody : MachineCustody inventory)
    (world : WorldState resourceCatalog)
    (backed : MachineCustody.Backed world custody)
    (process : QueuedProcess schema) :
    Except SimulatorIssue
      (ProcessCompletion resourceCatalog world process custody) :=
  match MachineCustody.applyCustodyInventoryProgram world custody backed
      (completionDeltas process) with
  | .error issues => .error (.transformationRejected issues)
  | .ok transformed =>
      match returnReservations custody transformed.after transformed.backedAfter
          process.reservations with
      | .error issue => .error issue
      | .ok returned =>
          .ok
            { world := returned.world
              backed := returned.backed
              process :=
                { process with
                  reservations := []
                  reservationsValid := by simp [ReservationsValid]
                  consumedInputsComplete := .missing
                  reservedInputsComplete := .missing }
              kindPreserved := rfl
              reservationsCleared := rfl
              transformations := transformed.receipts
              transformationsExact := transformed.receiptsExact
              returnReceipts := returned.receipts
              reservedInputsReturned := returned.returned
              returnReceiptsSound := returned.sound
              balanceUntouched := by
                intro account resourceId deltasUntouched returnsUntouched
                exact (returned.balanceUntouched account resourceId
                  returnsUntouched).trans
                    (transformed.balance_untouched account resourceId
                      deltasUntouched)
              receipts :=
                transformed.receipts.map SimulatorEffectReceipt.transformation ++
                  returned.receipts
              worldEffects :=
                transformed.receipts.map WorldEffectReceipt.transformation ++
                  returned.worldEffects
              replayExact := by
                rw [replayWorldEffectReceipts_append]
                rw [replayWorldEffectReceipts_transformations,
                  transformed.replayExact]
                exact returned.replayExact }

theorem ProcessCompletion.consumedReceipt
    {resourceCatalog : ResourceCatalog}
    {initialWorld : WorldState resourceCatalog}
    {schema : MachineSchema}
    {before : QueuedProcess schema}
    {inventory : AccountId}
    {custody : MachineCustody inventory}
    (completed : ProcessCompletion resourceCatalog initialWorld before custody)
    (reservation : Reservation schema.Label)
    (reservationMem : reservation ∈ before.reservations)
    (consumed : reservation.use = .consumed)
    (entry : BasketEntry)
    (entryMem : entry ∈ reservation.basket.entries) :
    ∃ receipt ∈ completed.transformations,
      receipt.delta = .debit reservation.custody entry := by
  have deltaMem := completionDeltas_consumes before reservation reservationMem
    consumed entry entryMem
  rw [← completed.transformationsExact] at deltaMem
  obtain ⟨receipt, receiptMem, receiptDelta⟩ := List.mem_map.mp deltaMem
  exact ⟨receipt, receiptMem, receiptDelta⟩

theorem ProcessCompletion.outputReceipt
    {resourceCatalog : ResourceCatalog}
    {initialWorld : WorldState resourceCatalog}
    {schema : MachineSchema}
    {before : QueuedProcess schema}
    {inventory : AccountId}
    {custody : MachineCustody inventory}
    (completed : ProcessCompletion resourceCatalog initialWorld before custody)
    (port : ProcessPort schema.Label)
    (portMem : port ∈ (schema.process before.processKind).outputs)
    (entry : BasketEntry)
    (entryMem : entry ∈ port.basket.entries) :
    ∃ receipt ∈ completed.transformations,
      receipt.delta = .credit (before.bindings.custody port.label) entry := by
  have deltaMem := completionDeltas_produces before port portMem entry entryMem
  rw [← completed.transformationsExact] at deltaMem
  obtain ⟨receipt, receiptMem, receiptDelta⟩ := List.mem_map.mp deltaMem
  exact ⟨receipt, receiptMem, receiptDelta⟩

/-- The complete resource contract carried by every successful completion. -/
structure CompletionContract
    {resourceCatalog : ResourceCatalog}
    {initialWorld : WorldState resourceCatalog}
    {schema : MachineSchema}
    {before : QueuedProcess schema}
    {inventory : AccountId}
    {custody : MachineCustody inventory}
    (completed : ProcessCompletion resourceCatalog initialWorld before custody) : Prop where
  consumed :
    ∀ reservation ∈ before.reservations,
      reservation.use = .consumed →
      ∀ entry ∈ reservation.basket.entries,
        ∃ receipt ∈ completed.transformations,
          receipt.delta = .debit reservation.custody entry
  returned : ReservedInputsReturned before.reservations completed.returnReceipts
  returnsSound :
    ReservedReturnReceiptsSound before.reservations completed.returnReceipts
  produced :
    ∀ port ∈ (schema.process before.processKind).outputs,
      ∀ entry ∈ port.basket.entries,
        ∃ receipt ∈ completed.transformations,
          receipt.delta = .credit (before.bindings.custody port.label) entry
  transformationsExact :
    completed.transformations.map InventoryDeltaReceipt.delta =
      completionDeltas before
  reservationsCleared : completed.process.reservations = []
  unrelatedBalances :
    ∀ account resourceId,
      (∀ delta ∈ completionDeltas before,
        ¬delta.TouchesKey account resourceId) →
      (∀ reservation ∈ before.reservations,
        ¬reservation.TouchesReturnKey account resourceId) →
      (completed.world.balance account resourceId).atoms =
        (initialWorld.balance account resourceId).atoms

theorem ProcessCompletion.contract
    {resourceCatalog : ResourceCatalog}
    {initialWorld : WorldState resourceCatalog}
    {schema : MachineSchema}
    {before : QueuedProcess schema}
    {inventory : AccountId}
    {custody : MachineCustody inventory}
    (completed : ProcessCompletion resourceCatalog initialWorld before custody) :
    CompletionContract completed where
  consumed := by
    intro reservation reservationMem consumed entry entryMem
    exact completed.consumedReceipt reservation reservationMem consumed entry entryMem
  returned := completed.reservedInputsReturned
  returnsSound := completed.returnReceiptsSound
  produced := by
    intro port portMem entry entryMem
    exact completed.outputReceipt port portMem entry entryMem
  transformationsExact := completed.transformationsExact
  reservationsCleared := completed.reservationsCleared
  unrelatedBalances := completed.balanceUntouched

private structure ReservationRelease
    (resourceCatalog : ResourceCatalog)
    (initialWorld : WorldState resourceCatalog)
    {schema : MachineSchema}
    (before : QueuedProcess schema)
    {inventory : AccountId}
    (custody : MachineCustody inventory) where
  world : WorldState resourceCatalog
  backed : MachineCustody.Backed world custody
  process : QueuedProcess schema
  kindPreserved : process.processKind = before.processKind
  consumedComplete :
    ConsumedInputsComplete (schema.process process.processKind) process.reservations
  receipts : List SimulatorEffectReceipt
  worldEffects : List WorldEffectReceipt
  replayExact :
    replayWorldEffectReceipts worldEffects initialWorld.holdings = world.holdings

private def releaseQueuedReservations
    {resourceCatalog : ResourceCatalog}
    {schema : MachineSchema}
    {inventory : AccountId}
    (custody : MachineCustody inventory)
    (world : WorldState resourceCatalog)
    (backed : MachineCustody.Backed world custody)
    (process : QueuedProcess schema)
    (consumedComplete :
      ConsumedInputsComplete (schema.process process.processKind)
        process.reservations) :
    Except SimulatorIssue
      (ReservationRelease resourceCatalog world process custody) :=
  match returnReservations custody world backed process.reservations with
  | .error issue => .error issue
  | .ok returned =>
      let remaining := process.reservations.filter fun reservation =>
        decide (reservation.use ≠ .reserved)
      .ok
        { world := returned.world
          backed := returned.backed
          process :=
            { process with
              reservations := remaining
              reservationsValid := by
                intro reservation reservationMem
                exact process.reservationsValid reservation
                  (List.mem_filter.mp reservationMem).1
              consumedInputsComplete := .complete (by
                intro port portMem
                obtain ⟨reservation, reservationMem, useEq, labelEq, basketEq⟩ :=
                  consumedComplete port portMem
                exact ⟨reservation, List.mem_filter.mpr ⟨reservationMem, by
                  simp [useEq]⟩, useEq, labelEq, basketEq⟩)
              reservedInputsComplete := .missing }
          kindPreserved := rfl
          consumedComplete := by
            intro port portMem
            obtain ⟨reservation, reservationMem, useEq, labelEq, basketEq⟩ :=
              consumedComplete port portMem
            exact ⟨reservation, List.mem_filter.mpr ⟨reservationMem, by
              simp [useEq]⟩, useEq, labelEq, basketEq⟩
          receipts := returned.receipts ++ [.reservationsReleased process.id]
          worldEffects := returned.worldEffects
          replayExact := returned.replayExact }

private structure RecipientBindingRun
    {schema : MachineSchema}
    (before : QueuedProcess schema) where
  process : QueuedProcess schema
  kindPreserved : process.processKind = before.processKind
  reservationsPreserved : process.reservations = before.reservations
  receipts : List SimulatorEffectReceipt

private def bindLateRecipients
    {schema : MachineSchema}
    (late : List (schema.Label × AccountId))
    (process : QueuedProcess schema) :
    Except SimulatorIssue (RecipientBindingRun process) := by
  letI : DecidableEq schema.Label := schema.labelDecidableEq
  match late with
  | [] =>
      let result : RecipientBindingRun process :=
        { process := process
          kindPreserved := rfl
          reservationsPreserved := rfl
          receipts := [] }
      exact .ok result
  | (label, account) :: rest =>
      match (schema.process process.processKind).outputFor label with
      | none => exact .error .outputLabelMissing
      | some _ =>
          match pending : process.bindings.output label with
          | some _ => exact .error .recipientAlreadyBound
          | none =>
              let updated : QueuedProcess schema :=
                { process with
                  bindings := process.bindings.bindOutput label account pending }
              match bindLateRecipients rest updated with
              | .error issue => exact .error issue
              | .ok suffix =>
                  let result : RecipientBindingRun process :=
                    { process := suffix.process
                      kindPreserved := suffix.kindPreserved
                      reservationsPreserved := suffix.reservationsPreserved
                      receipts := .recipientBound account :: suffix.receipts }
                  exact .ok result

def deliverAllocations
    {resourceCatalog : ResourceCatalog}
    {Label : Type}
    {inventory : AccountId}
    (custody : MachineCustody inventory) :
    (world : WorldState resourceCatalog) →
    MachineCustody.Backed world custody →
    (allocations : List (OutputAllocation Label)) →
      Except SimulatorIssue
        (AllocationDelivery resourceCatalog custody world allocations)
  | world, backed, [] =>
      .ok
        { world, backed, receipts := []
          worldEffects := []
          replayExact := rfl
          delivered := by simp [AllocationsDelivered]
          sound := by simp [AllocationReceiptsSound] }
  | world, backed, allocation :: rest =>
      match recipientEq : allocation.recipient with
      | none => .error .outputRecipientMissing
      | some recipient =>
          if same : allocation.custody = recipient then
            match deliverAllocations custody world backed rest with
            | .error issue => .error issue
            | .ok suffix =>
                .ok
                  { world := suffix.world
                    backed := suffix.backed
                    receipts := suffix.receipts
                    worldEffects := suffix.worldEffects
                    replayExact := suffix.replayExact
                    delivered := by
                      intro queried queriedMem
                      simp only [List.mem_cons] at queriedMem
                      rcases queriedMem with isHead | inRest
                      · subst queried
                        exact ⟨recipient, recipientEq, Or.inl same⟩
                      · exact suffix.delivered queried inRest
                    sound := by
                      intro receipt receiptMem
                      obtain ⟨matched, matchedMem, exactMatch⟩ :=
                        suffix.sound receipt receiptMem
                      exact ⟨matched, by simp [matchedMem], exactMatch⟩ }
          else
            let proposal : Transfer :=
              { source := allocation.custody
                destination := recipient
                basket := allocation.basket }
            match MachineCustody.assessCustodyTransfer world custody proposal with
            | .rejected issues _ _ => .error (.transferRejected issues)
            | .accepted accepted =>
                let after := applyTransferState accepted.transferAccepted
                let afterBacked := backed.applyCustodyTransfer accepted
                match deliverAllocations custody after afterBacked rest with
                | .error issue => .error issue
                | .ok suffix =>
                    .ok
                      { world := suffix.world
                        backed := suffix.backed
                        receipts :=
                          .transfer (transferReceipt accepted.transferAccepted) ::
                            suffix.receipts
                        worldEffects :=
                          .transfer (transferReceipt accepted.transferAccepted) ::
                            suffix.worldEffects
                        replayExact := by
                          change replayWorldEffectReceipts suffix.worldEffects
                              (replayReceipt
                                (transferReceipt accepted.transferAccepted)
                                world.holdings) = suffix.world.holdings
                          rw [replay_transferReceipt accepted.transferAccepted]
                          exact suffix.replayExact
                        delivered := by
                          intro queried queriedMem
                          simp only [List.mem_cons] at queriedMem
                          rcases queriedMem with isHead | inRest
                          · subst queried
                            let receipt := transferReceipt accepted.transferAccepted
                            exact ⟨recipient, recipientEq, Or.inr ⟨receipt,
                              List.mem_cons_self, rfl, rfl,
                              transferReceipt_entries accepted.transferAccepted⟩⟩
                          · obtain ⟨bound, recipientEq, delivered⟩ :=
                              suffix.delivered queried inRest
                            exact ⟨bound, recipientEq, by
                              rcases delivered with already | ⟨receipt, receiptMem,
                                exactDelivery⟩
                              · exact Or.inl already
                              · exact Or.inr ⟨receipt, by simp [receiptMem],
                                  exactDelivery⟩⟩
                        sound := by
                          intro receipt receiptMem
                          simp only [List.mem_cons] at receiptMem
                          rcases receiptMem with isHead | inRest
                          · cases isHead
                            exact ⟨allocation, by simp, recipient, recipientEq,
                              rfl, rfl,
                              transferReceipt_entries accepted.transferAccepted⟩
                          · obtain ⟨matched, matchedMem, exactMatch⟩ :=
                              suffix.sound receipt inRest
                            exact ⟨matched, by simp [matchedMem], exactMatch⟩ }

private structure EffectState
    (resourceCatalog : ResourceCatalog)
    (schema : MachineSchema)
    (language : OperationLanguage schema)
    (worldOrigin : List (Holding AccountId)) where
  runtime : SimulatorState resourceCatalog schema language
  pending : Option (QueuedProcess schema)
  lateRecipients : List (schema.Label × AccountId)
  receipts : List SimulatorEffectReceipt
  worldEffects : List WorldEffectReceipt
  worldReplayExact :
    replayWorldEffectReceipts worldEffects worldOrigin = runtime.world.holdings

private def checkExpectedKind
    {schema : MachineSchema}
    (expected : Option schema.ProcessKind)
    (actual : schema.ProcessKind) : Except SimulatorIssue Unit := by
  letI : DecidableEq schema.ProcessKind := schema.processKindDecidableEq
  match expected with
  | none => exact .ok ()
  | some kind =>
      if kind = actual then exact .ok () else exact .error .processKindMismatch

private theorem appendWorldReplay
    {resourceCatalog : ResourceCatalog}
    {schema : MachineSchema}
    {language : OperationLanguage schema}
    {worldOrigin : List (Holding AccountId)}
    (current : EffectState resourceCatalog schema language worldOrigin)
    (added : List WorldEffectReceipt)
    (afterHoldings : List (Holding AccountId))
    (localExact :
      replayWorldEffectReceipts added current.runtime.world.holdings =
        afterHoldings) :
    replayWorldEffectReceipts (current.worldEffects ++ added)
        worldOrigin = afterHoldings := by
  rw [replayWorldEffectReceipts_append, current.worldReplayExact]
  exact localExact

private def applyEffect
    {resourceCatalog : ResourceCatalog}
    {schema : MachineSchema}
    {language : OperationLanguage schema}
    {worldOrigin : List (Holding AccountId)}
    (proposal : OperationProposal schema language)
    (definition : OperationDefinition schema language.QueuePort language.Guard) :
    EffectState resourceCatalog schema language worldOrigin →
    OperationEffect schema language.QueuePort →
      Except SimulatorIssue
        (EffectState resourceCatalog schema language worldOrigin)
  | current, .reserveConsumedInputs =>
      match current.pending with
      | some _ => .error .pendingProcessAlreadyExists
      | none =>
          match definition.processKind, proposal.processBindings with
          | none, _ => .error .missingProcessKind
          | _, none => .error .missingProcessBindings
          | some kind, some bindings =>
              match reserveConsumedProcess current.runtime.custody
                  current.runtime.world current.runtime.custodyBacked
                  (schema.process kind) bindings with
              | .error issue => .error issue
              | .ok reserved =>
                  let queued : QueuedProcess schema :=
                    { id := current.runtime.nextProcessId
                      processKind := kind
                      bindings := bindings
                      reservations := reserved.reservations
                      reservationsValid := reserved.reservationsValid
                      consumedInputsComplete := reserved.consumedComplete
                      reservedInputsComplete := .missing }
                  .ok
                    { current with
                      runtime :=
                        { current.runtime with
                          world := reserved.world
                          custodyBacked := reserved.backed
                          nextProcessId := current.runtime.nextProcessId + 1 }
                      pending := some queued
                      receipts := current.receipts ++ reserved.receipts
                      worldEffects := current.worldEffects ++ reserved.worldEffects
                      worldReplayExact := appendWorldReplay current
                        reserved.worldEffects reserved.world.holdings
                        reserved.replayExact }
  | current, .reserveReservedInputs source =>
      match proposal.queueBindings.resolve source with
      | none => .error (.queueBindingMissing .input)
      | some queueId =>
          match current.runtime.machine.inputQueue? queueId with
          | none => .error (.queueMissing .input queueId.value)
          | some queue =>
              match Queue.assessDequeue queue.contents with
              | .rejected issues _ _ => .error (.queueRejected .input issues)
              | .accepted accepted =>
                  let front := (Queue.dequeue queue.contents accepted).removed.value
                  let process := front.process
                  match checkExpectedKind definition.processKind process.kind with
                  | .error issue => .error issue
                  | .ok _ =>
                      if process.reservations.any fun reservation =>
                          decide (reservation.use = .reserved) then
                        .error .reservedInputsAlreadyExist
                      else
                        match reserveReservedProcess current.runtime.custody
                            current.runtime.world current.runtime.custodyBacked
                            (schema.process process.kind) process.bindings with
                        | .error issue => .error issue
                        | .ok reserved =>
                            let updated : QueuedProcess schema :=
                              { process with
                                reservations :=
                                  process.reservations ++ reserved.reservations
                                reservationsValid := by
                                  intro reservation reservationMem
                                  simp only [List.mem_append] at reservationMem
                                  rcases reservationMem with existing | added
                                  · exact process.reservationsValid reservation existing
                                  · exact reserved.reservationsValid reservation added
                                consumedInputsComplete :=
                                  match process.consumedInputsComplete with
                                  | .missing => .missing
                                  | .complete complete => .complete (by
                                      intro port portMem
                                      obtain ⟨reservation, reservationMem, useEq,
                                          labelEq, basketEq⟩ := complete port portMem
                                      exact ⟨reservation, by simp [reservationMem],
                                        useEq, labelEq, basketEq⟩)
                                reservedInputsComplete :=
                                  match reserved.reservedComplete with
                                  | .missing => .missing
                                  | .complete complete => .complete (by
                                      intro port portMem
                                      obtain ⟨reservation, reservationMem, useEq,
                                          labelEq, basketEq⟩ := complete port portMem
                                      exact ⟨reservation, by simp [reservationMem],
                                        useEq, labelEq, basketEq⟩) }
                            let entry : InputQueueEntry schema queue.kind :=
                              { process := updated
                                accepted := by
                                  change schema.acceptsInput queue.kind updated.kind
                                  exact front.accepted
                                consumedInputsComplete := by
                                  intro port portMem
                                  obtain ⟨reservation, reservationMem, useEq,
                                      labelEq, basketEq⟩ :=
                                    front.consumedInputsComplete port portMem
                                  exact ⟨reservation, by
                                      rw [show updated.reservations =
                                        process.reservations ++ reserved.reservations
                                        by rfl]
                                      exact List.mem_append_left _ reservationMem,
                                    useEq, labelEq, basketEq⟩ }
                            let replacement : MachineInputQueue schema :=
                              { queue with
                                contents := queue.contents.replaceFront accepted entry }
                            .ok
                              { current with
                                runtime :=
                                  { current.runtime with
                                    world := reserved.world
                                    custodyBacked := reserved.backed
                                    machine := current.runtime.machine
                                      |>.replaceInputQueue replacement }
                                receipts := current.receipts ++ reserved.receipts
                                worldEffects := current.worldEffects ++
                                  reserved.worldEffects
                                worldReplayExact := appendWorldReplay current
                                  reserved.worldEffects reserved.world.holdings
                                  reserved.replayExact }
  | current, .enqueue destination =>
      match proposal.queueBindings.resolve destination with
      | none => .error (.queueBindingMissing .input)
      | some queueId =>
          match current.runtime.machine.inputQueue? queueId with
          | none => .error (.queueMissing .input queueId.value)
          | some queue =>
              match current.pending with
              | none => .error .pendingProcessMissing
              | some process =>
                  match process.consumedInputsComplete with
                  | .missing => .error .consumedInputsMissing
                  | .complete complete =>
                      letI := schema.acceptsInputDecidable queue.kind process.kind
                      if accepts : schema.acceptsInput queue.kind process.kind then
                        match Queue.assessEnqueue queue.contents with
                        | .rejected issues _ _ => .error (.queueRejected .input issues)
                        | .accepted accepted =>
                            let entry : InputQueueEntry schema queue.kind :=
                              { process
                                accepted := accepts
                                consumedInputsComplete := complete }
                            let enqueued := Queue.enqueue queue.contents entry accepted
                            let replacement : MachineInputQueue schema :=
                              { queue with contents := enqueued.queue }
                            .ok
                              { current with
                                runtime :=
                                  { current.runtime with
                                    machine := current.runtime.machine.replaceInputQueue
                                      replacement }
                                pending := none
                                receipts := current.receipts ++
                                  [.enqueued queueId.value enqueued.admitted.ticket
                                    process.id] }
                      else .error (.queueRejectsProcess .input)
  | current, .moveToProcessing source destination =>
      match proposal.queueBindings.resolve source,
          proposal.queueBindings.resolve destination with
      | none, _ => .error (.queueBindingMissing .input)
      | _, none => .error (.queueBindingMissing .processing)
      | some inputId, some processingId =>
          match inputFound : current.runtime.machine.inputQueue? inputId,
              processingFound : current.runtime.machine.processingQueue? processingId with
          | none, _ => .error (.queueMissing .input inputId.value)
          | _, none => .error (.queueMissing .processing processingId.value)
          | some inputQueue, some processingQueue =>
              match Queue.assessDequeue inputQueue.contents with
              | .rejected issues _ _ => .error (.queueRejected .input issues)
              | .accepted acceptedDequeue =>
                  let removed := Queue.dequeue inputQueue.contents acceptedDequeue
                  let process := removed.removed.value.process
                  match checkExpectedKind definition.processKind process.kind with
                  | .error issue => .error issue
                  | .ok _ =>
                      match process.reservedInputsComplete with
                      | .missing => .error .reservedInputsMissing
                      | .complete complete =>
                          letI := schema.acceptsProcessingDecidable
                            processingQueue.kind process.kind
                          if accepts : schema.acceptsProcessing
                              processingQueue.kind process.kind then
                            match assessActiveCustody current.runtime.custody
                                proposal.custodyBindings
                                (schema.process process.kind).activeCustody with
                            | .rejected failures _ =>
                                .error (.activeCustodyRejected failures)
                            | .accepted dependencyBinding =>
                                match Queue.assessEnqueue processingQueue.contents with
                                | .rejected issues _ _ =>
                                    .error (.queueRejected .processing issues)
                                | .accepted acceptedEnqueue =>
                                    let active : ActiveProcess schema :=
                                      { queued := process
                                        progress := 0
                                        custodyDependencies :=
                                          dependencyBinding.dependencies
                                        custodyDependenciesExact :=
                                          dependencyBinding.exact }
                                    let entry : ProcessingQueueEntry schema
                                        processingQueue.kind :=
                                      { process := active
                                        accepted := accepts
                                        reservedInputsComplete := complete
                                        consumedInputsComplete :=
                                          removed.removed.value.consumedInputsComplete }
                                    let enqueued := Queue.enqueue
                                      processingQueue.contents entry acceptedEnqueue
                                    let inputReplacement : MachineInputQueue schema :=
                                      { inputQueue with contents := removed.queue }
                                    let processingReplacement :
                                        MachineProcessingQueue schema :=
                                      { processingQueue with contents := enqueued.queue }
                                    let machineAfterInput :=
                                      current.runtime.machine.replaceInputQueue
                                        inputReplacement
                                    let machine := machineAfterInput.replaceProcessingQueue
                                      processingReplacement
                                    have processingPresent : processingQueue ∈
                                        current.runtime.machine.processingQueues :=
                                      current.runtime.machine.processingQueue?_mem
                                        processingFound
                                    have processingHeld :
                                        processingQueue.DependenciesSatisfy
                                          (ActiveCustodyDependency.HeldBy
                                            current.runtime.custody) :=
                                      current.runtime.activeCustodyHeld processingQueue
                                        processingPresent
                                    have replacementHeld :
                                        processingReplacement.DependenciesSatisfy
                                          (ActiveCustodyDependency.HeldBy
                                            current.runtime.custody) :=
                                      processingHeld.enqueue entry dependencyBinding.held
                                        acceptedEnqueue
                                    have machineHeld :
                                        machine.ActiveDependenciesSatisfy
                                          (ActiveCustodyDependency.HeldBy
                                            current.runtime.custody) :=
                                      (current.runtime.activeCustodyHeld.replaceInputQueue
                                        inputReplacement).replaceProcessingQueue
                                          processingReplacement replacementHeld
                                    .ok
                                      { current with
                                        runtime :=
                                          { current.runtime with
                                            machine
                                            activeCustodyHeld := machineHeld }
                                        receipts := current.receipts ++
                                          [.custodyDependenciesBound process.id
                                              (dependencyBinding.dependencies.map
                                                ActiveCustodyDependency.positionId),
                                            .dispatched inputId.value processingId.value
                                              process.id] }
                          else .error (.queueRejectsProcess .processing)
  | current, .advance source work _ =>
      match proposal.queueBindings.resolve source with
      | none => .error (.queueBindingMissing .processing)
      | some queueId =>
          match queueFound : current.runtime.machine.processingQueue? queueId with
          | none => .error (.queueMissing .processing queueId.value)
          | some queue =>
              match Queue.assessDequeue queue.contents with
              | .rejected issues _ _ => .error (.queueRejected .processing issues)
              | .accepted accepted =>
                  let front := (Queue.dequeue queue.contents accepted).removed.value
                  match checkExpectedKind definition.processKind front.process.kind with
                  | .error issue => .error issue
                  | .ok _ =>
                      let advanced : ActiveProcess schema :=
                        { front.process with progress := front.process.progress + work }
                      let entry : ProcessingQueueEntry schema queue.kind :=
                        { process := advanced
                          accepted := front.accepted
                          reservedInputsComplete := front.reservedInputsComplete
                          consumedInputsComplete := front.consumedInputsComplete }
                      let replacement : MachineProcessingQueue schema :=
                        { queue with
                          contents := queue.contents.replaceFront accepted entry }
                      have queuePresent : queue ∈
                          current.runtime.machine.processingQueues :=
                        current.runtime.machine.processingQueue?_mem queueFound
                      have queueHeld : queue.DependenciesSatisfy
                          (ActiveCustodyDependency.HeldBy current.runtime.custody) :=
                        current.runtime.activeCustodyHeld queue queuePresent
                      have entryHeld : ∀ dependency ∈
                          entry.process.custodyDependencies,
                          dependency.HeldBy current.runtime.custody := by
                        intro dependency dependencyMem
                        apply queueHeld dependency
                        apply List.mem_flatMap.mpr
                        exact ⟨(Queue.dequeue queue.contents accepted).removed,
                          Queue.dequeue_removed_mem queue.contents accepted,
                          dependencyMem⟩
                      have replacementHeld : replacement.DependenciesSatisfy
                          (ActiveCustodyDependency.HeldBy current.runtime.custody) :=
                        queueHeld.replaceFront accepted entry entryHeld
                      let machine := current.runtime.machine.replaceProcessingQueue
                        replacement
                      have machineHeld : machine.ActiveDependenciesSatisfy
                          (ActiveCustodyDependency.HeldBy current.runtime.custody) :=
                        current.runtime.activeCustodyHeld.replaceProcessingQueue
                          replacement replacementHeld
                      .ok
                        { current with
                          runtime :=
                            { current.runtime with
                              machine
                              activeCustodyHeld := machineHeld }
                          receipts := current.receipts ++
                            [.advanced queueId.value front.process.queued.id
                              front.process.progress advanced.progress] }
  | current, .bindOutput label =>
      match proposal.recipientBindings.resolve label with
      | none => .error .recipientBindingMissing
      | some account =>
          .ok
            { current with
              lateRecipients := current.lateRecipients ++ [(label, account)] }
  | current, .completeToOutput source destination =>
      match proposal.queueBindings.resolve source,
          proposal.queueBindings.resolve destination with
      | none, _ => .error (.queueBindingMissing .processing)
      | _, none => .error (.queueBindingMissing .output)
      | some processingId, some outputId =>
          match processingFound : current.runtime.machine.processingQueue? processingId,
              outputFound : current.runtime.machine.outputQueue? outputId with
          | none, _ => .error (.queueMissing .processing processingId.value)
          | _, none => .error (.queueMissing .output outputId.value)
          | some processingQueue, some outputQueue =>
              match Queue.assessDequeue processingQueue.contents with
              | .rejected issues _ _ => .error (.queueRejected .processing issues)
              | .accepted acceptedDequeue =>
                  let removed := Queue.dequeue processingQueue.contents acceptedDequeue
                  let active := removed.removed.value.process
                  match checkExpectedKind definition.processKind active.kind with
                  | .error issue => .error issue
                  | .ok _ =>
                      let required := (schema.process active.kind).requiredWork
                      if _enough : required ≤ active.progress then
                        letI := schema.acceptsOutputDecidable outputQueue.kind active.kind
                        if accepts : schema.acceptsOutput outputQueue.kind active.kind then
                          match Queue.assessEnqueue outputQueue.contents with
                          | .rejected issues _ _ =>
                              .error (.queueRejected .output issues)
                          | .accepted acceptedEnqueue =>
                              match completeInventory current.runtime.custody
                                  current.runtime.world current.runtime.custodyBacked
                                  active.queued with
                              | .error issue => .error issue
                              | .ok inventory =>
                                  let completedActive : ActiveProcess schema :=
                                    { queued := inventory.process
                                      progress := active.progress
                                      custodyDependencies := active.custodyDependencies
                                      custodyDependenciesExact := by
                                        simpa [ActiveProcess.kind, QueuedProcess.kind,
                                          inventory.kindPreserved] using
                                          active.custodyDependenciesExact }
                                  let completed : CompletedProcess schema :=
                                    { active := completedActive
                                      workComplete := by
                                        change
                                          (schema.process inventory.process.processKind).requiredWork ≤
                                            active.progress
                                        rw [inventory.kindPreserved]
                                        exact _enough
                                      reservationsCleared :=
                                        by simpa [completedActive] using
                                          inventory.reservationsCleared }
                                  let entry : OutputQueueEntry schema outputQueue.kind :=
                                    { process := completed
                                      accepted := by
                                        simpa [completed, completedActive,
                                          CompletedProcess.kind, ActiveProcess.kind,
                                          QueuedProcess.kind, inventory.kindPreserved] using
                                          accepts
                                      allocations := completed.outputAllocations
                                      allocationLabelsUnique :=
                                        completed.active.queued.invocation
                                          |>.outputAllocations_labelsUnique }
                                  let enqueued := Queue.enqueue outputQueue.contents
                                    entry acceptedEnqueue
                                  let processingReplacement :
                                      MachineProcessingQueue schema :=
                                    { processingQueue with contents := removed.queue }
                                  let outputReplacement : MachineOutputQueue schema :=
                                    { outputQueue with contents := enqueued.queue }
                                  let machine :=
                                    (current.runtime.machine.replaceProcessingQueue
                                      processingReplacement).replaceOutputQueue
                                        outputReplacement
                                  have processingPresent : processingQueue ∈
                                      current.runtime.machine.processingQueues :=
                                    current.runtime.machine.processingQueue?_mem
                                      processingFound
                                  have processingHeld :
                                      processingQueue.DependenciesSatisfy
                                        (ActiveCustodyDependency.HeldBy
                                          current.runtime.custody) :=
                                    current.runtime.activeCustodyHeld processingQueue
                                      processingPresent
                                  have processingReplacementHeld :
                                      processingReplacement.DependenciesSatisfy
                                        (ActiveCustodyDependency.HeldBy
                                          current.runtime.custody) :=
                                    processingHeld.dequeue acceptedDequeue
                                  have machineHeld :
                                      machine.ActiveDependenciesSatisfy
                                        (ActiveCustodyDependency.HeldBy
                                          current.runtime.custody) :=
                                    (current.runtime.activeCustodyHeld
                                      |>.replaceProcessingQueue processingReplacement
                                        processingReplacementHeld)
                                      |>.replaceOutputQueue outputReplacement
                                  .ok
                                    { current with
                                      runtime :=
                                        { current.runtime with
                                          world := inventory.world
                                          custodyBacked := inventory.backed
                                          machine
                                          activeCustodyHeld := machineHeld }
                                      receipts := current.receipts ++ inventory.receipts ++
                                        [.custodyDependenciesReleased active.queued.id
                                            (active.custodyDependencies.map
                                              ActiveCustodyDependency.positionId),
                                          .completed processingId.value
                                          (some outputId.value) active.queued.id]
                                      worldEffects := current.worldEffects ++
                                        inventory.worldEffects
                                      worldReplayExact := appendWorldReplay current
                                        inventory.worldEffects inventory.world.holdings
                                        inventory.replayExact }
                        else .error (.queueRejectsProcess .output)
                      else .error (.insufficientWork required active.progress)
  | current, .completeToInventories source =>
      match proposal.queueBindings.resolve source with
      | none => .error (.queueBindingMissing .processing)
      | some processingId =>
          match processingFound : current.runtime.machine.processingQueue? processingId with
          | none => .error (.queueMissing .processing processingId.value)
          | some processingQueue =>
              match Queue.assessDequeue processingQueue.contents with
              | .rejected issues _ _ => .error (.queueRejected .processing issues)
              | .accepted acceptedDequeue =>
                  let removed := Queue.dequeue processingQueue.contents acceptedDequeue
                  let active := removed.removed.value.process
                  match checkExpectedKind definition.processKind active.kind with
                  | .error issue => .error issue
                  | .ok _ =>
                      let required := (schema.process active.kind).requiredWork
                      if _enough : required ≤ active.progress then
                        match completeInventory current.runtime.custody
                            current.runtime.world current.runtime.custodyBacked
                            active.queued with
                        | .error issue => .error issue
                        | .ok inventory =>
                            let completedActive : ActiveProcess schema :=
                              { queued := inventory.process
                                progress := active.progress
                                custodyDependencies := active.custodyDependencies
                                custodyDependenciesExact := by
                                  simpa [ActiveProcess.kind, QueuedProcess.kind,
                                    inventory.kindPreserved] using
                                    active.custodyDependenciesExact }
                            let completed : CompletedProcess schema :=
                              { active := completedActive
                                workComplete := by
                                  change
                                    (schema.process inventory.process.processKind).requiredWork ≤
                                      active.progress
                                  rw [inventory.kindPreserved]
                                  exact _enough
                                reservationsCleared := by
                                  simpa [completedActive] using
                                    inventory.reservationsCleared }
                            match deliverAllocations current.runtime.custody
                                inventory.world inventory.backed
                                completed.outputAllocations with
                            | .error issue => .error issue
                            | .ok delivery =>
                                let replacement : MachineProcessingQueue schema :=
                                  { processingQueue with contents := removed.queue }
                                let machine := current.runtime.machine
                                  |>.replaceProcessingQueue replacement
                                have processingPresent : processingQueue ∈
                                    current.runtime.machine.processingQueues :=
                                  current.runtime.machine.processingQueue?_mem
                                    processingFound
                                have processingHeld :
                                    processingQueue.DependenciesSatisfy
                                      (ActiveCustodyDependency.HeldBy
                                        current.runtime.custody) :=
                                  current.runtime.activeCustodyHeld processingQueue
                                    processingPresent
                                have replacementHeld :
                                    replacement.DependenciesSatisfy
                                      (ActiveCustodyDependency.HeldBy
                                        current.runtime.custody) :=
                                  processingHeld.dequeue acceptedDequeue
                                have machineHeld :
                                    machine.ActiveDependenciesSatisfy
                                      (ActiveCustodyDependency.HeldBy
                                        current.runtime.custody) :=
                                  current.runtime.activeCustodyHeld
                                    |>.replaceProcessingQueue replacement replacementHeld
                                .ok
                                  { current with
                                    runtime :=
                                      { current.runtime with
                                        world := delivery.world
                                        custodyBacked := delivery.backed
                                        machine
                                        activeCustodyHeld := machineHeld }
                                    receipts := current.receipts ++
                                      inventory.receipts ++ delivery.receipts ++
                                      [.custodyDependenciesReleased active.queued.id
                                          (active.custodyDependencies.map
                                            ActiveCustodyDependency.positionId),
                                        .completed processingId.value none
                                        active.queued.id]
                                    worldEffects := current.worldEffects ++
                                      (inventory.worldEffects ++ delivery.worldEffects)
                                    worldReplayExact := appendWorldReplay current
                                      (inventory.worldEffects ++ delivery.worldEffects)
                                      delivery.world.holdings (by
                                        rw [replayWorldEffectReceipts_append,
                                          inventory.replayExact]
                                        exact delivery.replayExact) }
                      else .error (.insufficientWork required active.progress)
  | current, .cancelInput source disposition =>
      match proposal.queueBindings.resolve source with
      | none => .error (.queueBindingMissing .input)
      | some queueId =>
          match current.runtime.machine.inputQueue? queueId with
          | none => .error (.queueMissing .input queueId.value)
          | some queue =>
              match Queue.assessDequeue queue.contents with
              | .rejected issues _ _ => .error (.queueRejected .input issues)
              | .accepted accepted =>
                  let removed := Queue.dequeue queue.contents accepted
                  let process := removed.removed.value.process
                  match checkExpectedKind definition.processKind process.kind with
                  | .error issue => .error issue
                  | .ok _ =>
                      match cancelInventory current.runtime.custody
                          current.runtime.world current.runtime.custodyBacked
                          process disposition with
                      | .error issue => .error issue
                      | .ok cancelled =>
                          let replacement : MachineInputQueue schema :=
                            { queue with contents := removed.queue }
                          let machine := current.runtime.machine.replaceInputQueue
                            replacement
                          have machineHeld : machine.ActiveDependenciesSatisfy
                              (ActiveCustodyDependency.HeldBy current.runtime.custody) :=
                            current.runtime.activeCustodyHeld.replaceInputQueue
                              replacement
                          .ok
                            { current with
                              runtime :=
                                { current.runtime with
                                  world := cancelled.world
                                  custodyBacked := cancelled.backed
                                  machine
                                  activeCustodyHeld := machineHeld }
                              receipts := current.receipts ++ cancelled.receipts ++
                                [.cancelled .input queueId.value process.id
                                  disposition]
                              worldEffects := current.worldEffects ++
                                cancelled.worldEffects
                              worldReplayExact := appendWorldReplay current
                                cancelled.worldEffects cancelled.world.holdings
                                cancelled.replayExact }
  | current, .cancelProcessing source disposition =>
      match proposal.queueBindings.resolve source with
      | none => .error (.queueBindingMissing .processing)
      | some queueId =>
          match queueFound : current.runtime.machine.processingQueue? queueId with
          | none => .error (.queueMissing .processing queueId.value)
          | some queue =>
              match Queue.assessDequeue queue.contents with
              | .rejected issues _ _ => .error (.queueRejected .processing issues)
              | .accepted accepted =>
                  let removed := Queue.dequeue queue.contents accepted
                  let active := removed.removed.value.process
                  match checkExpectedKind definition.processKind active.kind with
                  | .error issue => .error issue
                  | .ok _ =>
                      match cancelInventory current.runtime.custody
                          current.runtime.world current.runtime.custodyBacked
                          active.queued disposition with
                      | .error issue => .error issue
                      | .ok cancelled =>
                          let replacement : MachineProcessingQueue schema :=
                            { queue with contents := removed.queue }
                          let machine := current.runtime.machine
                            |>.replaceProcessingQueue replacement
                          have queuePresent : queue ∈
                              current.runtime.machine.processingQueues :=
                            current.runtime.machine.processingQueue?_mem queueFound
                          have queueHeld : queue.DependenciesSatisfy
                              (ActiveCustodyDependency.HeldBy current.runtime.custody) :=
                            current.runtime.activeCustodyHeld queue queuePresent
                          have replacementHeld : replacement.DependenciesSatisfy
                              (ActiveCustodyDependency.HeldBy current.runtime.custody) :=
                            queueHeld.dequeue accepted
                          have machineHeld : machine.ActiveDependenciesSatisfy
                              (ActiveCustodyDependency.HeldBy current.runtime.custody) :=
                            current.runtime.activeCustodyHeld
                              |>.replaceProcessingQueue replacement replacementHeld
                          .ok
                            { current with
                              runtime :=
                                { current.runtime with
                                  world := cancelled.world
                                  custodyBacked := cancelled.backed
                                  machine
                                  activeCustodyHeld := machineHeld }
                              receipts := current.receipts ++ cancelled.receipts ++
                                [.custodyDependenciesReleased active.queued.id
                                    (active.custodyDependencies.map
                                      ActiveCustodyDependency.positionId),
                                  .cancelled .processing queueId.value active.queued.id
                                  disposition]
                              worldEffects := current.worldEffects ++
                                cancelled.worldEffects
                              worldReplayExact := appendWorldReplay current
                                cancelled.worldEffects cancelled.world.holdings
                                cancelled.replayExact }
  | current, .collectAllocation source label =>
      match proposal.queueBindings.resolve source with
      | none => .error (.queueBindingMissing .output)
      | some queueId =>
          match current.runtime.machine.outputQueue? queueId with
          | none => .error (.queueMissing .output queueId.value)
          | some queue =>
              match Queue.assessDequeue queue.contents with
              | .rejected issues _ _ => .error (.queueRejected .output issues)
              | .accepted accepted =>
                  let front := (Queue.dequeue queue.contents accepted).removed.value
                  match checkExpectedKind definition.processKind front.process.kind with
                  | .error issue => .error issue
                  | .ok _ =>
                      letI : DecidableEq schema.Label := schema.labelDecidableEq
                      match selectedEq : front.allocations.find?
                          fun allocation => allocation.label = label with
                      | none => .error .outputLabelMissing
                      | some selected =>
                          let recipient? := selected.recipient.orElse fun _ =>
                            proposal.recipientBindings.resolve label
                          match recipient? with
                          | none => .error .recipientBindingMissing
                          | some recipient =>
                              let allocation : OutputAllocation schema.Label :=
                                { selected with recipient := some recipient }
                              match deliverAllocations current.runtime.custody
                                  current.runtime.world current.runtime.custodyBacked
                                  [allocation] with
                              | .error issue => .error issue
                              | .ok delivery =>
                                  let remaining :=
                                    remainingAllocations front.allocations label
                                  let removed := Queue.dequeue queue.contents accepted
                                  if _empty : remaining = [] then
                                    let replacement : MachineOutputQueue schema :=
                                      { queue with contents := removed.queue }
                                    .ok
                                      { current with
                                        runtime :=
                                          { current.runtime with
                                            world := delivery.world
                                            custodyBacked := delivery.backed
                                            machine := current.runtime.machine
                                              |>.replaceOutputQueue replacement }
                                        receipts := current.receipts ++
                                          delivery.receipts ++
                                          [.allocationCollected queueId.value
                                            front.process.active.queued.id 0]
                                        worldEffects := current.worldEffects ++
                                          delivery.worldEffects
                                        worldReplayExact := appendWorldReplay current
                                          delivery.worldEffects delivery.world.holdings
                                          delivery.replayExact }
                                  else
                                    let updated : OutputQueueEntry schema queue.kind :=
                                      { front with
                                        allocations := remaining
                                        allocationLabelsUnique :=
                                          remainingAllocations_labelsUnique
                                            front.allocations label
                                            front.allocationLabelsUnique }
                                    let replacement : MachineOutputQueue schema :=
                                      { queue with
                                        contents := queue.contents.replaceFront
                                          accepted updated }
                                    .ok
                                      { current with
                                        runtime :=
                                          { current.runtime with
                                            world := delivery.world
                                            custodyBacked := delivery.backed
                                            machine := current.runtime.machine
                                              |>.replaceOutputQueue replacement }
                                        receipts := current.receipts ++
                                          delivery.receipts ++
                                          [.allocationCollected queueId.value
                                            front.process.active.queued.id
                                            remaining.length]
                                        worldEffects := current.worldEffects ++
                                          delivery.worldEffects
                                        worldReplayExact := appendWorldReplay current
                                          delivery.worldEffects delivery.world.holdings
                                          delivery.replayExact }
  | current, .collect source =>
      match proposal.queueBindings.resolve source with
      | none => .error (.queueBindingMissing .output)
      | some queueId =>
          match current.runtime.machine.outputQueue? queueId with
          | none => .error (.queueMissing .output queueId.value)
          | some queue =>
              match Queue.assessDequeue queue.contents with
              | .rejected issues _ _ => .error (.queueRejected .output issues)
              | .accepted accepted =>
                  let removed := Queue.dequeue queue.contents accepted
                  let front := removed.removed.value
                  let completed := front.process
                  match checkExpectedKind definition.processKind completed.kind with
                  | .error issue => .error issue
                  | .ok _ =>
                      match bindLateRecipients current.lateRecipients
                          completed.active.queued with
                      | .error issue => .error issue
                      | .ok binding =>
                          let reboundAllocations := front.allocations.map fun allocation =>
                            { allocation with
                              recipient := binding.process.bindings.output allocation.label }
                          match deliverAllocations current.runtime.custody
                              current.runtime.world current.runtime.custodyBacked
                              reboundAllocations with
                          | .error issue => .error issue
                          | .ok delivery =>
                              let replacement : MachineOutputQueue schema :=
                                { queue with contents := removed.queue }
                              .ok
                                { current with
                                  runtime :=
                                    { current.runtime with
                                      world := delivery.world
                                      custodyBacked := delivery.backed
                                      machine := current.runtime.machine
                                        |>.replaceOutputQueue replacement }
                                  lateRecipients := []
                                  receipts := current.receipts ++ binding.receipts ++
                                    delivery.receipts ++
                                    [.collected queueId.value binding.process.id]
                                  worldEffects := current.worldEffects ++
                                    delivery.worldEffects
                                  worldReplayExact := appendWorldReplay current
                                    delivery.worldEffects delivery.world.holdings
                                    delivery.replayExact }
  | current, .openCustody source basket =>
      let transfer : Transfer :=
        { source := proposal.possessionBindings.resolve source
          destination := current.runtime.machine.inventory
          basket }
      match MachineCustody.assessCustodyTransfer current.runtime.world
          current.runtime.custody transfer with
      | .rejected issues _ _ => .error (.transferRejected issues)
      | .accepted accepted =>
          let positionId := current.runtime.custody.nextId
          let transferAccepted := accepted.transferAccepted
          let world := applyTransferState transferAccepted
          let custody := current.runtime.custody.deposit transferAccepted rfl
          let custodyBacked := MachineCustody.backed_deposit
            current.runtime.custody current.runtime.custodyBacked transferAccepted rfl
          have activeCustodyHeld : current.runtime.machine.ActiveDependenciesSatisfy
              (ActiveCustodyDependency.HeldBy custody) :=
            current.runtime.activeCustodyHeld.deposit transferAccepted rfl
          .ok
            { current with
              runtime :=
                { current.runtime with
                  world, custody, custodyBacked, activeCustodyHeld }
              receipts := current.receipts ++
                [.transfer (transferReceipt transferAccepted),
                  .custodyOpened positionId]
              worldEffects := current.worldEffects ++
                [.transfer (transferReceipt transferAccepted)]
              worldReplayExact := appendWorldReplay current
                [.transfer (transferReceipt transferAccepted)] world.holdings
                (by exact replay_transferReceipt transferAccepted) }
  | current, .closeCustody position =>
      match proposal.custodyBindings.resolve position with
      | none => .error .custodyBindingMissing
      | some positionId =>
          match current.runtime.custody.position? positionId with
          | none => .error (.custodyPositionMissing positionId)
          | some held =>
              if inUse : positionId ∈
                  current.runtime.machine.activeCustodyPositionIds then
                .error (.custodyPositionInUse positionId)
              else
                let transfer : Transfer :=
                  { source := current.runtime.machine.inventory
                    destination := held.source
                    basket := held.basket }
                let custody := current.runtime.custody.remove positionId
                let releasedBacked := current.runtime.custodyBacked.remove positionId
                have activeCustodyHeld :
                    current.runtime.machine.ActiveDependenciesSatisfy
                      (ActiveCustodyDependency.HeldBy custody) :=
                  current.runtime.activeCustodyHeld.remove inUse
                match MachineCustody.assessCustodyTransfer current.runtime.world
                    custody transfer with
                | .rejected issues _ _ => .error (.transferRejected issues)
                | .accepted accepted =>
                    let transferAccepted := accepted.transferAccepted
                    let world := applyTransferState transferAccepted
                    let custodyBacked := releasedBacked.applyCustodyTransfer accepted
                    .ok
                      { current with
                        runtime :=
                          { current.runtime with
                            world, custody, custodyBacked, activeCustodyHeld }
                        receipts := current.receipts ++
                          [.transfer (transferReceipt transferAccepted),
                            .custodyClosed positionId]
                        worldEffects := current.worldEffects ++
                          [.transfer (transferReceipt transferAccepted)]
                        worldReplayExact := appendWorldReplay current
                          [.transfer (transferReceipt transferAccepted)] world.holdings
                          (by exact replay_transferReceipt transferAccepted) }
  | current, .releaseReservations source =>
      match proposal.queueBindings.resolve source with
      | none => .error (.queueBindingMissing .input)
      | some queueId =>
          match current.runtime.machine.inputQueue? queueId with
          | none => .error (.queueMissing .input queueId.value)
          | some queue =>
              match Queue.assessDequeue queue.contents with
              | .rejected issues _ _ => .error (.queueRejected .input issues)
              | .accepted accepted =>
                  let front := (Queue.dequeue queue.contents accepted).removed.value
                  match checkExpectedKind definition.processKind front.process.kind with
                  | .error issue => .error issue
                  | .ok _ =>
                      match releaseQueuedReservations current.runtime.custody
                          current.runtime.world current.runtime.custodyBacked
                          front.process front.consumedInputsComplete with
                      | .error issue => .error issue
                      | .ok released =>
                          let entry : InputQueueEntry schema queue.kind :=
                            { process := released.process
                              accepted := by
                                rw [QueuedProcess.kind, released.kindPreserved]
                                exact front.accepted
                              consumedInputsComplete := released.consumedComplete }
                          let replacement : MachineInputQueue schema :=
                            { queue with
                              contents := queue.contents.replaceFront accepted entry }
                          .ok
                            { current with
                              runtime :=
                                { current.runtime with
                                  world := released.world
                                  custodyBacked := released.backed
                                  machine := current.runtime.machine
                                    |>.replaceInputQueue replacement }
                              receipts := current.receipts ++ released.receipts
                              worldEffects := current.worldEffects ++
                                released.worldEffects
                              worldReplayExact := appendWorldReplay current
                                released.worldEffects released.world.holdings
                                released.replayExact }
  | current, .addInputQueue _ kind capacity =>
      let machine := current.runtime.machine
      if room : machine.queueCount < machine.maximumQueues then
        let queueId := machine.nextInputQueueId
        .ok
          { current with
            runtime :=
              { current.runtime with
                machine := machine.addInputQueue kind capacity room }
            receipts := current.receipts ++ [.queueAdded .input queueId] }
      else .error .machineQueueLimit
  | current, .removeInputQueue port =>
      match proposal.queueBindings.resolve port with
      | none => .error (.queueBindingMissing .input)
      | some queueId =>
          match current.runtime.machine.inputQueue? queueId with
          | none => .error (.queueMissing .input queueId.value)
          | some queue =>
              if queue.contents.entries = [] then
                .ok
                  { current with
                    runtime :=
                      { current.runtime with
                        machine := current.runtime.machine.removeInputQueue queueId }
                    receipts := current.receipts ++
                      [.queueRemoved .input queueId.value] }
              else .error (.queueNotEmpty .input)
  | current, .addProcessingQueue _ kind capacity =>
      let machine := current.runtime.machine
      if room : machine.queueCount < machine.maximumQueues then
        let queueId := machine.nextProcessingQueueId
        let machineAfter := machine.addProcessingQueue kind capacity room
        have activeCustodyHeld : machineAfter.ActiveDependenciesSatisfy
            (ActiveCustodyDependency.HeldBy current.runtime.custody) :=
          current.runtime.activeCustodyHeld.addProcessingQueue kind capacity room
        .ok
          { current with
            runtime :=
              { current.runtime with
                machine := machineAfter
                activeCustodyHeld }
            receipts := current.receipts ++ [.queueAdded .processing queueId] }
      else .error .machineQueueLimit
  | current, .removeProcessingQueue port =>
      match proposal.queueBindings.resolve port with
      | none => .error (.queueBindingMissing .processing)
      | some queueId =>
          match current.runtime.machine.processingQueue? queueId with
          | none => .error (.queueMissing .processing queueId.value)
          | some queue =>
              if queue.contents.entries = [] then
                let machine := current.runtime.machine.removeProcessingQueue queueId
                have activeCustodyHeld : machine.ActiveDependenciesSatisfy
                    (ActiveCustodyDependency.HeldBy current.runtime.custody) :=
                  current.runtime.activeCustodyHeld.removeProcessingQueue queueId
                .ok
                  { current with
                    runtime :=
                      { current.runtime with machine, activeCustodyHeld }
                    receipts := current.receipts ++
                      [.queueRemoved .processing queueId.value] }
              else .error (.queueNotEmpty .processing)
  | current, .addOutputQueue _ kind capacity =>
      let machine := current.runtime.machine
      if room : machine.queueCount < machine.maximumQueues then
        let queueId := machine.nextOutputQueueId
        .ok
          { current with
            runtime :=
              { current.runtime with
                machine := machine.addOutputQueue kind capacity room }
            receipts := current.receipts ++ [.queueAdded .output queueId] }
      else .error .machineQueueLimit
  | current, .removeOutputQueue port =>
      match proposal.queueBindings.resolve port with
      | none => .error (.queueBindingMissing .output)
      | some queueId =>
          match current.runtime.machine.outputQueue? queueId with
          | none => .error (.queueMissing .output queueId.value)
          | some queue =>
              if queue.contents.entries = [] then
                .ok
                  { current with
                    runtime :=
                      { current.runtime with
                        machine := current.runtime.machine.removeOutputQueue queueId }
                    receipts := current.receipts ++
                      [.queueRemoved .output queueId.value] }
              else .error (.queueNotEmpty .output)

private def applyEffects
    {resourceCatalog : ResourceCatalog}
    {schema : MachineSchema}
    {language : OperationLanguage schema}
    {worldOrigin : List (Holding AccountId)}
    (proposal : OperationProposal schema language)
    (definition : OperationDefinition schema language.QueuePort language.Guard) :
    EffectState resourceCatalog schema language worldOrigin →
    List (OperationEffect schema language.QueuePort) →
      Except SimulatorIssue
        (EffectState resourceCatalog schema language worldOrigin)
  | current, [] => .ok current
  | current, effect :: rest =>
      match applyEffect proposal definition current effect with
      | .error issue => .error issue
      | .ok after => applyEffects proposal definition after rest

def applyOperation
    {resourceCatalog : ResourceCatalog}
    {schema : MachineSchema}
    {language : OperationLanguage schema}
    (evaluateGuard : GuardEvaluator resourceCatalog schema language)
    (before : SimulatorState resourceCatalog schema language)
    (proposal : OperationProposal schema language) :
    Except (List SimulatorIssue) (AppliedOperation before proposal) := by
  letI : DecidableEq language.Mode := language.modeDecidableEq
  if modeMatches : before.mode = proposal.before then
    let definition := language.definition proposal.operation
    match assessOperationGuards evaluateGuard before definition.guards with
    | .rejected issues _ _ => exact .error [.guardRejected issues]
    | .accepted _ guardEvidence =>
      match assessOperationRequirements before.world proposal.possessionBindings
          definition.requirements with
      | .error failures => exact .error [.possessionRejected failures]
      | .ok possessionReceipts =>
          let initial : EffectState resourceCatalog schema language
              before.world.holdings :=
            { runtime := before
              pending := none
              lateRecipients := []
              receipts := []
              worldEffects := []
              worldReplayExact := rfl }
          match applyEffects proposal definition initial definition.effects with
          | .error issue => exact .error [issue]
          | .ok final =>
              match final.pending with
              | some _ => exact .error [.pendingProcessNotEnqueued]
              | none =>
                  let after : SimulatorState resourceCatalog schema language :=
                    { final.runtime with mode := proposal.after }
                  exact .ok
                    { after
                      checks :=
                        guardEvidence.map OperationCheckReceipt.guard ++
                          possessionReceipts.mapIdx fun requirementIndex receipt =>
                            OperationCheckReceipt.possession requirementIndex receipt
                      effects := final.receipts
                      worldEffects := final.worldEffects
                      worldReplayExact := final.worldReplayExact }
  else exact .error [.wrongMode]

/-- Exhaustive structured guard rejection occurs before effect interpretation. -/
theorem applyOperation_guardsRejected
    {resourceCatalog : ResourceCatalog}
    {schema : MachineSchema}
    {language : OperationLanguage schema}
    (evaluateGuard : GuardEvaluator resourceCatalog schema language)
    (before : SimulatorState resourceCatalog schema language)
    (proposal : OperationProposal schema language)
    (issues : List GuardIssue)
    (issuesExact :
      issues = operationGuardIssues evaluateGuard before
        (language.definition proposal.operation).guards)
    (nonempty : issues ≠ [])
    (modeMatches : before.mode = proposal.before)
    (guardsRejected :
      assessOperationGuards evaluateGuard before
          (language.definition proposal.operation).guards =
        .rejected issues issuesExact nonempty) :
    applyOperation evaluateGuard before proposal =
      .error [.guardRejected issues] := by
  simp [applyOperation, modeMatches, guardsRejected]

/-- Failed possession requirements reject before the effect interpreter runs. -/
theorem applyOperation_requirementsRejected
    {resourceCatalog : ResourceCatalog}
    {schema : MachineSchema}
    {language : OperationLanguage schema}
    (evaluateGuard : GuardEvaluator resourceCatalog schema language)
    (before : SimulatorState resourceCatalog schema language)
    (proposal : OperationProposal schema language)
    (failures : List PossessionFailure)
    (guardWitness : AcceptedOperationGuards evaluateGuard before
      (language.definition proposal.operation).guards)
    (guardEvidence : List GuardEvidence)
    (modeMatches : before.mode = proposal.before)
    (guardsAccepted :
      assessOperationGuards evaluateGuard before
          (language.definition proposal.operation).guards =
        .accepted guardWitness guardEvidence)
    (requirementsRejected :
      assessOperationRequirements before.world proposal.possessionBindings
        (language.definition proposal.operation).requirements = .error failures) :
    applyOperation evaluateGuard before proposal =
      .error [.possessionRejected failures] := by
  simp [applyOperation, modeMatches, guardsAccepted, requirementsRejected]

/-- An operation whose sole effect closes an actively used position is rejected
before custody or world state can be returned as a successor. -/
theorem applyOperation_closeCustodyInUse
    {resourceCatalog : ResourceCatalog}
    {schema : MachineSchema}
    {language : OperationLanguage schema}
    (evaluateGuard : GuardEvaluator resourceCatalog schema language)
    (before : SimulatorState resourceCatalog schema language)
    (proposal : OperationProposal schema language)
    (position : schema.Label)
    (positionId : Nat)
    (held : CustodyPosition)
    (possessionReceipts : List PossessionReceipt)
    (guardWitness : AcceptedOperationGuards evaluateGuard before
      (language.definition proposal.operation).guards)
    (guardEvidence : List GuardEvidence)
    (modeMatches : before.mode = proposal.before)
    (guardsAccepted :
      assessOperationGuards evaluateGuard before
          (language.definition proposal.operation).guards =
        .accepted guardWitness guardEvidence)
    (requirementsAccepted :
      assessOperationRequirements before.world proposal.possessionBindings
        (language.definition proposal.operation).requirements =
          .ok possessionReceipts)
    (effectsExact :
      (language.definition proposal.operation).effects = [.closeCustody position])
    (bindingExact : proposal.custodyBindings.resolve position = some positionId)
    (positionOpen : before.custody.position? positionId = some held)
    (positionInUse : positionId ∈ before.machine.activeCustodyPositionIds) :
    applyOperation evaluateGuard before proposal =
      .error [.custodyPositionInUse positionId] := by
  simp [applyOperation, modeMatches, guardsAccepted, requirementsAccepted,
    effectsExact, applyEffects, applyEffect, bindingExact, positionOpen,
    positionInUse]

def operationSuccessor
    {resourceCatalog : ResourceCatalog}
    {schema : MachineSchema}
    {language : OperationLanguage schema}
    (evaluateGuard : GuardEvaluator resourceCatalog schema language)
    (before : SimulatorState resourceCatalog schema language)
    (proposal : OperationProposal schema language) :
    Option (SimulatorState resourceCatalog schema language) :=
  match applyOperation evaluateGuard before proposal with
  | .error _ => none
  | .ok applied => some applied.after

/-- Rejected operation assessment exposes no successor state. -/
theorem operationSuccessor_rejected
    {resourceCatalog : ResourceCatalog}
    {schema : MachineSchema}
    {language : OperationLanguage schema}
    (evaluateGuard : GuardEvaluator resourceCatalog schema language)
    (before : SimulatorState resourceCatalog schema language)
    (proposal : OperationProposal schema language)
    (issues : List SimulatorIssue)
    (rejected : applyOperation evaluateGuard before proposal = .error issues) :
    operationSuccessor evaluateGuard before proposal = none := by
  simp [operationSuccessor, rejected]

/-- Output backpressure cannot expose a partially completed successor. -/
theorem operationSuccessor_outputBackpressure
    {resourceCatalog : ResourceCatalog}
    {schema : MachineSchema}
    {language : OperationLanguage schema}
    (evaluateGuard : GuardEvaluator resourceCatalog schema language)
    (before : SimulatorState resourceCatalog schema language)
    (proposal : OperationProposal schema language)
    (issues : List Queue.QueueIssue)
    (rejected : applyOperation evaluateGuard before proposal =
      .error [.queueRejected .output issues]) :
    operationSuccessor evaluateGuard before proposal = none :=
  operationSuccessor_rejected evaluateGuard before proposal _ rejected

/-! ## Deterministic trace execution and replay -/

def replayOperationReceipts
    {resourceCatalog : ResourceCatalog}
    {schema : MachineSchema}
    {language : OperationLanguage schema}
    (evaluateGuard : GuardEvaluator resourceCatalog schema language) :
    SimulatorState resourceCatalog schema language →
    List (OperationReceipt schema language) →
      Option (SimulatorState resourceCatalog schema language)
  | state, [] => some state
  | state, receipt :: rest =>
      match operationSuccessor evaluateGuard state receipt.proposal with
      | none => none
      | some after => replayOperationReceipts evaluateGuard after rest

structure AppliedOperationTrace
    {resourceCatalog : ResourceCatalog}
    {schema : MachineSchema}
    {language : OperationLanguage schema}
    (evaluateGuard : GuardEvaluator resourceCatalog schema language)
    (before : SimulatorState resourceCatalog schema language) where
  after : SimulatorState resourceCatalog schema language
  receipts : List (OperationReceipt schema language)
  replayExact : replayOperationReceipts evaluateGuard before receipts = some after
  directReceipts : List (DirectEffectReceipt schema language)
  directReplayExact :
    replayDirectEffectReceipts (SimulatorData.ofState before) directReceipts =
      SimulatorData.ofState after

def applyOperations
    {resourceCatalog : ResourceCatalog}
    {schema : MachineSchema}
    {language : OperationLanguage schema}
    (evaluateGuard : GuardEvaluator resourceCatalog schema language)
    (before : SimulatorState resourceCatalog schema language) :
    List (OperationProposal schema language) →
      Except (List SimulatorIssue)
        (AppliedOperationTrace evaluateGuard before)
  | [] =>
      .ok
        { after := before
          receipts := []
          replayExact := rfl
          directReceipts := []
          directReplayExact := rfl }
  | proposal :: rest =>
      match appliedEq : applyOperation evaluateGuard before proposal with
      | .error issues => .error issues
      | .ok applied =>
          match applyOperations evaluateGuard applied.after rest with
          | .error issues => .error issues
          | .ok suffix =>
              .ok
                { after := suffix.after
                  receipts := applied.receipt :: suffix.receipts
                  replayExact := by
                    simp only [replayOperationReceipts]
                    have successor :
                        operationSuccessor evaluateGuard before proposal =
                          some applied.after := by
                      simp [operationSuccessor, appliedEq]
                    change
                      (match operationSuccessor evaluateGuard before proposal with
                       | none => none
                       | some after => replayOperationReceipts evaluateGuard after
                           suffix.receipts) = some suffix.after
                    rw [successor]
                    exact suffix.replayExact
                  directReceipts := applied.directReceipt :: suffix.directReceipts
                  directReplayExact := by
                    change replayDirectEffectReceipts
                        (replayDirectEffectReceipt (SimulatorData.ofState before)
                          applied.directReceipt) suffix.directReceipts =
                      SimulatorData.ofState suffix.after
                    rw [applied.replayDirect_exact]
                    exact suffix.directReplayExact }

/-- A trace exposes its final state only when every operation succeeds. -/
def operationTraceSuccessor
    {resourceCatalog : ResourceCatalog}
    {schema : MachineSchema}
    {language : OperationLanguage schema}
    (evaluateGuard : GuardEvaluator resourceCatalog schema language)
    (before : SimulatorState resourceCatalog schema language)
    (proposals : List (OperationProposal schema language)) :
    Option (SimulatorState resourceCatalog schema language) :=
  match applyOperations evaluateGuard before proposals with
  | .error _ => none
  | .ok applied => some applied.after

/-- Rejection at any trace suffix discards every locally computed prefix. -/
theorem operationTraceSuccessor_rejected
    {resourceCatalog : ResourceCatalog}
    {schema : MachineSchema}
    {language : OperationLanguage schema}
    (evaluateGuard : GuardEvaluator resourceCatalog schema language)
    (before : SimulatorState resourceCatalog schema language)
    (proposals : List (OperationProposal schema language))
    (issues : List SimulatorIssue)
    (rejected : applyOperations evaluateGuard before proposals = .error issues) :
    operationTraceSuccessor evaluateGuard before proposals = none := by
  simp [operationTraceSuccessor, rejected]

end Maquina
