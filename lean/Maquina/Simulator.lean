import Maquina.CustodyTransformation
import Maquina.Operation

/-!
# Maquina Generic Simulator

The simulator interprets generic operation effects. It has no knowledge of
game modes, process names, participant labels, or resource meanings.
-/

namespace Maquina

structure SimulatorState
    (resourceCatalog : ResourceCatalog)
    (schema : MachineSchema)
    (language : OperationLanguage schema) where
  world : WorldState resourceCatalog
  mode : language.Mode
  machine : Machine schema
  custody : MachineCustody machine.inventory
  custodyBacked : MachineCustody.Backed world custody
  nextProcessId : Nat

inductive SimulatorIssue where
  | wrongMode
  | guardRejected
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
  | custodyPositionMissing (id : Nat)
  | outputLabelMissing
  | outputRecipientMissing
  | machineQueueLimit
  | queueNotEmpty (stage : QueueStage)
  deriving DecidableEq, Repr

inductive SimulatorEffectReceipt where
  | possession (receipt : PossessionReceipt)
  | transfer (receipt : TransferReceipt)
  | transformation (receipt : InventoryDeltaReceipt)
  | enqueued (queueId ticket processId : Nat)
  | dispatched (inputQueueId processingQueueId processId : Nat)
  | advanced (queueId processId before after : Nat)
  | completed (processingQueueId : Nat) (outputQueueId : Option Nat)
      (processId : Nat)
  | recipientBound (account : AccountId)
  | collected (queueId processId : Nat)
  | custodyOpened (positionId : Nat)
  | custodyClosed (positionId : Nat)
  | reservationsReleased (processId : Nat)
  | queueAdded (stage : QueueStage) (queueId : Nat)
  | queueRemoved (stage : QueueStage) (queueId : Nat)
  deriving Repr

structure OperationReceipt
    (schema : MachineSchema)
    (language : OperationLanguage schema) where
  proposal : OperationProposal schema language
  effects : List SimulatorEffectReceipt

structure AppliedOperation
    {resourceCatalog : ResourceCatalog}
    {schema : MachineSchema}
    {language : OperationLanguage schema}
    (before : SimulatorState resourceCatalog schema language)
    (proposal : OperationProposal schema language) where
  after : SimulatorState resourceCatalog schema language
  effects : List SimulatorEffectReceipt

namespace AppliedOperation

def receipt
    {resourceCatalog : ResourceCatalog}
    {schema : MachineSchema}
    {language : OperationLanguage schema}
    {before : SimulatorState resourceCatalog schema language}
    {proposal : OperationProposal schema language}
    (applied : AppliedOperation before proposal) : OperationReceipt schema language :=
  { proposal, effects := applied.effects }

end AppliedOperation

abbrev GuardEvaluator
    (resourceCatalog : ResourceCatalog)
    (schema : MachineSchema)
    (language : OperationLanguage schema) :=
  language.Guard → SimulatorState resourceCatalog schema language → Bool

private def assessOperationRequirements
    {resourceCatalog : ResourceCatalog}
    {Label : Type}
    (world : WorldState resourceCatalog)
    (bindings : PossessionBindings Label) :
    List (PossessionPort Label) →
      Except (List PossessionFailure) (List PossessionReceipt)
  | [] => .ok []
  | port :: rest =>
      let requirement : PossessionRequirement :=
        { account := bindings.resolve port.label
          basket := port.basket }
      let current := assessPossession world requirement
      let suffix := assessOperationRequirements world bindings rest
      match current, suffix with
      | .accepted accepted, .ok receipts =>
          .ok (possessionReceipt accepted :: receipts)
      | .accepted _, .error failures => .error failures
      | .rejected issues _ _, .ok _ =>
          .error [{ account := requirement.account, issues }]
      | .rejected issues _ _, .error failures =>
          .error ({ account := requirement.account, issues } :: failures)

private structure ReservationRun
    (resourceCatalog : ResourceCatalog)
    {Label : Type}
    (bindings : ProcessBindings Label)
    (use : ProcessInputUse)
    (ports : List (ProcessPort Label))
    {inventory : AccountId}
    (custody : MachineCustody inventory) where
  world : WorldState resourceCatalog
  backed : MachineCustody.Backed world custody
  reservations : List (Reservation Label)
  receipts : List SimulatorEffectReceipt
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
        (ReservationRun resourceCatalog bindings use ports custody)
  | world, backed, [] =>
      .ok
        { world
          backed
          reservations := []
          receipts := []
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
    (custody : MachineCustody inventory) where
  world : WorldState resourceCatalog
  backed : MachineCustody.Backed world custody
  reservations : List (Reservation Label)
  receipts : List SimulatorEffectReceipt
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
    (run : ReservationRun resourceCatalog bindings .consumed process.consumed
      custody) :
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
    (run : ReservationRun resourceCatalog bindings .reserved process.reserved
      custody) :
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
      (ProcessReservationRun resourceCatalog process bindings custody) :=
  match reservePorts bindings .consumed custody world backed process.consumed with
  | .error issue => .error issue
  | .ok consumed =>
      .ok
        { world := consumed.world
          backed := consumed.backed
          reservations := consumed.reservations
          receipts := consumed.receipts
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
      (ProcessReservationRun resourceCatalog process bindings custody) :=
  match reservePorts bindings .reserved custody world backed process.reserved with
  | .error issue => .error issue
  | .ok reserved =>
      .ok
        { world := reserved.world
          backed := reserved.backed
          reservations := reserved.reservations
          receipts := reserved.receipts
          reservationsValid := reserved.reservedValid
          consumedComplete := .missing
          reservedComplete := .complete (by
            intro port portMem
            exact reserved.portsCovered port portMem) }

private def completionDeltas
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

private structure BackedWorldRun
    (resourceCatalog : ResourceCatalog)
    {inventory : AccountId}
    (custody : MachineCustody inventory) where
  world : WorldState resourceCatalog
  backed : MachineCustody.Backed world custody
  receipts : List SimulatorEffectReceipt

private def returnReservations
    {resourceCatalog : ResourceCatalog}
    {Label : Type}
    {inventory : AccountId}
    (custody : MachineCustody inventory) :
    (world : WorldState resourceCatalog) →
    MachineCustody.Backed world custody →
    List (Reservation Label) →
      Except SimulatorIssue
        (BackedWorldRun resourceCatalog custody)
  | world, backed, [] => .ok { world, backed, receipts := [] }
  | world, backed, reservation :: rest =>
      if reservation.use = .reserved then
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
                        suffix.receipts }
      else
        returnReservations custody world backed rest

private structure ProcessCompletion
    (resourceCatalog : ResourceCatalog)
    {schema : MachineSchema}
    (before : QueuedProcess schema)
    {inventory : AccountId}
    (custody : MachineCustody inventory) where
  world : WorldState resourceCatalog
  backed : MachineCustody.Backed world custody
  process : QueuedProcess schema
  kindPreserved : process.processKind = before.processKind
  receipts : List SimulatorEffectReceipt

private def completeInventory
    {resourceCatalog : ResourceCatalog}
    {schema : MachineSchema}
    {inventory : AccountId}
    (custody : MachineCustody inventory)
    (world : WorldState resourceCatalog)
    (backed : MachineCustody.Backed world custody)
    (process : QueuedProcess schema) :
    Except SimulatorIssue (ProcessCompletion resourceCatalog process custody) :=
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
              receipts :=
                transformed.receipts.map SimulatorEffectReceipt.transformation ++
                  returned.receipts }

private structure ReservationRelease
    (resourceCatalog : ResourceCatalog)
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
      (ReservationRelease resourceCatalog process custody) :=
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
          receipts := returned.receipts ++ [.reservationsReleased process.id] }

private def bindLateRecipients
    {schema : MachineSchema}
    (late : List (schema.Label × AccountId))
    (process : QueuedProcess schema) :
    Except SimulatorIssue (QueuedProcess schema × List SimulatorEffectReceipt) := by
  letI : DecidableEq schema.Label := schema.labelDecidableEq
  match late with
  | [] => exact .ok (process, [])
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
              | .ok (final, receipts) =>
                  exact .ok (final, .recipientBound account :: receipts)

private def deliverAllocations
    {resourceCatalog : ResourceCatalog}
    {Label : Type}
    {inventory : AccountId}
    (custody : MachineCustody inventory) :
    (world : WorldState resourceCatalog) →
    MachineCustody.Backed world custody →
    List (OutputAllocation Label) →
      Except SimulatorIssue
        (BackedWorldRun resourceCatalog custody)
  | world, backed, [] => .ok { world, backed, receipts := [] }
  | world, backed, allocation :: rest =>
      match allocation.recipient with
      | none => .error .outputRecipientMissing
      | some recipient =>
          if _same : allocation.custody = recipient then
            deliverAllocations custody world backed rest
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
                            suffix.receipts }

private structure EffectState
    (resourceCatalog : ResourceCatalog)
    (schema : MachineSchema)
    (language : OperationLanguage schema) where
  runtime : SimulatorState resourceCatalog schema language
  pending : Option (QueuedProcess schema)
  lateRecipients : List (schema.Label × AccountId)
  receipts : List SimulatorEffectReceipt

private def checkExpectedKind
    {schema : MachineSchema}
    (expected : Option schema.ProcessKind)
    (actual : schema.ProcessKind) : Except SimulatorIssue Unit := by
  letI : DecidableEq schema.ProcessKind := schema.processKindDecidableEq
  match expected with
  | none => exact .ok ()
  | some kind =>
      if kind = actual then exact .ok () else exact .error .processKindMismatch

private def applyEffect
    {resourceCatalog : ResourceCatalog}
    {schema : MachineSchema}
    {language : OperationLanguage schema}
    (proposal : OperationProposal schema language)
    (definition : OperationDefinition schema language.QueuePort language.Guard) :
    EffectState resourceCatalog schema language →
    OperationEffect schema language.QueuePort →
      Except SimulatorIssue (EffectState resourceCatalog schema language)
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
                      receipts := current.receipts ++ reserved.receipts }
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
                                receipts := current.receipts ++ reserved.receipts }
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
          match current.runtime.machine.inputQueue? inputId,
              current.runtime.machine.processingQueue? processingId with
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
                            match Queue.assessEnqueue processingQueue.contents with
                            | .rejected issues _ _ =>
                                .error (.queueRejected .processing issues)
                            | .accepted acceptedEnqueue =>
                                let active : ActiveProcess schema :=
                                  { queued := process, progress := 0 }
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
                                let machine :=
                                  (current.runtime.machine.replaceInputQueue
                                    inputReplacement).replaceProcessingQueue
                                      processingReplacement
                                .ok
                                  { current with
                                    runtime := { current.runtime with machine }
                                    receipts := current.receipts ++
                                      [.dispatched inputId.value processingId.value
                                        process.id] }
                          else .error (.queueRejectsProcess .processing)
  | current, .advance source work _ =>
      match proposal.queueBindings.resolve source with
      | none => .error (.queueBindingMissing .processing)
      | some queueId =>
          match current.runtime.machine.processingQueue? queueId with
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
                      .ok
                        { current with
                          runtime :=
                            { current.runtime with
                              machine := current.runtime.machine.replaceProcessingQueue
                                replacement }
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
          match current.runtime.machine.processingQueue? processingId,
              current.runtime.machine.outputQueue? outputId with
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
                                    { active with queued := inventory.process }
                                  let completed : CompletedProcess schema :=
                                    { active := completedActive }
                                  let entry : OutputQueueEntry schema outputQueue.kind :=
                                    { process := completed
                                      accepted := by
                                        rw [CompletedProcess.kind, ActiveProcess.kind,
                                          QueuedProcess.kind, inventory.kindPreserved]
                                        exact accepts }
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
                                  .ok
                                    { current with
                                      runtime :=
                                        { current.runtime with
                                          world := inventory.world
                                          custodyBacked := inventory.backed
                                          machine }
                                      receipts := current.receipts ++ inventory.receipts ++
                                        [.completed processingId.value
                                          (some outputId.value) active.queued.id] }
                        else .error (.queueRejectsProcess .output)
                      else .error (.insufficientWork required active.progress)
  | current, .completeToInventories source =>
      match proposal.queueBindings.resolve source with
      | none => .error (.queueBindingMissing .processing)
      | some processingId =>
          match current.runtime.machine.processingQueue? processingId with
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
                            let completed : CompletedProcess schema :=
                              { active := { active with queued := inventory.process } }
                            match deliverAllocations current.runtime.custody
                                inventory.world inventory.backed
                                completed.outputAllocations with
                            | .error issue => .error issue
                            | .ok delivery =>
                                let replacement : MachineProcessingQueue schema :=
                                  { processingQueue with contents := removed.queue }
                                .ok
                                  { current with
                                    runtime :=
                                      { current.runtime with
                                        world := delivery.world
                                        custodyBacked := delivery.backed
                                        machine := current.runtime.machine
                                          |>.replaceProcessingQueue replacement }
                                    receipts := current.receipts ++
                                      inventory.receipts ++ delivery.receipts ++
                                      [.completed processingId.value none
                                        active.queued.id] }
                      else .error (.insufficientWork required active.progress)
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
                  let completed := removed.removed.value.process
                  match checkExpectedKind definition.processKind completed.kind with
                  | .error issue => .error issue
                  | .ok _ =>
                      match bindLateRecipients current.lateRecipients
                          completed.active.queued with
                      | .error issue => .error issue
                      | .ok (queued, bindingReceipts) =>
                          let rebound : CompletedProcess schema :=
                            { active := { completed.active with queued } }
                          match deliverAllocations current.runtime.custody
                              current.runtime.world current.runtime.custodyBacked
                              rebound.outputAllocations with
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
                                  receipts := current.receipts ++ bindingReceipts ++
                                    delivery.receipts ++
                                    [.collected queueId.value queued.id] }
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
          .ok
            { current with
              runtime := { current.runtime with world, custody, custodyBacked }
              receipts := current.receipts ++
                [.transfer (transferReceipt transferAccepted),
                  .custodyOpened positionId] }
  | current, .closeCustody position =>
      match proposal.custodyBindings.resolve position with
      | none => .error .custodyBindingMissing
      | some positionId =>
          match current.runtime.custody.position? positionId with
          | none => .error (.custodyPositionMissing positionId)
          | some held =>
              let transfer : Transfer :=
                { source := current.runtime.machine.inventory
                  destination := held.source
                  basket := held.basket }
              let custody := current.runtime.custody.remove positionId
              let releasedBacked := current.runtime.custodyBacked.remove positionId
              match MachineCustody.assessCustodyTransfer current.runtime.world
                  custody transfer with
              | .rejected issues _ _ => .error (.transferRejected issues)
              | .accepted accepted =>
                  let transferAccepted := accepted.transferAccepted
                  let world := applyTransferState transferAccepted
                  let custodyBacked := releasedBacked.applyCustodyTransfer accepted
                  .ok
                    { current with
                      runtime := { current.runtime with world, custody, custodyBacked }
                      receipts := current.receipts ++
                        [.transfer (transferReceipt transferAccepted),
                          .custodyClosed positionId] }
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
                              receipts := current.receipts ++ released.receipts }
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
        .ok
          { current with
            runtime :=
              { current.runtime with
                machine := machine.addProcessingQueue kind capacity room }
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
                .ok
                  { current with
                    runtime :=
                      { current.runtime with
                        machine := current.runtime.machine.removeProcessingQueue queueId }
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
    (proposal : OperationProposal schema language)
    (definition : OperationDefinition schema language.QueuePort language.Guard) :
    EffectState resourceCatalog schema language →
    List (OperationEffect schema language.QueuePort) →
      Except SimulatorIssue (EffectState resourceCatalog schema language)
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
    if guardsHold : definition.guards.all fun guard => evaluateGuard guard before then
      match assessOperationRequirements before.world proposal.possessionBindings
          definition.requirements with
      | .error failures => exact .error [.possessionRejected failures]
      | .ok possessionReceipts =>
          let initial : EffectState resourceCatalog schema language :=
            { runtime := before
              pending := none
              lateRecipients := []
              receipts := possessionReceipts.map SimulatorEffectReceipt.possession }
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
                      effects := final.receipts }
    else exact .error [.guardRejected]
  else exact .error [.wrongMode]

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
      .ok { after := before, receipts := [], replayExact := rfl }
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
                    exact suffix.replayExact }

end Maquina
