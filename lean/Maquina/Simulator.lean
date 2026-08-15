import Maquina.Operation
import Maquina.Transformation

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
  nextProcessId : Nat

inductive SimulatorIssue where
  | wrongMode
  | guardRejected
  | missingProcessKind
  | missingProcessBindings
  | pendingProcessAlreadyExists
  | pendingProcessMissing
  | pendingProcessNotEnqueued
  | queueBindingMissing (stage : QueueStage)
  | queueMissing (stage : QueueStage) (id : Nat)
  | queueRejected (stage : QueueStage) (issues : List Queue.QueueIssue)
  | queueRejectsProcess (stage : QueueStage)
  | processKindMismatch
  | transferRejected (issues : List TransferIssue)
  | transformationRejected (issues : List InventoryDeltaIssue)
  | insufficientWork (required actual : Nat)
  | recipientBindingMissing
  | recipientAlreadyBound
  | outputLabelMissing
  | outputRecipientMissing
  | machineQueueLimit
  | queueNotEmpty (stage : QueueStage)
  | unsupportedEffect
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

private structure ReservationRun
    (resourceCatalog : ResourceCatalog)
    (Label : Type) where
  world : WorldState resourceCatalog
  reservations : List (Reservation Label)
  receipts : List SimulatorEffectReceipt

private def reservePorts
    {resourceCatalog : ResourceCatalog}
    {Label : Type}
    (bindings : ProcessBindings Label)
    (use : ProcessInputUse) :
    WorldState resourceCatalog →
    List (ProcessPort Label) →
      Except SimulatorIssue (ReservationRun resourceCatalog Label)
  | world, [] =>
      .ok { world, reservations := [], receipts := [] }
  | world, port :: rest =>
      let proposal : Transfer :=
        { source := bindings.source port.label
          destination := bindings.custody port.label
          basket := port.basket }
      match assessTransfer world proposal with
      | .rejected issues _ _ => .error (.transferRejected issues)
      | .accepted accepted =>
          let after := applyTransferState accepted
          match reservePorts bindings use after rest with
          | .error issue => .error issue
          | .ok suffix =>
              .ok
                { world := suffix.world
                  reservations :=
                    Reservation.ofAccepted use port.label accepted ::
                      suffix.reservations
                  receipts :=
                    .transfer (transferReceipt accepted) :: suffix.receipts }

private def reserveProcess
    {resourceCatalog : ResourceCatalog}
    {Label : Type}
    (world : WorldState resourceCatalog)
    (process : Process Label)
    (bindings : ProcessBindings Label) :
    Except SimulatorIssue (ReservationRun resourceCatalog Label) :=
  match reservePorts bindings .consumed world process.consumed with
  | .error issue => .error issue
  | .ok consumed =>
      match reservePorts bindings .reserved consumed.world process.reserved with
      | .error issue => .error issue
      | .ok reserved =>
          .ok
            { world := reserved.world
              reservations := consumed.reservations ++ reserved.reservations
              receipts := consumed.receipts ++ reserved.receipts }

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

private def returnReservations
    {resourceCatalog : ResourceCatalog}
    {Label : Type} :
    WorldState resourceCatalog →
    List (Reservation Label) →
      Except SimulatorIssue
        (WorldState resourceCatalog × List SimulatorEffectReceipt)
  | world, [] => .ok (world, [])
  | world, reservation :: rest =>
      if reservation.use = .reserved then
        let proposal : Transfer :=
          { source := reservation.custody
            destination := reservation.source
            basket := reservation.basket }
        match assessTransfer world proposal with
        | .rejected issues _ _ => .error (.transferRejected issues)
        | .accepted accepted =>
            let after := applyTransferState accepted
            match returnReservations after rest with
            | .error issue => .error issue
            | .ok (final, receipts) =>
                .ok (final, .transfer (transferReceipt accepted) :: receipts)
      else
        returnReservations world rest

private structure ProcessCompletion
    (resourceCatalog : ResourceCatalog)
    {schema : MachineSchema}
    (before : QueuedProcess schema) where
  world : WorldState resourceCatalog
  process : QueuedProcess schema
  kindPreserved : process.processKind = before.processKind
  receipts : List SimulatorEffectReceipt

private def completeInventory
    {resourceCatalog : ResourceCatalog}
    {schema : MachineSchema}
    (world : WorldState resourceCatalog)
    (process : QueuedProcess schema) :
    Except SimulatorIssue (ProcessCompletion resourceCatalog process) :=
  match applyInventoryProgram world (completionDeltas process) with
  | .error issues => .error (.transformationRejected issues)
  | .ok transformed =>
      match returnReservations transformed.after process.reservations with
      | .error issue => .error issue
      | .ok (after, returned) =>
          .ok
            { world := after
              process := { process with reservations := [] }
              kindPreserved := rfl
              receipts :=
                transformed.receipts.map SimulatorEffectReceipt.transformation ++
                  returned }

private structure ReservationRelease
    (resourceCatalog : ResourceCatalog)
    {schema : MachineSchema}
    (before : QueuedProcess schema) where
  world : WorldState resourceCatalog
  process : QueuedProcess schema
  kindPreserved : process.processKind = before.processKind
  receipts : List SimulatorEffectReceipt

private def releaseQueuedReservations
    {resourceCatalog : ResourceCatalog}
    {schema : MachineSchema}
    (world : WorldState resourceCatalog)
    (process : QueuedProcess schema) :
    Except SimulatorIssue
      (ReservationRelease resourceCatalog process) :=
  match returnReservations world process.reservations with
  | .error issue => .error issue
  | .ok (after, receipts) =>
      let remaining := process.reservations.filter fun reservation =>
        decide (reservation.use ≠ .reserved)
      .ok
        { world := after
          process := { process with reservations := remaining }
          kindPreserved := rfl
          receipts := receipts ++ [.reservationsReleased process.id] }

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
    {Label : Type} :
    WorldState resourceCatalog →
    List (OutputAllocation Label) →
      Except SimulatorIssue
        (WorldState resourceCatalog × List SimulatorEffectReceipt)
  | world, [] => .ok (world, [])
  | world, allocation :: rest =>
      match allocation.recipient with
      | none => .error .outputRecipientMissing
      | some recipient =>
          if _same : allocation.custody = recipient then
            deliverAllocations world rest
          else
            let proposal : Transfer :=
              { source := allocation.custody
                destination := recipient
                basket := allocation.basket }
            match assessTransfer world proposal with
            | .rejected issues _ _ => .error (.transferRejected issues)
            | .accepted accepted =>
                let after := applyTransferState accepted
                match deliverAllocations after rest with
                | .error issue => .error issue
                | .ok (final, receipts) =>
                    .ok
                      (final,
                        .transfer (transferReceipt accepted) :: receipts)

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
  | current, .reserveProcessInputs =>
      match current.pending with
      | some _ => .error .pendingProcessAlreadyExists
      | none =>
          match definition.processKind, proposal.processBindings with
          | none, _ => .error .missingProcessKind
          | _, none => .error .missingProcessBindings
          | some kind, some bindings =>
              match reserveProcess current.runtime.world
                  (schema.process kind) bindings with
              | .error issue => .error issue
              | .ok reserved =>
                  let queued : QueuedProcess schema :=
                    { id := current.runtime.nextProcessId
                      processKind := kind
                      bindings := bindings
                      reservations := reserved.reservations }
                  .ok
                    { current with
                      runtime :=
                        { current.runtime with
                          world := reserved.world
                          nextProcessId := current.runtime.nextProcessId + 1 }
                      pending := some queued
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
                  letI := schema.acceptsInputDecidable queue.kind process.kind
                  if accepts : schema.acceptsInput queue.kind process.kind then
                    match Queue.assessEnqueue queue.contents with
                    | .rejected issues _ _ => .error (.queueRejected .input issues)
                    | .accepted accepted =>
                        let entry : InputQueueEntry schema queue.kind :=
                          { process, accepted := accepts }
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
                              { process := active, accepted := accepts }
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
                        { process := advanced, accepted := front.accepted }
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
                              match completeInventory current.runtime.world
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
                        match completeInventory current.runtime.world active.queued with
                        | .error issue => .error issue
                        | .ok inventory =>
                            let completed : CompletedProcess schema :=
                              { active := { active with queued := inventory.process } }
                            match deliverAllocations inventory.world
                                completed.outputAllocations with
                            | .error issue => .error issue
                            | .ok (world, deliveryReceipts) =>
                                let replacement : MachineProcessingQueue schema :=
                                  { processingQueue with contents := removed.queue }
                                .ok
                                  { current with
                                    runtime :=
                                      { current.runtime with
                                        world
                                        machine := current.runtime.machine
                                          |>.replaceProcessingQueue replacement }
                                    receipts := current.receipts ++
                                      inventory.receipts ++ deliveryReceipts ++
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
                          match deliverAllocations current.runtime.world
                              rebound.outputAllocations with
                          | .error issue => .error issue
                          | .ok (world, deliveryReceipts) =>
                              let replacement : MachineOutputQueue schema :=
                                { queue with contents := removed.queue }
                              .ok
                                { current with
                                  runtime :=
                                    { current.runtime with
                                      world
                                      machine := current.runtime.machine
                                        |>.replaceOutputQueue replacement }
                                  lateRecipients := []
                                  receipts := current.receipts ++ bindingReceipts ++
                                    deliveryReceipts ++
                                    [.collected queueId.value queued.id] }
  | current, .releaseReservations (stage := stage) source =>
      match stage with
      | .input =>
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
                          match releaseQueuedReservations current.runtime.world
                              front.process with
                          | .error issue => .error issue
                          | .ok released =>
                              let entry : InputQueueEntry schema queue.kind :=
                                { process := released.process
                                  accepted := by
                                    rw [QueuedProcess.kind, released.kindPreserved]
                                    exact front.accepted }
                              let replacement : MachineInputQueue schema :=
                                { queue with
                                  contents := queue.contents.replaceFront accepted entry }
                              .ok
                                { current with
                                  runtime :=
                                    { current.runtime with
                                      world := released.world
                                      machine := current.runtime.machine
                                        |>.replaceInputQueue replacement }
                                  receipts := current.receipts ++ released.receipts }
      | .processing =>
          match proposal.queueBindings.resolve source with
          | none => .error (.queueBindingMissing .processing)
          | some queueId =>
              match current.runtime.machine.processingQueue? queueId with
              | none => .error (.queueMissing .processing queueId.value)
              | some queue =>
                  match Queue.assessDequeue queue.contents with
                  | .rejected issues _ _ =>
                      .error (.queueRejected .processing issues)
                  | .accepted accepted =>
                      let front := (Queue.dequeue queue.contents accepted).removed.value
                      match checkExpectedKind definition.processKind front.process.kind with
                      | .error issue => .error issue
                      | .ok _ =>
                          match releaseQueuedReservations current.runtime.world
                              front.process.queued with
                          | .error issue => .error issue
                          | .ok released =>
                              let process : ActiveProcess schema :=
                                { front.process with queued := released.process }
                              let entry : ProcessingQueueEntry schema queue.kind :=
                                { process
                                  accepted := by
                                    rw [ActiveProcess.kind, QueuedProcess.kind,
                                      released.kindPreserved]
                                    exact front.accepted }
                              let replacement : MachineProcessingQueue schema :=
                                { queue with
                                  contents := queue.contents.replaceFront accepted entry }
                              .ok
                                { current with
                                  runtime :=
                                    { current.runtime with
                                      world := released.world
                                      machine := current.runtime.machine
                                        |>.replaceProcessingQueue replacement }
                                  receipts := current.receipts ++ released.receipts }
      | .output =>
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
                          match releaseQueuedReservations current.runtime.world
                              front.process.active.queued with
                          | .error issue => .error issue
                          | .ok released =>
                              let active : ActiveProcess schema :=
                                { front.process.active with queued := released.process }
                              let process : CompletedProcess schema := { active }
                              let entry : OutputQueueEntry schema queue.kind :=
                                { process
                                  accepted := by
                                    rw [CompletedProcess.kind, ActiveProcess.kind,
                                      QueuedProcess.kind, released.kindPreserved]
                                    exact front.accepted }
                              let replacement : MachineOutputQueue schema :=
                                { queue with
                                  contents := queue.contents.replaceFront accepted entry }
                              .ok
                                { current with
                                  runtime :=
                                    { current.runtime with
                                      world := released.world
                                      machine := current.runtime.machine
                                        |>.replaceOutputQueue replacement }
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
      let initial : EffectState resourceCatalog schema language :=
        { runtime := before
          pending := none
          lateRecipients := []
          receipts := [] }
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
