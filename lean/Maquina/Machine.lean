import Maquina.Process
import Maquina.Queue

/-!
# Maquina Machines

Machines own one inventory account and a dynamically sized, direction-typed
queue topology bounded by a machine-wide maximum.
-/

namespace Maquina

inductive QueueStage where
  | input
  | processing
  | output
  deriving DecidableEq, Repr

/-- Queue identities of different stages are different Lean types. -/
structure MachineQueueId (stage : QueueStage) where
  value : Nat
  deriving DecidableEq, Repr

/-- A game supplies its process, label, queue-kind, and acceptance vocabulary. -/
structure MachineSchema where
  ProcessKind : Type
  Label : Type
  InputQueueKind : Type
  ProcessingQueueKind : Type
  OutputQueueKind : Type

  processKindDecidableEq : DecidableEq ProcessKind
  labelDecidableEq : DecidableEq Label

  acceptsInput : InputQueueKind → ProcessKind → Prop
  acceptsProcessing : ProcessingQueueKind → ProcessKind → Prop
  acceptsOutput : OutputQueueKind → ProcessKind → Prop

  process : ProcessKind → Process Label

  acceptsInputDecidable :
    ∀ queueKind processKind, Decidable (acceptsInput queueKind processKind)
  acceptsProcessingDecidable :
    ∀ queueKind processKind, Decidable (acceptsProcessing queueKind processKind)
  acceptsOutputDecidable :
    ∀ queueKind processKind, Decidable (acceptsOutput queueKind processKind)

/-- A live reservation must belong to the canonical process and its bindings. -/
def ReservationValidFor
    (process : Process Label)
    (bindings : ProcessBindings Label)
    (reservation : Reservation Label) : Prop :=
  reservation.source = bindings.source reservation.label ∧
  reservation.custody = bindings.custody reservation.label ∧
  match reservation.use with
  | .consumed =>
      ∃ port ∈ process.consumed,
        reservation.label = port.label ∧ reservation.basket = port.basket
  | .reserved =>
      ∃ port ∈ process.reserved,
        reservation.label = port.label ∧ reservation.basket = port.basket

def ReservationsValid
    (process : Process Label)
    (bindings : ProcessBindings Label)
    (reservations : List (Reservation Label)) : Prop :=
  ∀ reservation, reservation ∈ reservations →
    ReservationValidFor process bindings reservation

/-- An admitted invocation waiting to be dispatched. -/
structure QueuedProcess (schema : MachineSchema) where
  id : Nat
  processKind : schema.ProcessKind
  bindings : ProcessBindings schema.Label
  reservations : List (Reservation schema.Label)
  reservationsValid :
    ReservationsValid (schema.process processKind) bindings reservations

namespace QueuedProcess

def kind (process : QueuedProcess schema) : schema.ProcessKind :=
  process.processKind

def invocation
    (process : QueuedProcess schema) :
    ProcessInvocation schema.ProcessKind schema.Label where
  kind := process.processKind
  process := schema.process process.processKind
  bindings := process.bindings

end QueuedProcess

/-- A process currently occupying processing capacity. -/
structure ActiveProcess (schema : MachineSchema) where
  queued : QueuedProcess schema
  progress : Nat

namespace ActiveProcess

def kind (process : ActiveProcess schema) : schema.ProcessKind :=
  process.queued.kind

end ActiveProcess

/-- A process whose declared work and transformation have completed. -/
structure CompletedProcess (schema : MachineSchema) where
  active : ActiveProcess schema

namespace CompletedProcess

def kind (process : CompletedProcess schema) : schema.ProcessKind :=
  process.active.kind

/-- Canonical produced amounts paired with their staged destinations. -/
def outputAllocations
    (process : CompletedProcess schema) :
    List (OutputAllocation schema.Label) :=
  process.active.queued.invocation.outputAllocations

end CompletedProcess

/-! ## Queue entries carry their routing acceptance proof -/

structure InputQueueEntry
    (schema : MachineSchema)
    (queueKind : schema.InputQueueKind) where
  process : QueuedProcess schema
  accepted : schema.acceptsInput queueKind process.kind

structure ProcessingQueueEntry
    (schema : MachineSchema)
    (queueKind : schema.ProcessingQueueKind) where
  process : ActiveProcess schema
  accepted : schema.acceptsProcessing queueKind process.kind

structure OutputQueueEntry
    (schema : MachineSchema)
    (queueKind : schema.OutputQueueKind) where
  process : CompletedProcess schema
  accepted : schema.acceptsOutput queueKind process.kind

/-! ## Direction-specific queues -/

structure MachineInputQueue (schema : MachineSchema) where
  id : MachineQueueId .input
  kind : schema.InputQueueKind
  contents : Queue (InputQueueEntry schema kind)

namespace MachineInputQueue

def empty
    (id : MachineQueueId .input)
    (kind : schema.InputQueueKind)
    (capacity : Option Nat := none) : MachineInputQueue schema where
  id := id
  kind := kind
  contents := Queue.empty capacity

end MachineInputQueue

structure MachineProcessingQueue (schema : MachineSchema) where
  id : MachineQueueId .processing
  kind : schema.ProcessingQueueKind
  contents : Queue (ProcessingQueueEntry schema kind)

namespace MachineProcessingQueue

def empty
    (id : MachineQueueId .processing)
    (kind : schema.ProcessingQueueKind)
    (capacity : Option Nat := none) : MachineProcessingQueue schema where
  id := id
  kind := kind
  contents := Queue.empty capacity

end MachineProcessingQueue

structure MachineOutputQueue (schema : MachineSchema) where
  id : MachineQueueId .output
  kind : schema.OutputQueueKind
  contents : Queue (OutputQueueEntry schema kind)

namespace MachineOutputQueue

def empty
    (id : MachineQueueId .output)
    (kind : schema.OutputQueueKind)
    (capacity : Option Nat := none) : MachineOutputQueue schema where
  id := id
  kind := kind
  contents := Queue.empty capacity

end MachineOutputQueue

/-! ## Dynamic queue topology -/

structure Machine (schema : MachineSchema) where
  inventory : AccountId
  maximumQueues : Nat

  inputQueues : List (MachineInputQueue schema)
  processingQueues : List (MachineProcessingQueue schema)
  outputQueues : List (MachineOutputQueue schema)

  inputIdsUnique : (inputQueues.map MachineInputQueue.id).Nodup
  processingIdsUnique :
    (processingQueues.map MachineProcessingQueue.id).Nodup
  outputIdsUnique : (outputQueues.map MachineOutputQueue.id).Nodup

  nextInputQueueId : Nat
  nextProcessingQueueId : Nat
  nextOutputQueueId : Nat

  inputIdsBeforeNext :
    ∀ queue ∈ inputQueues, queue.id.value < nextInputQueueId
  processingIdsBeforeNext :
    ∀ queue ∈ processingQueues, queue.id.value < nextProcessingQueueId
  outputIdsBeforeNext :
    ∀ queue ∈ outputQueues, queue.id.value < nextOutputQueueId

  withinQueueLimit :
    inputQueues.length + processingQueues.length + outputQueues.length ≤
      maximumQueues

namespace Machine

private def replaceSameId
    {Item Id : Type}
    [DecidableEq Id]
    (idOf : Item → Id)
    (replacement : Item) : List Item → List Item
  | [] => []
  | item :: rest =>
      (if idOf item = idOf replacement then replacement else item) ::
        replaceSameId idOf replacement rest

@[simp]
private theorem replaceSameId_length
    {Item Id : Type}
    [DecidableEq Id]
    (idOf : Item → Id)
    (replacement : Item)
    (items : List Item) :
    (replaceSameId idOf replacement items).length = items.length := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp [replaceSameId, ih]

@[simp]
private theorem replaceSameId_ids
    {Item Id : Type}
    [DecidableEq Id]
    (idOf : Item → Id)
    (replacement : Item)
    (items : List Item) :
    (replaceSameId idOf replacement items).map idOf = items.map idOf := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      by_cases same : idOf item = idOf replacement
      · simp [replaceSameId, same, ih]
      · simp [replaceSameId, same, ih]

def inputQueue?
    (machine : Machine schema)
    (id : MachineQueueId .input) : Option (MachineInputQueue schema) :=
  machine.inputQueues.find? fun queue => decide (queue.id = id)

def processingQueue?
    (machine : Machine schema)
    (id : MachineQueueId .processing) : Option (MachineProcessingQueue schema) :=
  machine.processingQueues.find? fun queue => decide (queue.id = id)

def outputQueue?
    (machine : Machine schema)
    (id : MachineQueueId .output) : Option (MachineOutputQueue schema) :=
  machine.outputQueues.find? fun queue => decide (queue.id = id)

def replaceInputQueue
    (machine : Machine schema)
    (replacement : MachineInputQueue schema) : Machine schema where
  inventory := machine.inventory
  maximumQueues := machine.maximumQueues
  inputQueues := replaceSameId MachineInputQueue.id replacement machine.inputQueues
  processingQueues := machine.processingQueues
  outputQueues := machine.outputQueues
  inputIdsUnique := by simpa using machine.inputIdsUnique
  processingIdsUnique := machine.processingIdsUnique
  outputIdsUnique := machine.outputIdsUnique
  nextInputQueueId := machine.nextInputQueueId
  nextProcessingQueueId := machine.nextProcessingQueueId
  nextOutputQueueId := machine.nextOutputQueueId
  inputIdsBeforeNext := by
    intro queue queueMem
    have idMem : queue.id ∈
        (replaceSameId MachineInputQueue.id replacement
          machine.inputQueues).map MachineInputQueue.id :=
      List.mem_map.mpr ⟨queue, queueMem, rfl⟩
    rw [replaceSameId_ids] at idMem
    obtain ⟨oldQueue, oldMem, sameId⟩ := List.mem_map.mp idMem
    rw [← sameId]
    exact machine.inputIdsBeforeNext oldQueue oldMem
  processingIdsBeforeNext := machine.processingIdsBeforeNext
  outputIdsBeforeNext := machine.outputIdsBeforeNext
  withinQueueLimit := by simpa using machine.withinQueueLimit

def replaceProcessingQueue
    (machine : Machine schema)
    (replacement : MachineProcessingQueue schema) : Machine schema where
  inventory := machine.inventory
  maximumQueues := machine.maximumQueues
  inputQueues := machine.inputQueues
  processingQueues :=
    replaceSameId MachineProcessingQueue.id replacement machine.processingQueues
  outputQueues := machine.outputQueues
  inputIdsUnique := machine.inputIdsUnique
  processingIdsUnique := by simpa using machine.processingIdsUnique
  outputIdsUnique := machine.outputIdsUnique
  nextInputQueueId := machine.nextInputQueueId
  nextProcessingQueueId := machine.nextProcessingQueueId
  nextOutputQueueId := machine.nextOutputQueueId
  inputIdsBeforeNext := machine.inputIdsBeforeNext
  processingIdsBeforeNext := by
    intro queue queueMem
    have idMem : queue.id ∈
        (replaceSameId MachineProcessingQueue.id replacement
          machine.processingQueues).map MachineProcessingQueue.id :=
      List.mem_map.mpr ⟨queue, queueMem, rfl⟩
    rw [replaceSameId_ids] at idMem
    obtain ⟨oldQueue, oldMem, sameId⟩ := List.mem_map.mp idMem
    rw [← sameId]
    exact machine.processingIdsBeforeNext oldQueue oldMem
  outputIdsBeforeNext := machine.outputIdsBeforeNext
  withinQueueLimit := by simpa using machine.withinQueueLimit

def replaceOutputQueue
    (machine : Machine schema)
    (replacement : MachineOutputQueue schema) : Machine schema where
  inventory := machine.inventory
  maximumQueues := machine.maximumQueues
  inputQueues := machine.inputQueues
  processingQueues := machine.processingQueues
  outputQueues := replaceSameId MachineOutputQueue.id replacement machine.outputQueues
  inputIdsUnique := machine.inputIdsUnique
  processingIdsUnique := machine.processingIdsUnique
  outputIdsUnique := by simpa using machine.outputIdsUnique
  nextInputQueueId := machine.nextInputQueueId
  nextProcessingQueueId := machine.nextProcessingQueueId
  nextOutputQueueId := machine.nextOutputQueueId
  inputIdsBeforeNext := machine.inputIdsBeforeNext
  processingIdsBeforeNext := machine.processingIdsBeforeNext
  outputIdsBeforeNext := by
    intro queue queueMem
    have idMem : queue.id ∈
        (replaceSameId MachineOutputQueue.id replacement
          machine.outputQueues).map MachineOutputQueue.id :=
      List.mem_map.mpr ⟨queue, queueMem, rfl⟩
    rw [replaceSameId_ids] at idMem
    obtain ⟨oldQueue, oldMem, sameId⟩ := List.mem_map.mp idMem
    rw [← sameId]
    exact machine.outputIdsBeforeNext oldQueue oldMem
  withinQueueLimit := by simpa using machine.withinQueueLimit

def empty
    (inventory : AccountId)
    (maximumQueues : Nat) : Machine schema where
  inventory := inventory
  maximumQueues := maximumQueues
  inputQueues := []
  processingQueues := []
  outputQueues := []
  inputIdsUnique := by simp
  processingIdsUnique := by simp
  outputIdsUnique := by simp
  nextInputQueueId := 0
  nextProcessingQueueId := 0
  nextOutputQueueId := 0
  inputIdsBeforeNext := by simp
  processingIdsBeforeNext := by simp
  outputIdsBeforeNext := by simp
  withinQueueLimit := by simp

def queueCount (machine : Machine schema) : Nat :=
  machine.inputQueues.length +
    machine.processingQueues.length +
    machine.outputQueues.length

theorem queueCount_withinLimit (machine : Machine schema) :
    machine.queueCount ≤ machine.maximumQueues :=
  machine.withinQueueLimit

def addInputQueue
    (machine : Machine schema)
    (kind : schema.InputQueueKind)
    (capacity : Option Nat)
    (room : machine.queueCount < machine.maximumQueues) : Machine schema where
  inventory := machine.inventory
  maximumQueues := machine.maximumQueues
  inputQueues := machine.inputQueues ++
    [MachineInputQueue.empty ⟨machine.nextInputQueueId⟩ kind capacity]
  processingQueues := machine.processingQueues
  outputQueues := machine.outputQueues
  inputIdsUnique := by
    rw [List.map_append]
    simp only [List.map_singleton, MachineInputQueue.empty]
    rw [List.nodup_append]
    refine ⟨machine.inputIdsUnique, by simp, ?_⟩
    intro old oldMem fresh freshMem
    simp only [List.mem_singleton] at freshMem
    subst fresh
    obtain ⟨queue, queueMem, queueId⟩ := List.mem_map.mp oldMem
    have before := machine.inputIdsBeforeNext queue queueMem
    rw [queueId] at before
    intro equal
    have valueEqual := congrArg MachineQueueId.value equal
    change old.value = machine.nextInputQueueId at valueEqual
    omega
  processingIdsUnique := machine.processingIdsUnique
  outputIdsUnique := machine.outputIdsUnique
  nextInputQueueId := machine.nextInputQueueId + 1
  nextProcessingQueueId := machine.nextProcessingQueueId
  nextOutputQueueId := machine.nextOutputQueueId
  inputIdsBeforeNext := by
    intro queue queueMem
    simp only [List.mem_append, List.mem_singleton] at queueMem
    rcases queueMem with oldMem | isNew
    · have before := machine.inputIdsBeforeNext queue oldMem
      omega
    · subst queue
      simp [MachineInputQueue.empty]
  processingIdsBeforeNext := machine.processingIdsBeforeNext
  outputIdsBeforeNext := machine.outputIdsBeforeNext
  withinQueueLimit := by
    simp only [List.length_append, List.length_singleton]
    unfold queueCount at room
    omega

def addProcessingQueue
    (machine : Machine schema)
    (kind : schema.ProcessingQueueKind)
    (capacity : Option Nat)
    (room : machine.queueCount < machine.maximumQueues) : Machine schema where
  inventory := machine.inventory
  maximumQueues := machine.maximumQueues
  inputQueues := machine.inputQueues
  processingQueues := machine.processingQueues ++
    [MachineProcessingQueue.empty ⟨machine.nextProcessingQueueId⟩ kind capacity]
  outputQueues := machine.outputQueues
  inputIdsUnique := machine.inputIdsUnique
  processingIdsUnique := by
    rw [List.map_append]
    simp only [List.map_singleton, MachineProcessingQueue.empty]
    rw [List.nodup_append]
    refine ⟨machine.processingIdsUnique, by simp, ?_⟩
    intro old oldMem fresh freshMem
    simp only [List.mem_singleton] at freshMem
    subst fresh
    obtain ⟨queue, queueMem, queueId⟩ := List.mem_map.mp oldMem
    have before := machine.processingIdsBeforeNext queue queueMem
    rw [queueId] at before
    intro equal
    have valueEqual := congrArg MachineQueueId.value equal
    change old.value = machine.nextProcessingQueueId at valueEqual
    omega
  outputIdsUnique := machine.outputIdsUnique
  nextInputQueueId := machine.nextInputQueueId
  nextProcessingQueueId := machine.nextProcessingQueueId + 1
  nextOutputQueueId := machine.nextOutputQueueId
  inputIdsBeforeNext := machine.inputIdsBeforeNext
  processingIdsBeforeNext := by
    intro queue queueMem
    simp only [List.mem_append, List.mem_singleton] at queueMem
    rcases queueMem with oldMem | isNew
    · have before := machine.processingIdsBeforeNext queue oldMem
      omega
    · subst queue
      simp [MachineProcessingQueue.empty]
  outputIdsBeforeNext := machine.outputIdsBeforeNext
  withinQueueLimit := by
    simp only [List.length_append, List.length_singleton]
    unfold queueCount at room
    omega

def addOutputQueue
    (machine : Machine schema)
    (kind : schema.OutputQueueKind)
    (capacity : Option Nat)
    (room : machine.queueCount < machine.maximumQueues) : Machine schema where
  inventory := machine.inventory
  maximumQueues := machine.maximumQueues
  inputQueues := machine.inputQueues
  processingQueues := machine.processingQueues
  outputQueues := machine.outputQueues ++
    [MachineOutputQueue.empty ⟨machine.nextOutputQueueId⟩ kind capacity]
  inputIdsUnique := machine.inputIdsUnique
  processingIdsUnique := machine.processingIdsUnique
  outputIdsUnique := by
    rw [List.map_append]
    simp only [List.map_singleton, MachineOutputQueue.empty]
    rw [List.nodup_append]
    refine ⟨machine.outputIdsUnique, by simp, ?_⟩
    intro old oldMem fresh freshMem
    simp only [List.mem_singleton] at freshMem
    subst fresh
    obtain ⟨queue, queueMem, queueId⟩ := List.mem_map.mp oldMem
    have before := machine.outputIdsBeforeNext queue queueMem
    rw [queueId] at before
    intro equal
    have valueEqual := congrArg MachineQueueId.value equal
    change old.value = machine.nextOutputQueueId at valueEqual
    omega
  nextInputQueueId := machine.nextInputQueueId
  nextProcessingQueueId := machine.nextProcessingQueueId
  nextOutputQueueId := machine.nextOutputQueueId + 1
  inputIdsBeforeNext := machine.inputIdsBeforeNext
  processingIdsBeforeNext := machine.processingIdsBeforeNext
  outputIdsBeforeNext := by
    intro queue queueMem
    simp only [List.mem_append, List.mem_singleton] at queueMem
    rcases queueMem with oldMem | isNew
    · have before := machine.outputIdsBeforeNext queue oldMem
      omega
    · subst queue
      simp [MachineOutputQueue.empty]
  withinQueueLimit := by
    simp only [List.length_append, List.length_singleton]
    unfold queueCount at room
    omega

def removeInputQueue
    (machine : Machine schema)
    (id : MachineQueueId .input) : Machine schema where
  inventory := machine.inventory
  maximumQueues := machine.maximumQueues
  inputQueues := machine.inputQueues.filter fun queue => decide (queue.id ≠ id)
  processingQueues := machine.processingQueues
  outputQueues := machine.outputQueues
  inputIdsUnique := by
    exact List.Nodup.sublist (List.filter_sublist.map MachineInputQueue.id)
      machine.inputIdsUnique
  processingIdsUnique := machine.processingIdsUnique
  outputIdsUnique := machine.outputIdsUnique
  nextInputQueueId := machine.nextInputQueueId
  nextProcessingQueueId := machine.nextProcessingQueueId
  nextOutputQueueId := machine.nextOutputQueueId
  inputIdsBeforeNext := by
    intro queue queueMem
    exact machine.inputIdsBeforeNext queue (List.mem_filter.mp queueMem).1
  processingIdsBeforeNext := machine.processingIdsBeforeNext
  outputIdsBeforeNext := machine.outputIdsBeforeNext
  withinQueueLimit := by
    have shorter := List.length_filter_le
      (fun queue : MachineInputQueue schema => decide (queue.id ≠ id))
      machine.inputQueues
    have within := machine.withinQueueLimit
    omega

def removeProcessingQueue
    (machine : Machine schema)
    (id : MachineQueueId .processing) : Machine schema where
  inventory := machine.inventory
  maximumQueues := machine.maximumQueues
  inputQueues := machine.inputQueues
  processingQueues :=
    machine.processingQueues.filter fun queue => decide (queue.id ≠ id)
  outputQueues := machine.outputQueues
  inputIdsUnique := machine.inputIdsUnique
  processingIdsUnique := by
    exact List.Nodup.sublist (List.filter_sublist.map MachineProcessingQueue.id)
      machine.processingIdsUnique
  outputIdsUnique := machine.outputIdsUnique
  nextInputQueueId := machine.nextInputQueueId
  nextProcessingQueueId := machine.nextProcessingQueueId
  nextOutputQueueId := machine.nextOutputQueueId
  inputIdsBeforeNext := machine.inputIdsBeforeNext
  processingIdsBeforeNext := by
    intro queue queueMem
    exact machine.processingIdsBeforeNext queue (List.mem_filter.mp queueMem).1
  outputIdsBeforeNext := machine.outputIdsBeforeNext
  withinQueueLimit := by
    have shorter := List.length_filter_le
      (fun queue : MachineProcessingQueue schema => decide (queue.id ≠ id))
      machine.processingQueues
    have within := machine.withinQueueLimit
    omega

def removeOutputQueue
    (machine : Machine schema)
    (id : MachineQueueId .output) : Machine schema where
  inventory := machine.inventory
  maximumQueues := machine.maximumQueues
  inputQueues := machine.inputQueues
  processingQueues := machine.processingQueues
  outputQueues := machine.outputQueues.filter fun queue => decide (queue.id ≠ id)
  inputIdsUnique := machine.inputIdsUnique
  processingIdsUnique := machine.processingIdsUnique
  outputIdsUnique := by
    exact List.Nodup.sublist (List.filter_sublist.map MachineOutputQueue.id)
      machine.outputIdsUnique
  nextInputQueueId := machine.nextInputQueueId
  nextProcessingQueueId := machine.nextProcessingQueueId
  nextOutputQueueId := machine.nextOutputQueueId
  inputIdsBeforeNext := machine.inputIdsBeforeNext
  processingIdsBeforeNext := machine.processingIdsBeforeNext
  outputIdsBeforeNext := by
    intro queue queueMem
    exact machine.outputIdsBeforeNext queue (List.mem_filter.mp queueMem).1
  withinQueueLimit := by
    have shorter := List.length_filter_le
      (fun queue : MachineOutputQueue schema => decide (queue.id ≠ id))
      machine.outputQueues
    have within := machine.withinQueueLimit
    omega

end Machine

end Maquina
