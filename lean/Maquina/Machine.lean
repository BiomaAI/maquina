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

/-- An admitted invocation waiting to be dispatched. -/
structure QueuedProcess (schema : MachineSchema) where
  id : Nat
  processKind : schema.ProcessKind
  bindings : ProcessBindings schema.Label
  reservations : List (Reservation schema.Label)

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

end Machine

end Maquina
