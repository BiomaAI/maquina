import Maquina.Machine
import Maquina.Possession

/-!
# Maquina Operations

Declarative operation programs and their bindings. This module defines data;
it does not assess, apply, schedule, or simulate operations.
-/

namespace Maquina

inductive OperationTrigger where
  | commanded
  | scheduled
  | reactive
  deriving DecidableEq, Repr

/--
Abstract queue ports are bound to concrete, direction-correct machine queue
identities by an operation proposal or machine instance.
-/
structure QueueBindings (Port : QueueStage → Type) where
  resolve : {stage : QueueStage} → Port stage → Option (MachineQueueId stage)

/-- Runtime accounts offered for operation-defined output recipient roles. -/
structure RecipientBindings (Label : Type) where
  resolve : Label → Option AccountId

/--
The generic effects understood by the Maquina simulator. Games compose
these primitives but do not implement their execution.
-/
inductive OperationEffect
    (schema : MachineSchema)
    (Port : QueueStage → Type) where
  | reserveProcessInputs
  | enqueue
      (destination : Port .input)
  | moveToProcessing
      (source : Port .input)
      (destination : Port .processing)
  | advance
      (source : Port .processing)
      (work : Nat)
      (positive : 0 < work)
  | bindOutput
      (label : schema.Label)
  | completeToOutput
      (source : Port .processing)
      (destination : Port .output)
  | completeToInventories
      (source : Port .processing)
  | releaseReservations
      {stage : QueueStage}
      (source : Port stage)
  | collect
      (source : Port .output)
  | addInputQueue
      (port : Port .input)
      (kind : schema.InputQueueKind)
      (entryCapacity : Option Nat)
  | removeInputQueue
      (port : Port .input)
  | addProcessingQueue
      (port : Port .processing)
      (kind : schema.ProcessingQueueKind)
      (entryCapacity : Option Nat)
  | removeProcessingQueue
      (port : Port .processing)
  | addOutputQueue
      (port : Port .output)
      (kind : schema.OutputQueueKind)
      (entryCapacity : Option Nat)
  | removeOutputQueue
      (port : Port .output)

/-- One declarative operation program. -/
structure OperationDefinition
    (schema : MachineSchema)
    (Port : QueueStage → Type)
    (Guard : Type) where
  trigger : OperationTrigger
  guards : List Guard
  requirements : List (PossessionPort schema.Label)
  processKind : Option schema.ProcessKind
  effects : List (OperationEffect schema Port)

/--
An implementor supplies its own modes, indexed operations, queue-port names,
guards, and the definition of each typed operation.
-/
structure OperationLanguage (schema : MachineSchema) where
  Mode : Type
  Operation : Mode → Mode → Type
  QueuePort : QueueStage → Type
  Guard : Type
  modeDecidableEq : DecidableEq Mode
  definition :
    {before after : Mode} →
      Operation before after →
      OperationDefinition schema QueuePort Guard

/--
A bound proposal selects one typed operation and supplies concrete process and
queue bindings. It remains inert data until a generic simulator interprets it.
-/
structure OperationProposal
    (schema : MachineSchema)
    (language : OperationLanguage schema) where
  before : language.Mode
  after : language.Mode
  operation : language.Operation before after
  possessionBindings : PossessionBindings schema.Label
  processBindings : Option (ProcessBindings schema.Label)
  queueBindings : QueueBindings language.QueuePort
  recipientBindings : RecipientBindings schema.Label

end Maquina
