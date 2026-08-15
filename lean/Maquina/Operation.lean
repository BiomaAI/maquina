import Maquina.Machine

/-!
# Maquina Operations

Operations declare when process instances move, where completion is routed,
and how a machine's queue topology changes. Domain operation names and machine
conditions remain implementor-owned types.
-/

namespace Maquina

inductive OperationTrigger where
  | commanded
  | scheduled
  | reactive
  deriving DecidableEq, Repr

/--
The generic lifecycle routes available to an operation. Inventory endpoints
are obtained from the process invocation's labeled account bindings.
-/
inductive OperationRoute where
  | admit
      (destination : MachineQueueId .input)
  | dispatch
      (source : MachineQueueId .input)
      (destination : MachineQueueId .processing)
  | completeToOutput
      (source : MachineQueueId .processing)
      (destination : MachineQueueId .output)
  | completeToInventories
      (source : MachineQueueId .processing)
  | collect
      (source : MachineQueueId .output)
  deriving DecidableEq, Repr

/-- Queue topology changes are explicit operation effects. -/
inductive QueueTopologyEffect (schema : MachineSchema) where
  | addInput
      (kind : schema.InputQueueKind)
      (entryCapacity : Option Nat)
  | removeInput
      (queueId : MachineQueueId .input)
  | addProcessing
      (kind : schema.ProcessingQueueKind)
      (entryCapacity : Option Nat)
  | removeProcessing
      (queueId : MachineQueueId .processing)
  | addOutput
      (kind : schema.OutputQueueKind)
      (entryCapacity : Option Nat)
  | removeOutput
      (queueId : MachineQueueId .output)

/--
A machine operation may route one process phase and may change queue topology.
An absent process kind and route describes a condition-only or topology-only
operation such as starting, stopping, or installing an additional queue.
-/
structure OperationRule (schema : MachineSchema) (Guard : Type) where
  trigger : OperationTrigger
  guards : List Guard
  processKind : Option schema.ProcessKind
  route : Option OperationRoute
  topologyEffects : List (QueueTopologyEffect schema)

namespace OperationRule

def stateOnly
    (trigger : OperationTrigger)
    (guards : List Guard := []) : OperationRule schema Guard where
  trigger := trigger
  guards := guards
  processKind := none
  route := none
  topologyEffects := []

def routed
    (trigger : OperationTrigger)
    (processKind : schema.ProcessKind)
    (route : OperationRoute)
    (guards : List Guard := []) : OperationRule schema Guard where
  trigger := trigger
  guards := guards
  processKind := some processKind
  route := some route
  topologyEffects := []

end OperationRule

end Maquina
