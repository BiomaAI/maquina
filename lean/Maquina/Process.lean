import Maquina.Inventory

/-!
# Maquina Processes

Processes are inert, labeled declarations of resource transformation. They do
not move themselves through queues or mutate inventories; operations do that.
-/

namespace Maquina

/-- One nonempty basket attached to a process-defined participant label. -/
structure ProcessPort (Label : Type) where
  label : Label
  basket : Basket
  nonempty : basket.entries ≠ []
  deriving Repr

/--
A process declares what labeled baskets are consumed and produced, plus the
exact amount of abstract work required for completion. Missing output labels
mean that the process produces nothing for those labels.
-/
structure Process (Label : Type) where
  inputs : List (ProcessPort Label)
  outputs : List (ProcessPort Label)
  inputLabelsUnique : (inputs.map ProcessPort.label).Nodup
  outputLabelsUnique : (outputs.map ProcessPort.label).Nodup
  requiredWork : Nat
  deriving Repr

namespace Process

def empty (requiredWork : Nat := 0) : Process Label where
  inputs := []
  outputs := []
  inputLabelsUnique := by simp
  outputLabelsUnique := by simp
  requiredWork := requiredWork

private def basketFor
    [DecidableEq Label]
    (label : Label) : List (ProcessPort Label) → Option Basket
  | [] => none
  | port :: rest =>
      if port.label = label then some port.basket
      else basketFor label rest

def inputFor
    [DecidableEq Label]
    (process : Process Label)
    (label : Label) : Option Basket :=
  basketFor label process.inputs

def outputFor
    [DecidableEq Label]
    (process : Process Label)
    (label : Label) : Option Basket :=
  basketFor label process.outputs

@[simp]
theorem inputFor_empty [DecidableEq Label] (label : Label) :
    (empty work : Process Label).inputFor label = none := rfl

@[simp]
theorem outputFor_empty [DecidableEq Label] (label : Label) :
    (empty work : Process Label).outputFor label = none := rfl

end Process

/--
A concrete invocation chooses a game-defined kind and binds every process
label directly to an inventory account. Account identities need no registry.
-/
structure ProcessInvocation (Kind Label : Type) where
  kind : Kind
  process : Process Label
  bind : Label → AccountId

namespace ProcessInvocation

def accountFor
    (invocation : ProcessInvocation Kind Label)
    (label : Label) : AccountId :=
  invocation.bind label

end ProcessInvocation

end Maquina
