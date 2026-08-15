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
A process separates inputs that are transformed from capabilities that are
only reserved while work is live. Reserved baskets must remain unchanged and
are returned from custody to their recorded sources by a releasing operation.
Missing output labels mean that the process produces nothing for those labels.
-/
structure Process (Label : Type) where
  consumed : List (ProcessPort Label)
  reserved : List (ProcessPort Label)
  outputs : List (ProcessPort Label)
  consumedLabelsUnique : (consumed.map ProcessPort.label).Nodup
  reservedLabelsUnique : (reserved.map ProcessPort.label).Nodup
  outputLabelsUnique : (outputs.map ProcessPort.label).Nodup
  requiredWork : Nat
  deriving Repr

namespace Process

def empty (requiredWork : Nat := 0) : Process Label where
  consumed := []
  reserved := []
  outputs := []
  consumedLabelsUnique := by simp
  reservedLabelsUnique := by simp
  outputLabelsUnique := by simp
  requiredWork := requiredWork

private def basketFor
    [DecidableEq Label]
    (label : Label) : List (ProcessPort Label) → Option Basket
  | [] => none
  | port :: rest =>
      if port.label = label then some port.basket
      else basketFor label rest

def consumedFor
    [DecidableEq Label]
    (process : Process Label)
    (label : Label) : Option Basket :=
  basketFor label process.consumed

def reservedFor
    [DecidableEq Label]
    (process : Process Label)
    (label : Label) : Option Basket :=
  basketFor label process.reserved

def outputFor
    [DecidableEq Label]
    (process : Process Label)
    (label : Label) : Option Basket :=
  basketFor label process.outputs

@[simp]
theorem consumedFor_empty [DecidableEq Label] (label : Label) :
    (empty work : Process Label).consumedFor label = none := rfl

@[simp]
theorem reservedFor_empty [DecidableEq Label] (label : Label) :
    (empty work : Process Label).reservedFor label = none := rfl

@[simp]
theorem outputFor_empty [DecidableEq Label] (label : Label) :
    (empty work : Process Label).outputFor label = none := rfl

end Process

/--
Concrete inventory bindings keep an input source, process custody, and an
initial output destination distinct. They are proposed routing data; accepted
reservation records later prove which sources actually funded custody.
-/
structure ProcessBindings (Label : Type) where
  source : Label → AccountId
  custody : Label → AccountId
  output : Label → AccountId

/-- A concrete invocation chooses a game-defined kind and its account bindings. -/
structure ProcessInvocation (Kind Label : Type) where
  kind : Kind
  process : Process Label
  bindings : ProcessBindings Label

namespace ProcessInvocation

def sourceAccountFor
    (invocation : ProcessInvocation Kind Label)
    (label : Label) : AccountId :=
  invocation.bindings.source label

def custodyAccountFor
    (invocation : ProcessInvocation Kind Label)
    (label : Label) : AccountId :=
  invocation.bindings.custody label

def outputAccountFor
    (invocation : ProcessInvocation Kind Label)
    (label : Label) : AccountId :=
  invocation.bindings.output label

end ProcessInvocation

end Maquina
