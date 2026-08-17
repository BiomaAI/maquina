import Maquina.Transfer

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

/-- Whether a custodied process input is transformed or returned unchanged. -/
inductive ProcessInputUse where
  | consumed
  | reserved
  deriving DecidableEq, Repr

/--
Immutable provenance for one process input moved into custody. Source and
custody are recovered from the applied transfer receipt instead of being
independently mutable owner fields.
-/
structure Reservation (Label : Type) where
  use : ProcessInputUse
  label : Label
  basket : Basket
  receipt : TransferReceipt
  basketExact :
    receipt.lines.map TransferReceiptLine.toEntry = basket.entries
  deriving Repr

namespace Reservation

def source (reservation : Reservation Label) : AccountId :=
  reservation.receipt.source

def custody (reservation : Reservation Label) : AccountId :=
  reservation.receipt.destination

/-- Construct provenance directly from the receipt of an accepted transfer. -/
def ofAccepted
    {resourceCatalog : ResourceCatalog}
    {state : WorldState resourceCatalog}
    {proposal : Transfer}
    (use : ProcessInputUse)
    (label : Label)
    (accepted : AcceptedTransfer state proposal) : Reservation Label where
  use := use
  label := label
  basket := proposal.basket
  receipt := transferReceipt accepted
  basketExact := transferReceipt_entries accepted

@[simp]
theorem ofAccepted_source
    {resourceCatalog : ResourceCatalog}
    {state : WorldState resourceCatalog}
    {proposal : Transfer}
    (use : ProcessInputUse)
    (label : Label)
    (accepted : AcceptedTransfer state proposal) :
    (ofAccepted use label accepted).source = proposal.source := rfl

@[simp]
theorem ofAccepted_custody
    {resourceCatalog : ResourceCatalog}
    {state : WorldState resourceCatalog}
    {proposal : Transfer}
    (use : ProcessInputUse)
    (label : Label)
    (accepted : AcceptedTransfer state proposal) :
    (ofAccepted use label accepted).custody = proposal.destination := rfl

end Reservation

/-- Every canonical temporary input has one matching live reservation. -/
def ReservedInputsComplete
    (process : Process Label)
    (reservations : List (Reservation Label)) : Prop :=
  ∀ port ∈ process.reserved,
    ∃ reservation ∈ reservations,
      reservation.use = .reserved ∧
      reservation.label = port.label ∧
      reservation.basket = port.basket

/-- Every canonical consumed input has one matching staged reservation. -/
def ConsumedInputsComplete
    (process : Process Label)
    (reservations : List (Reservation Label)) : Prop :=
  ∀ port ∈ process.consumed,
    ∃ reservation ∈ reservations,
      reservation.use = .consumed ∧
      reservation.label = port.label ∧
      reservation.basket = port.basket

inductive ConsumedInputStatus
    (process : Process Label)
    (reservations : List (Reservation Label)) : Type where
  | missing
  | complete (evidence : ConsumedInputsComplete process reservations)

/-- Runtime evidence that temporary inputs are either not yet staged or complete. -/
inductive ReservedInputStatus
    (process : Process Label)
    (reservations : List (Reservation Label)) : Type where
  | missing
  | complete (evidence : ReservedInputsComplete process reservations)

/--
Concrete inventory bindings keep an input source, process custody, and an
initial output destination distinct. They are proposed routing data; accepted
reservation records later prove which sources actually funded custody.
-/
structure ProcessBindings (Label : Type) where
  source : Label → AccountId
  custody : Label → AccountId
  output : Label → Option AccountId

namespace ProcessBindings

/-- Bind one previously unresolved output without permitting reassignment. -/
def bindOutput
    [DecidableEq Label]
    (bindings : ProcessBindings Label)
    (label : Label)
    (account : AccountId)
    (_pending : bindings.output label = none) : ProcessBindings Label where
  source := bindings.source
  custody := bindings.custody
  output := fun queried =>
    if queried = label then some account else bindings.output queried

@[simp]
theorem bindOutput_same
    [DecidableEq Label]
    (bindings : ProcessBindings Label)
    (label : Label)
    (account : AccountId)
    (pending : bindings.output label = none) :
    (bindings.bindOutput label account pending).output label = some account := by
  simp [bindOutput]

@[simp]
theorem bindOutput_other
    [DecidableEq Label]
    (bindings : ProcessBindings Label)
    (label queried : Label)
    (account : AccountId)
    (pending : bindings.output label = none)
    (different : queried ≠ label) :
    (bindings.bindOutput label account pending).output queried =
      bindings.output queried := by
  simp [bindOutput, different]

end ProcessBindings

/--
One canonical process output held in custody. `none` means its destination is
intentionally unresolved until a later operation binds the labeled role.
-/
structure OutputAllocation (Label : Type) where
  label : Label
  basket : Basket
  custody : AccountId
  recipient : Option AccountId
  deriving Repr

def remainingAllocations
    [DecidableEq Label]
    (allocations : List (OutputAllocation Label))
    (collected : Label) : List (OutputAllocation Label) :=
  allocations.filter fun allocation => decide (allocation.label ≠ collected)

theorem remainingAllocations_label_absent
    [DecidableEq Label]
    (allocations : List (OutputAllocation Label))
    (collected : Label) :
    collected ∉ (remainingAllocations allocations collected).map
      OutputAllocation.label := by
  intro present
  obtain ⟨allocation, allocationMem, labelEq⟩ := List.mem_map.mp present
  have kept := (List.mem_filter.mp allocationMem).2
  simp only [decide_eq_true_eq] at kept
  exact kept labelEq

theorem remainingAllocations_labelsUnique
    [DecidableEq Label]
    (allocations : List (OutputAllocation Label))
    (collected : Label)
    (unique : (allocations.map OutputAllocation.label).Nodup) :
    ((remainingAllocations allocations collected).map
      OutputAllocation.label).Nodup := by
  apply List.Sublist.nodup
  · exact List.Sublist.map OutputAllocation.label List.filter_sublist
  · exact unique

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
    (label : Label) : Option AccountId :=
  invocation.bindings.output label

/-- Output amounts always come from the canonical process definition. -/
def outputAllocations
    (invocation : ProcessInvocation Kind Label) :
    List (OutputAllocation Label) :=
  invocation.process.outputs.map fun port =>
    { label := port.label
      basket := port.basket
      custody := invocation.bindings.custody port.label
      recipient := invocation.bindings.output port.label }

@[simp]
theorem outputAllocations_length
    (invocation : ProcessInvocation Kind Label) :
    invocation.outputAllocations.length = invocation.process.outputs.length := by
  simp [outputAllocations]

theorem outputAllocations_labelsUnique
    (invocation : ProcessInvocation Kind Label) :
    (invocation.outputAllocations.map OutputAllocation.label).Nodup := by
  simpa [outputAllocations, Function.comp_def] using
    invocation.process.outputLabelsUnique

end ProcessInvocation

end Maquina
