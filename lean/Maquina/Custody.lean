import Maquina.Transfer

/-!
# Maquina Machine Custody

Long-lived machine custody backed only by accepted transfer receipts. The
receipt is authoritative for the deposited basket, source, and destination;
closing a position reverses that exact movement.
-/

namespace Maquina

structure CustodyPosition where
  id : Nat
  basket : Basket
  receipt : TransferReceipt
  basketExact :
    receipt.lines.map TransferReceiptLine.toEntry = basket.entries
  deriving Repr

namespace CustodyPosition

def source (position : CustodyPosition) : AccountId :=
  position.receipt.source

def destination (position : CustodyPosition) : AccountId :=
  position.receipt.destination

def ofAccepted
    {resourceCatalog : ResourceCatalog}
    {state : WorldState resourceCatalog}
    {proposal : Transfer}
    (id : Nat)
    (accepted : AcceptedTransfer state proposal) : CustodyPosition where
  id := id
  basket := proposal.basket
  receipt := transferReceipt accepted
  basketExact := transferReceipt_entries accepted

@[simp]
theorem ofAccepted_source
    {resourceCatalog : ResourceCatalog}
    {state : WorldState resourceCatalog}
    {proposal : Transfer}
    (id : Nat)
    (accepted : AcceptedTransfer state proposal) :
    (ofAccepted id accepted).source = proposal.source := rfl

@[simp]
theorem ofAccepted_destination
    {resourceCatalog : ResourceCatalog}
    {state : WorldState resourceCatalog}
    {proposal : Transfer}
    (id : Nat)
    (accepted : AcceptedTransfer state proposal) :
    (ofAccepted id accepted).destination = proposal.destination := rfl

end CustodyPosition

/-- Open custody positions for one concrete machine inventory account. -/
structure MachineCustody (inventory : AccountId) where
  positions : List CustodyPosition
  idsUnique : (positions.map CustodyPosition.id).Nodup
  nextId : Nat
  idsBeforeNext : ∀ position ∈ positions, position.id < nextId
  destinationsExact :
    ∀ position ∈ positions, position.destination = inventory
  deriving Repr

namespace MachineCustody

def empty (inventory : AccountId) : MachineCustody inventory where
  positions := []
  idsUnique := by simp
  nextId := 0
  idsBeforeNext := by simp
  destinationsExact := by simp

def position?
    (custody : MachineCustody inventory)
    (id : Nat) : Option CustodyPosition :=
  custody.positions.find? fun position => position.id = id

def deposit
    {resourceCatalog : ResourceCatalog}
    {state : WorldState resourceCatalog}
    {proposal : Transfer}
    (custody : MachineCustody inventory)
    (accepted : AcceptedTransfer state proposal)
    (destinationExact : proposal.destination = inventory) :
    MachineCustody inventory :=
  let position := CustodyPosition.ofAccepted custody.nextId accepted
  { positions := position :: custody.positions
    idsUnique := by
      simp only [List.map_cons, List.nodup_cons]
      constructor
      · intro idMem
        obtain ⟨existing, existingMem, idEq⟩ := List.mem_map.mp idMem
        have before := custody.idsBeforeNext existing existingMem
        change existing.id = custody.nextId at idEq
        omega
      · exact custody.idsUnique
    nextId := custody.nextId + 1
    idsBeforeNext := by
      intro queried queriedMem
      simp only [List.mem_cons] at queriedMem
      rcases queriedMem with isNew | wasOpen
      · subst queried
        simp [position, CustodyPosition.ofAccepted]
      · exact Nat.lt_succ_of_lt (custody.idsBeforeNext queried wasOpen)
    destinationsExact := by
      intro queried queriedMem
      simp only [List.mem_cons] at queriedMem
      rcases queriedMem with isNew | wasOpen
      · subst queried
        simpa [position] using destinationExact
      · exact custody.destinationsExact queried wasOpen }

def remove
    (custody : MachineCustody inventory)
    (id : Nat) : MachineCustody inventory where
  positions := custody.positions.filter fun position => decide (position.id ≠ id)
  idsUnique := by
    apply List.Sublist.nodup
    · exact List.Sublist.map CustodyPosition.id List.filter_sublist
    · exact custody.idsUnique
  nextId := custody.nextId
  idsBeforeNext := by
    intro position positionMem
    exact custody.idsBeforeNext position (List.mem_filter.mp positionMem).1
  destinationsExact := by
    intro position positionMem
    exact custody.destinationsExact position (List.mem_filter.mp positionMem).1

end MachineCustody

end Maquina
