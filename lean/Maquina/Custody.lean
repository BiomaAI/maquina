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

/-- Total quantity unavailable to ordinary machine spending for one resource. -/
def lockedAtoms
    (custody : MachineCustody inventory)
    (resourceId : ResourceId) : Nat :=
  (custody.positions.map fun position =>
    position.basket.lookupAtoms resourceId).sum

/-- Every custody lock is continuously funded by the machine inventory. -/
def Backed
    {resourceCatalog : ResourceCatalog}
    (world : WorldState resourceCatalog)
    (custody : MachineCustody inventory) : Prop :=
  ∀ resourceId,
    custody.lockedAtoms resourceId ≤
      (world.balance inventory resourceId).atoms

def empty (inventory : AccountId) : MachineCustody inventory where
  positions := []
  idsUnique := by simp
  nextId := 0
  idsBeforeNext := by simp
  destinationsExact := by simp

@[simp]
theorem lockedAtoms_empty (inventory : AccountId) (resourceId : ResourceId) :
    (empty inventory).lockedAtoms resourceId = 0 := rfl

theorem backed_empty
    {resourceCatalog : ResourceCatalog}
    (world : WorldState resourceCatalog)
    (inventory : AccountId) :
    Backed world (empty inventory) := by
  intro resourceId
  simp

def position?
    (custody : MachineCustody inventory)
    (id : Nat) : Option CustodyPosition :=
  custody.positions.find? fun position => position.id = id

theorem position?_mem
    (custody : MachineCustody inventory)
    {id : Nat}
    {position : CustodyPosition}
    (found : custody.position? id = some position) :
    position ∈ custody.positions :=
  List.mem_of_find?_eq_some found

theorem position?_id
    (custody : MachineCustody inventory)
    {id : Nat}
    {position : CustodyPosition}
    (found : custody.position? id = some position) :
    position.id = id := by
  have predicateTrue : decide (position.id = id) = true := by
    exact List.find?_some
      (p := fun queried : CustodyPosition => decide (queried.id = id))
      (l := custody.positions)
      (a := position)
      (by simpa [position?] using found)
  exact of_decide_eq_true predicateTrue

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

@[simp]
theorem lockedAtoms_deposit
    {resourceCatalog : ResourceCatalog}
    {state : WorldState resourceCatalog}
    {proposal : Transfer}
    (custody : MachineCustody inventory)
    (accepted : AcceptedTransfer state proposal)
    (destinationExact : proposal.destination = inventory)
    (resourceId : ResourceId) :
    (custody.deposit accepted destinationExact).lockedAtoms resourceId =
      proposal.basket.lookupAtoms resourceId + custody.lockedAtoms resourceId :=
  rfl

/-- Depositing an accepted transfer increases balance and locks equally. -/
theorem backed_deposit
    {resourceCatalog : ResourceCatalog}
    {state : WorldState resourceCatalog}
    {proposal : Transfer}
    (custody : MachineCustody inventory)
    (backed : Backed state custody)
    (accepted : AcceptedTransfer state proposal)
    (destinationExact : proposal.destination = inventory) :
    Backed (applyTransferState accepted)
      (custody.deposit accepted destinationExact) := by
  intro resourceId
  rw [lockedAtoms_deposit]
  have destinationBalance :=
    applyTransferState_destination_lookup accepted resourceId
  rw [destinationExact] at destinationBalance
  rw [destinationBalance]
  have previous := backed resourceId
  omega

private theorem sum_filter_le
    {α : Type}
    (values : List α)
    (keep : α → Bool)
    (measure : α → Nat) :
    ((values.filter keep).map measure).sum ≤
      (values.map measure).sum := by
  induction values with
  | nil => simp
  | cons value rest ih =>
      cases kept : keep value
      · simp only [List.filter_cons, kept, Bool.false_eq_true, ↓reduceIte,
          List.map_cons, List.sum_cons]
        omega
      · simp [kept, ih]

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

theorem lockedAtoms_remove_le
    (custody : MachineCustody inventory)
    (id : Nat)
    (resourceId : ResourceId) :
    (custody.remove id).lockedAtoms resourceId ≤
      custody.lockedAtoms resourceId := by
  exact sum_filter_le custody.positions
    (fun position => decide (position.id ≠ id))
    (fun position => position.basket.lookupAtoms resourceId)

/-- Releasing a lock without yet moving funds cannot invalidate backing. -/
theorem Backed.remove
    {resourceCatalog : ResourceCatalog}
    {world : WorldState resourceCatalog}
    {custody : MachineCustody inventory}
    (backed : Backed world custody)
    (id : Nat) :
    Backed world (custody.remove id) := by
  intro resourceId
  exact Nat.le_trans (lockedAtoms_remove_le custody id resourceId)
    (backed resourceId)

/-! ## Lock-aware transfers -/

/-- Balance available after all open custody positions have been protected. -/
def unlockedAtoms
    {resourceCatalog : ResourceCatalog}
    (world : WorldState resourceCatalog)
    (custody : MachineCustody inventory)
    (resourceId : ResourceId) : Nat :=
  (world.balance inventory resourceId).atoms - custody.lockedAtoms resourceId

private def lockedEntryIssues
    {resourceCatalog : ResourceCatalog}
    (world : WorldState resourceCatalog)
    (custody : MachineCustody inventory)
    (entry : BasketEntry) : List TransferIssue :=
  let available := unlockedAtoms world custody entry.resourceId
  if entry.quantity.atoms ≤ available then []
  else
    [.shortfall entry.resourceId entry.quantity.atoms available
      (entry.quantity.atoms - available)]

/-- Ordinary transfer assessment includes shortfalls against unlocked balance. -/
def custodyTransferIssues
    {resourceCatalog : ResourceCatalog}
    (world : WorldState resourceCatalog)
    (custody : MachineCustody inventory)
    (proposal : Transfer) : List TransferIssue :=
  transferIssues world proposal ++
    if proposal.source = inventory then
      proposal.basket.entries.flatMap (lockedEntryIssues world custody)
    else []

/-- Proof that a transfer is both ordinarily valid and cannot spend locks. -/
structure AcceptedCustodyTransfer
    {resourceCatalog : ResourceCatalog}
    (world : WorldState resourceCatalog)
    (custody : MachineCustody inventory)
    (proposal : Transfer) : Prop where
  issuesEmpty : custodyTransferIssues world custody proposal = []

inductive CustodyTransferAssessment
    {resourceCatalog : ResourceCatalog}
    (world : WorldState resourceCatalog)
    (custody : MachineCustody inventory)
    (proposal : Transfer) where
  | accepted (witness : AcceptedCustodyTransfer world custody proposal)
  | rejected
      (issues : List TransferIssue)
      (issuesExact : issues = custodyTransferIssues world custody proposal)
      (nonempty : issues ≠ [])

def assessCustodyTransfer
    {resourceCatalog : ResourceCatalog}
    (world : WorldState resourceCatalog)
    (custody : MachineCustody inventory)
    (proposal : Transfer) : CustodyTransferAssessment world custody proposal :=
  let issues := custodyTransferIssues world custody proposal
  if empty : issues = [] then .accepted ⟨empty⟩
  else .rejected issues rfl empty

theorem AcceptedCustodyTransfer.transferAccepted
    {resourceCatalog : ResourceCatalog}
    {world : WorldState resourceCatalog}
    {custody : MachineCustody inventory}
    {proposal : Transfer}
    (accepted : AcceptedCustodyTransfer world custody proposal) :
    AcceptedTransfer world proposal := by
  constructor
  have allEmpty := List.append_eq_nil_iff.mp accepted.issuesEmpty
  exact allEmpty.1

theorem AcceptedCustodyTransfer.entryUnlocked
    {resourceCatalog : ResourceCatalog}
    {world : WorldState resourceCatalog}
    {custody : MachineCustody inventory}
    {proposal : Transfer}
    (accepted : AcceptedCustodyTransfer world custody proposal)
    (sourceMachine : proposal.source = inventory)
    (entry : BasketEntry)
    (entryMem : entry ∈ proposal.basket.entries) :
    entry.quantity.atoms ≤ unlockedAtoms world custody entry.resourceId := by
  have allEmpty := List.append_eq_nil_iff.mp accepted.issuesEmpty
  have lockedEmpty :
      proposal.basket.entries.flatMap (lockedEntryIssues world custody) = [] := by
    simpa [sourceMachine] using allEmpty.2
  have entryEmpty : lockedEntryIssues world custody entry = [] :=
    (List.flatMap_eq_nil_iff.mp lockedEmpty) entry entryMem
  by_cases available :
      entry.quantity.atoms ≤ unlockedAtoms world custody entry.resourceId
  · exact available
  · simp [lockedEntryIssues, available] at entryEmpty

theorem AcceptedCustodyTransfer.lookupUnlocked
    {resourceCatalog : ResourceCatalog}
    {world : WorldState resourceCatalog}
    {custody : MachineCustody inventory}
    {proposal : Transfer}
    (accepted : AcceptedCustodyTransfer world custody proposal)
    (sourceMachine : proposal.source = inventory)
    (resourceId : ResourceId) :
    proposal.basket.lookupAtoms resourceId ≤
      unlockedAtoms world custody resourceId := by
  by_cases present : resourceId ∈
      proposal.basket.entries.map BasketEntry.resourceId
  · obtain ⟨entry, entryMem, entryId⟩ := List.mem_map.mp present
    subst resourceId
    rw [Basket.lookupAtoms_eq_of_mem proposal.basket entry entryMem]
    exact accepted.entryUnlocked sourceMachine entry entryMem
  · rw [Basket.lookupAtoms_eq_zero_of_not_mem proposal.basket resourceId present]
    omega

/-- A lock-aware transfer preserves funding for every open position. -/
theorem Backed.applyCustodyTransfer
    {resourceCatalog : ResourceCatalog}
    {world : WorldState resourceCatalog}
    {custody : MachineCustody inventory}
    {proposal : Transfer}
    (backed : Backed world custody)
    (accepted : AcceptedCustodyTransfer world custody proposal) :
    Backed (applyTransferState accepted.transferAccepted) custody := by
  intro resourceId
  by_cases sourceMachine : proposal.source = inventory
  · have available := accepted.lookupUnlocked sourceMachine resourceId
    have balanceChange :=
      applyTransferState_source_lookup accepted.transferAccepted resourceId
    rw [sourceMachine] at balanceChange
    rw [balanceChange]
    have backing := backed resourceId
    simp only [unlockedAtoms] at available
    omega
  · by_cases destinationMachine : proposal.destination = inventory
    · have balanceChange :=
        applyTransferState_destination_lookup accepted.transferAccepted resourceId
      rw [destinationMachine] at balanceChange
      rw [balanceChange]
      exact Nat.le_add_right_of_le (backed resourceId)
    · rw [applyTransferState_otherAccount accepted.transferAccepted inventory
        resourceId sourceMachine destinationMachine]
      exact backed resourceId

end MachineCustody

end Maquina
