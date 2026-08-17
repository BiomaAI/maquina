import Maquina.Custody
import Maquina.Transformation

/-!
# Maquina Lock-Aware Transformations

Inventory debits performed while machine custody is open can consume only the
unlocked portion of the machine inventory. Credits remain ordinarily checked
against resource supply limits.
-/

namespace Maquina
namespace MachineCustody

private def lockedDeltaIssues
    {resourceCatalog : ResourceCatalog}
    (world : WorldState resourceCatalog)
    (custody : MachineCustody inventory) :
    InventoryDelta → List InventoryDeltaIssue
  | .debit account entry =>
      if account = inventory then
        let available := unlockedAtoms world custody entry.resourceId
        if entry.quantity.atoms ≤ available then []
        else
          [.shortfall entry.resourceId entry.quantity.atoms available
            (entry.quantity.atoms - available)]
      else []
  | .credit _ _ => []

def custodyInventoryDeltaIssues
    {resourceCatalog : ResourceCatalog}
    (world : WorldState resourceCatalog)
    (custody : MachineCustody inventory)
    (delta : InventoryDelta) : List InventoryDeltaIssue :=
  inventoryDeltaIssues world delta ++ lockedDeltaIssues world custody delta

structure AcceptedCustodyInventoryDelta
    {resourceCatalog : ResourceCatalog}
    (world : WorldState resourceCatalog)
    (custody : MachineCustody inventory)
    (delta : InventoryDelta) : Prop where
  issuesEmpty : custodyInventoryDeltaIssues world custody delta = []

inductive CustodyInventoryDeltaAssessment
    {resourceCatalog : ResourceCatalog}
    (world : WorldState resourceCatalog)
    (custody : MachineCustody inventory)
    (delta : InventoryDelta) where
  | accepted (witness : AcceptedCustodyInventoryDelta world custody delta)
  | rejected
      (issues : List InventoryDeltaIssue)
      (issuesExact : issues = custodyInventoryDeltaIssues world custody delta)
      (nonempty : issues ≠ [])

def assessCustodyInventoryDelta
    {resourceCatalog : ResourceCatalog}
    (world : WorldState resourceCatalog)
    (custody : MachineCustody inventory)
    (delta : InventoryDelta) :
    CustodyInventoryDeltaAssessment world custody delta :=
  let issues := custodyInventoryDeltaIssues world custody delta
  if empty : issues = [] then .accepted ⟨empty⟩
  else .rejected issues rfl empty

theorem AcceptedCustodyInventoryDelta.deltaAccepted
    {resourceCatalog : ResourceCatalog}
    {world : WorldState resourceCatalog}
    {custody : MachineCustody inventory}
    {delta : InventoryDelta}
    (accepted : AcceptedCustodyInventoryDelta world custody delta) :
    AcceptedInventoryDelta world delta := by
  constructor
  exact (List.append_eq_nil_iff.mp accepted.issuesEmpty).1

theorem AcceptedCustodyInventoryDelta.debitUnlocked
    {resourceCatalog : ResourceCatalog}
    {world : WorldState resourceCatalog}
    {custody : MachineCustody inventory}
    {account : AccountId}
    {entry : BasketEntry}
    (accepted : AcceptedCustodyInventoryDelta world custody (.debit account entry))
    (accountMachine : account = inventory) :
    entry.quantity.atoms ≤ unlockedAtoms world custody entry.resourceId := by
  have lockedEmpty := (List.append_eq_nil_iff.mp accepted.issuesEmpty).2
  by_cases available :
      entry.quantity.atoms ≤ unlockedAtoms world custody entry.resourceId
  · exact available
  · simp [lockedDeltaIssues, accountMachine, available] at lockedEmpty

/-- Every accepted lock-aware delta preserves continuous custody backing. -/
theorem Backed.applyCustodyInventoryDelta
    {resourceCatalog : ResourceCatalog}
    {world : WorldState resourceCatalog}
    {custody : MachineCustody inventory}
    {delta : InventoryDelta}
    (backed : Backed world custody)
    (accepted : AcceptedCustodyInventoryDelta world custody delta) :
    Backed (applyInventoryDelta accepted.deltaAccepted) custody := by
  intro resourceId
  cases delta with
  | debit account entry =>
      by_cases accountMachine : account = inventory
      · subst account
        by_cases resourceSame : entry.resourceId = resourceId
        · subst resourceId
          rw [applyInventoryDelta_debit accepted.deltaAccepted]
          have unlocked := accepted.debitUnlocked rfl
          simp only [unlockedAtoms] at unlocked
          have backing := backed entry.resourceId
          omega
        · rw [applyInventoryDelta_otherKey accepted.deltaAccepted inventory resourceId
            (Or.inr resourceSame)]
          exact backed resourceId
      · rw [applyInventoryDelta_otherKey accepted.deltaAccepted inventory resourceId
          (Or.inl accountMachine)]
        exact backed resourceId
  | credit account entry =>
      by_cases accountMachine : account = inventory
      · subst account
        by_cases resourceSame : entry.resourceId = resourceId
        · subst resourceId
          rw [applyInventoryDelta_credit accepted.deltaAccepted]
          exact Nat.le_add_right_of_le (backed entry.resourceId)
        · rw [applyInventoryDelta_otherKey accepted.deltaAccepted inventory resourceId
            (Or.inr resourceSame)]
          exact backed resourceId
      · rw [applyInventoryDelta_otherKey accepted.deltaAccepted inventory resourceId
          (Or.inl accountMachine)]
        exact backed resourceId

structure AppliedCustodyInventoryProgram
    {resourceCatalog : ResourceCatalog}
    (before : WorldState resourceCatalog)
    (custody : MachineCustody inventory)
    (deltas : List InventoryDelta) where
  after : WorldState resourceCatalog
  receipts : List InventoryDeltaReceipt
  receiptsExact : receipts.map InventoryDeltaReceipt.delta = deltas
  backedAfter : Backed after custody
  replayExact : replayInventoryProgram receipts before.holdings = after.holdings

theorem AppliedCustodyInventoryProgram.balance_untouched
    {resourceCatalog : ResourceCatalog}
    {before : WorldState resourceCatalog}
    {custody : MachineCustody inventory}
    {deltas : List InventoryDelta}
    (applied : AppliedCustodyInventoryProgram before custody deltas)
    (account : AccountId)
    (resourceId : ResourceId)
    (untouched : ∀ delta ∈ deltas, ¬delta.TouchesKey account resourceId) :
    (applied.after.balance account resourceId).atoms =
      (before.balance account resourceId).atoms := by
  change balanceAtoms applied.after.holdings account resourceId =
    balanceAtoms before.holdings account resourceId
  rw [← applied.replayExact]
  apply replayInventoryProgram_balance_untouched
  intro receipt receiptMem
  apply untouched receipt.delta
  rw [← applied.receiptsExact]
  exact List.mem_map.mpr ⟨receipt, receiptMem, rfl⟩

/-- Pure all-or-none execution whose every prefix respects custody locks. -/
def applyCustodyInventoryProgram
    {resourceCatalog : ResourceCatalog}
    (before : WorldState resourceCatalog)
    (custody : MachineCustody inventory)
    (backedBefore : Backed before custody) :
    (deltas : List InventoryDelta) →
      Except (List InventoryDeltaIssue)
        (AppliedCustodyInventoryProgram before custody deltas)
  | [] =>
      .ok
        { after := before
          receipts := []
          receiptsExact := rfl
          backedAfter := backedBefore
          replayExact := rfl }
  | delta :: rest =>
      match assessCustodyInventoryDelta before custody delta with
      | .rejected issues _ _ => .error issues
      | .accepted accepted =>
          let middle := applyInventoryDelta accepted.deltaAccepted
          let backedMiddle := backedBefore.applyCustodyInventoryDelta accepted
          match applyCustodyInventoryProgram middle custody backedMiddle rest with
          | .error issues => .error issues
          | .ok suffix =>
              .ok
                { after := suffix.after
                  receipts :=
                    inventoryDeltaReceipt accepted.deltaAccepted :: suffix.receipts
                  receiptsExact := by
                    simp only [List.map_cons, inventoryDeltaReceipt]
                    rw [suffix.receiptsExact]
                  backedAfter := suffix.backedAfter
                  replayExact := by
                    simp only [replayInventoryProgram, List.foldl_cons]
                    rw [replay_inventoryDeltaReceipt accepted.deltaAccepted]
                    exact suffix.replayExact }

end MachineCustody
end Maquina
