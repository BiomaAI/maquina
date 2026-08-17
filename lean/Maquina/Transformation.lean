import Maquina.Transfer

/-!
# Maquina Inventory Transformations

Checked single-entry debits and credits are the primitive effects from which a
process completion can consume staged inputs and produce declared outputs.
Unlike transfers, transformations may change the global total of one resource.
-/

namespace Maquina

inductive InventoryDelta where
  | debit (account : AccountId) (entry : BasketEntry)
  | credit (account : AccountId) (entry : BasketEntry)
  deriving Repr

namespace InventoryDelta

def account : InventoryDelta → AccountId
  | .debit account _ | .credit account _ => account

def entry : InventoryDelta → BasketEntry
  | .debit _ entry | .credit _ entry => entry

end InventoryDelta

inductive InventoryDeltaIssue where
  | unknownResource (resourceId : ResourceId)
  | shortfall
      (resourceId : ResourceId)
      (requested available missing : Nat)
  | supplyLimit
      (resourceId : ResourceId)
      (maximum current requested excess : Nat)
  deriving DecidableEq, Repr

def inventoryDeltaIssues
    {resourceCatalog : ResourceCatalog}
    (state : WorldState resourceCatalog)
    (delta : InventoryDelta) : List InventoryDeltaIssue :=
  let entry := delta.entry
  match resourceCatalog.lookup entry.resourceId with
  | none => [.unknownResource entry.resourceId]
  | some spec =>
      match delta with
      | .debit account entry =>
          let available := (state.balance account entry.resourceId).atoms
          if entry.quantity.atoms ≤ available then []
          else
            [.shortfall entry.resourceId entry.quantity.atoms available
              (entry.quantity.atoms - available)]
      | .credit _ entry =>
          match spec.limit with
          | .unbounded => []
          | .bounded maximum _ =>
              let current := (state.total entry.resourceId).atoms
              if current + entry.quantity.atoms ≤ maximum.atoms then []
              else
                [.supplyLimit entry.resourceId maximum.atoms current
                  entry.quantity.atoms
                  (current + entry.quantity.atoms - maximum.atoms)]

structure AcceptedInventoryDelta
    {resourceCatalog : ResourceCatalog}
    (state : WorldState resourceCatalog)
    (delta : InventoryDelta) : Prop where
  issuesEmpty : inventoryDeltaIssues state delta = []

inductive InventoryDeltaAssessment
    {resourceCatalog : ResourceCatalog}
    (state : WorldState resourceCatalog)
    (delta : InventoryDelta) where
  | accepted (witness : AcceptedInventoryDelta state delta)
  | rejected
      (issues : List InventoryDeltaIssue)
      (issuesExact : issues = inventoryDeltaIssues state delta)
      (nonempty : issues ≠ [])

def assessInventoryDelta
    {resourceCatalog : ResourceCatalog}
    (state : WorldState resourceCatalog)
    (delta : InventoryDelta) : InventoryDeltaAssessment state delta :=
  let issues := inventoryDeltaIssues state delta
  if empty : issues = [] then .accepted ⟨empty⟩
  else .rejected issues rfl empty

theorem AcceptedInventoryDelta.resourceKnown
    {resourceCatalog : ResourceCatalog}
    {state : WorldState resourceCatalog}
    {delta : InventoryDelta}
    (accepted : AcceptedInventoryDelta state delta) :
    ∃ spec, resourceCatalog.lookup delta.entry.resourceId = some spec := by
  cases delta with
  | debit account entry =>
      cases found : resourceCatalog.lookup entry.resourceId with
      | none =>
          have issuesEmpty := accepted.issuesEmpty
          simp [inventoryDeltaIssues, InventoryDelta.entry, found] at issuesEmpty
      | some spec => exact ⟨spec, found⟩
  | credit account entry =>
      cases found : resourceCatalog.lookup entry.resourceId with
      | none =>
          have issuesEmpty := accepted.issuesEmpty
          simp [inventoryDeltaIssues, InventoryDelta.entry, found] at issuesEmpty
      | some spec => exact ⟨spec, found⟩

theorem AcceptedInventoryDelta.debitFunded
    {resourceCatalog : ResourceCatalog}
    {state : WorldState resourceCatalog}
    {account : AccountId}
    {entry : BasketEntry}
    (accepted : AcceptedInventoryDelta state (.debit account entry)) :
    entry.quantity.atoms ≤ (state.balance account entry.resourceId).atoms := by
  obtain ⟨spec, found⟩ := accepted.resourceKnown
  change resourceCatalog.lookup entry.resourceId = some spec at found
  by_cases funded :
      entry.quantity.atoms ≤ (state.balance account entry.resourceId).atoms
  · exact funded
  · have issuesEmpty := accepted.issuesEmpty
    simp [inventoryDeltaIssues, InventoryDelta.entry, found, funded] at issuesEmpty

theorem AcceptedInventoryDelta.creditWithinLimit
    {resourceCatalog : ResourceCatalog}
    {state : WorldState resourceCatalog}
    {account : AccountId}
    {entry : BasketEntry}
    (accepted : AcceptedInventoryDelta state (.credit account entry))
    {spec : ResourceSpec}
    {maximum : Quantity}
    {positive : 0 < maximum.atoms}
    (found : resourceCatalog.lookup entry.resourceId = some spec)
    (limitEq : spec.limit = .bounded maximum positive) :
    (state.total entry.resourceId).atoms + entry.quantity.atoms ≤
      maximum.atoms := by
  by_cases within :
      (state.total entry.resourceId).atoms + entry.quantity.atoms ≤ maximum.atoms
  · exact within
  · have issuesEmpty := accepted.issuesEmpty
    simp [inventoryDeltaIssues, InventoryDelta.entry, found, limitEq, within]
      at issuesEmpty

def inventoryDeltaHoldings
    (holdings : List (Holding AccountId)) :
    InventoryDelta → List (Holding AccountId)
  | .debit account entry =>
      setBalance holdings account entry.resourceId
        (balanceAtoms holdings account entry.resourceId - entry.quantity.atoms)
  | .credit account entry =>
      setBalance holdings account entry.resourceId
        (balanceAtoms holdings account entry.resourceId + entry.quantity.atoms)

def applyInventoryDelta
    {resourceCatalog : ResourceCatalog}
    {state : WorldState resourceCatalog}
    {delta : InventoryDelta}
    (accepted : AcceptedInventoryDelta state delta) : WorldState resourceCatalog where
  holdings := inventoryDeltaHoldings state.holdings delta
  keysUnique := by
    cases delta <;> apply setBalance_keysUnique <;> exact state.keysUnique
  resourcesKnown := by
    cases delta with
    | debit account entry | credit account entry =>
        apply state.resourcesKnown.setBalance
        exact accepted.resourceKnown
  respectsLimits := by
    intro queriedId spec maximum positive found limitEq
    cases delta with
    | debit account entry =>
        simp only [inventoryDeltaHoldings]
        by_cases same : entry.resourceId = queriedId
        · subst queriedId
          rw [totalAtomsFor_setBalance_same _ _ _ _ state.keysUnique]
          have funded := accepted.debitFunded
          have accountLe :=
            balanceAtoms_le_totalAtomsFor state.holdings account entry.resourceId
          have beforeLimit := state.respectsLimits found limitEq
          change
            totalAtomsFor state.holdings entry.resourceId -
                balanceAtoms state.holdings account entry.resourceId +
                (balanceAtoms state.holdings account entry.resourceId -
                  entry.quantity.atoms) ≤ maximum.atoms
          omega
        · rw [totalAtomsFor_setBalance_other _ _ _ _ _ same]
          exact state.respectsLimits found limitEq
    | credit account entry =>
        simp only [inventoryDeltaHoldings]
        by_cases same : entry.resourceId = queriedId
        · subst queriedId
          rw [totalAtomsFor_setBalance_same _ _ _ _ state.keysUnique]
          have accountLe :=
            balanceAtoms_le_totalAtomsFor state.holdings account entry.resourceId
          have within := accepted.creditWithinLimit found limitEq
          change
            totalAtomsFor state.holdings entry.resourceId +
              entry.quantity.atoms ≤ maximum.atoms at within
          change
            totalAtomsFor state.holdings entry.resourceId -
                balanceAtoms state.holdings account entry.resourceId +
                (balanceAtoms state.holdings account entry.resourceId +
                  entry.quantity.atoms) ≤ maximum.atoms
          omega
        · rw [totalAtomsFor_setBalance_other _ _ _ _ _ same]
          exact state.respectsLimits found limitEq

structure InventoryDeltaReceipt where
  delta : InventoryDelta
  accountBefore : Quantity
  accountAfter : Quantity
  totalBefore : Quantity
  totalAfter : Quantity
  deriving Repr

def inventoryDeltaReceipt
    {resourceCatalog : ResourceCatalog}
    {state : WorldState resourceCatalog}
    {delta : InventoryDelta}
    (accepted : AcceptedInventoryDelta state delta) : InventoryDeltaReceipt :=
  let after := applyInventoryDelta accepted
  { delta := delta
    accountBefore := state.balance delta.account delta.entry.resourceId
    accountAfter := after.balance delta.account delta.entry.resourceId
    totalBefore := state.total delta.entry.resourceId
    totalAfter := after.total delta.entry.resourceId }

theorem applyInventoryDelta_debit
    {resourceCatalog : ResourceCatalog}
    {state : WorldState resourceCatalog}
    {account : AccountId}
    {entry : BasketEntry}
    (accepted : AcceptedInventoryDelta state (.debit account entry)) :
    ((applyInventoryDelta accepted).balance account entry.resourceId).atoms =
      (state.balance account entry.resourceId).atoms - entry.quantity.atoms := by
  exact balanceAtoms_setBalance_same _ _ _ _

theorem applyInventoryDelta_credit
    {resourceCatalog : ResourceCatalog}
    {state : WorldState resourceCatalog}
    {account : AccountId}
    {entry : BasketEntry}
    (accepted : AcceptedInventoryDelta state (.credit account entry)) :
    ((applyInventoryDelta accepted).balance account entry.resourceId).atoms =
      (state.balance account entry.resourceId).atoms + entry.quantity.atoms := by
  exact balanceAtoms_setBalance_same _ _ _ _

/-- A delta cannot change any account/resource key other than its target. -/
theorem applyInventoryDelta_otherKey
    {resourceCatalog : ResourceCatalog}
    {state : WorldState resourceCatalog}
    {delta : InventoryDelta}
    (accepted : AcceptedInventoryDelta state delta)
    (account : AccountId)
    (resourceId : ResourceId)
    (different : delta.account ≠ account ∨ delta.entry.resourceId ≠ resourceId) :
    ((applyInventoryDelta accepted).balance account resourceId).atoms =
      (state.balance account resourceId).atoms := by
  cases delta with
  | debit target entry | credit target entry =>
      exact balanceAtoms_setBalance_other _ _ _ _ _ _ different

theorem applyInventoryDelta_debit_total
    {resourceCatalog : ResourceCatalog}
    {state : WorldState resourceCatalog}
    {account : AccountId}
    {entry : BasketEntry}
    (accepted : AcceptedInventoryDelta state (.debit account entry)) :
    ((applyInventoryDelta accepted).total entry.resourceId).atoms =
      (state.total entry.resourceId).atoms - entry.quantity.atoms := by
  change
    totalAtomsFor
        (setBalance state.holdings account entry.resourceId
          (balanceAtoms state.holdings account entry.resourceId -
            entry.quantity.atoms))
        entry.resourceId =
      totalAtomsFor state.holdings entry.resourceId - entry.quantity.atoms
  rw [totalAtomsFor_setBalance_same _ _ _ _ state.keysUnique]
  have funded := accepted.debitFunded
  change entry.quantity.atoms ≤
    balanceAtoms state.holdings account entry.resourceId at funded
  have accountLe :=
    balanceAtoms_le_totalAtomsFor state.holdings account entry.resourceId
  omega

theorem applyInventoryDelta_credit_total
    {resourceCatalog : ResourceCatalog}
    {state : WorldState resourceCatalog}
    {account : AccountId}
    {entry : BasketEntry}
    (accepted : AcceptedInventoryDelta state (.credit account entry)) :
    ((applyInventoryDelta accepted).total entry.resourceId).atoms =
      (state.total entry.resourceId).atoms + entry.quantity.atoms := by
  change
    totalAtomsFor
        (setBalance state.holdings account entry.resourceId
          (balanceAtoms state.holdings account entry.resourceId +
            entry.quantity.atoms))
        entry.resourceId =
      totalAtomsFor state.holdings entry.resourceId + entry.quantity.atoms
  rw [totalAtomsFor_setBalance_same _ _ _ _ state.keysUnique]
  have accountLe :=
    balanceAtoms_le_totalAtomsFor state.holdings account entry.resourceId
  omega

/-- Replay a checked delta receipt against raw canonical holdings. -/
def replayInventoryDeltaReceipt
    (receipt : InventoryDeltaReceipt)
    (holdings : List (Holding AccountId)) : List (Holding AccountId) :=
  inventoryDeltaHoldings holdings receipt.delta

theorem replay_inventoryDeltaReceipt
    {resourceCatalog : ResourceCatalog}
    {state : WorldState resourceCatalog}
    {delta : InventoryDelta}
    (accepted : AcceptedInventoryDelta state delta) :
    replayInventoryDeltaReceipt (inventoryDeltaReceipt accepted) state.holdings =
      (applyInventoryDelta accepted).holdings := rfl

/-! ## Atomic programs of checked deltas -/

def replayInventoryProgram
    (receipts : List InventoryDeltaReceipt)
    (holdings : List (Holding AccountId)) : List (Holding AccountId) :=
  receipts.foldl (fun current receipt =>
    replayInventoryDeltaReceipt receipt current) holdings

def InventoryDelta.TouchesKey
    (delta : InventoryDelta)
    (account : AccountId)
    (resourceId : ResourceId) : Prop :=
  delta.account = account ∧ delta.entry.resourceId = resourceId

theorem replayInventoryProgram_balance_untouched
    (receipts : List InventoryDeltaReceipt)
    (holdings : List (Holding AccountId))
    (account : AccountId)
    (resourceId : ResourceId)
    (untouched : ∀ receipt ∈ receipts,
      ¬receipt.delta.TouchesKey account resourceId) :
    balanceAtoms (replayInventoryProgram receipts holdings) account resourceId =
      balanceAtoms holdings account resourceId := by
  induction receipts generalizing holdings with
  | nil => rfl
  | cons receipt rest ih =>
      change
        balanceAtoms
            (replayInventoryProgram rest
              (replayInventoryDeltaReceipt receipt holdings))
            account resourceId =
          balanceAtoms holdings account resourceId
      rw [ih]
      · cases deltaEq : receipt.delta with
        | debit target entry | credit target entry =>
            simp only [replayInventoryDeltaReceipt, inventoryDeltaHoldings,
              deltaEq]
            apply balanceAtoms_setBalance_other
            have notTouched := untouched receipt (by simp)
            simp only [InventoryDelta.TouchesKey, deltaEq,
              InventoryDelta.account, InventoryDelta.entry]
              at notTouched
            by_cases sameAccount : target = account
            · exact Or.inr fun sameResource =>
                notTouched ⟨sameAccount, sameResource⟩
            · exact Or.inl sameAccount
      · intro queried queriedMem
        exact untouched queried (by simp [queriedMem])

structure AppliedInventoryProgram
    {resourceCatalog : ResourceCatalog}
    (before : WorldState resourceCatalog)
    (deltas : List InventoryDelta) where
  after : WorldState resourceCatalog
  receipts : List InventoryDeltaReceipt
  receiptsExact : receipts.map InventoryDeltaReceipt.delta = deltas
  replayExact : replayInventoryProgram receipts before.holdings = after.holdings

theorem AppliedInventoryProgram.balance_untouched
    {resourceCatalog : ResourceCatalog}
    {before : WorldState resourceCatalog}
    {deltas : List InventoryDelta}
    (applied : AppliedInventoryProgram before deltas)
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

/--
Pure all-or-none execution. A rejected suffix discards the locally computed
prefix and exposes no successor world.
-/
def applyInventoryProgram
    {resourceCatalog : ResourceCatalog}
    (before : WorldState resourceCatalog) :
    (deltas : List InventoryDelta) →
      Except (List InventoryDeltaIssue) (AppliedInventoryProgram before deltas)
  | [] =>
      .ok
        { after := before
          receipts := []
          receiptsExact := rfl
          replayExact := rfl }
  | delta :: rest =>
      match assessInventoryDelta before delta with
      | .rejected issues _ _ => .error issues
      | .accepted accepted =>
          let middle := applyInventoryDelta accepted
          match applyInventoryProgram middle rest with
          | .error issues => .error issues
          | .ok suffix =>
              .ok
                { after := suffix.after
                  receipts := inventoryDeltaReceipt accepted :: suffix.receipts
                  receiptsExact := by
                    simp only [List.map_cons, inventoryDeltaReceipt]
                    rw [suffix.receiptsExact]
                  replayExact := by
                    simp only [replayInventoryProgram, List.foldl_cons]
                    rw [replay_inventoryDeltaReceipt accepted]
                    exact suffix.replayExact }

def inventoryProgramSuccessor
    {resourceCatalog : ResourceCatalog}
    (before : WorldState resourceCatalog)
    (deltas : List InventoryDelta) : Option (WorldState resourceCatalog) :=
  match applyInventoryProgram before deltas with
  | .error _ => none
  | .ok applied => some applied.after

end Maquina
