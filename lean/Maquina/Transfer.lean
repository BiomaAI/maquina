import Maquina.Inventory

/-!
# Maquina Transfers

Pure transfer proposals, structured assessment, accepted witnesses, and
receipt vocabulary.
-/

namespace Maquina

/-- A proposal to move one canonical basket atomically between two accounts. -/
structure Transfer where
  source : AccountId
  destination : AccountId
  basket : Basket
  deriving Repr

/-- Every reason discovered while assessing a transfer proposal. -/
inductive TransferIssue where
  | sameAccount
  | unknownResource (resourceId : ResourceId)
  | shortfall
      (resourceId : ResourceId)
      (requested : Nat)
      (available : Nat)
      (missing : Nat)
  deriving DecidableEq, Repr

private def entryIssues
    {resourceCatalog : ResourceCatalog}
    (state : WorldState resourceCatalog)
    (source : AccountId)
    (entry : BasketEntry) : List TransferIssue :=
  match resourceCatalog.lookup entry.resourceId with
  | none => [.unknownResource entry.resourceId]
  | some _ =>
      let available := (state.balance source entry.resourceId).atoms
      if entry.quantity.atoms ≤ available then
        []
      else
        [.shortfall
          entry.resourceId
          entry.quantity.atoms
          available
          (entry.quantity.atoms - available)]

/--
Assessment collects all independent resource issues instead of stopping at the
first failure.
-/
def transferIssues
    {resourceCatalog : ResourceCatalog}
    (state : WorldState resourceCatalog)
    (proposal : Transfer) : List TransferIssue :=
  let accountIssues :=
    if proposal.source = proposal.destination then [.sameAccount] else []
  accountIssues ++
    proposal.basket.entries.flatMap (entryIssues state proposal.source)

/-- Proof that a concrete proposal passed the authoritative assessment. -/
structure AcceptedTransfer
    {resourceCatalog : ResourceCatalog}
    (state : WorldState resourceCatalog)
    (proposal : Transfer) : Prop where
  issuesEmpty : transferIssues state proposal = []

/-- Assessment returns either every issue or a proof-carrying acceptance. -/
inductive TransferAssessment
    {resourceCatalog : ResourceCatalog}
    (state : WorldState resourceCatalog)
    (proposal : Transfer) where
  | accepted (witness : AcceptedTransfer state proposal)
  | rejected
      (issues : List TransferIssue)
      (issuesExact : issues = transferIssues state proposal)
      (nonempty : issues ≠ [])

/-- Pure, deterministic assessment of one transfer proposal. -/
def assessTransfer
    {resourceCatalog : ResourceCatalog}
    (state : WorldState resourceCatalog)
    (proposal : Transfer) : TransferAssessment state proposal :=
  let issues := transferIssues state proposal
  if empty : issues = [] then
    .accepted ⟨empty⟩
  else
    .rejected issues rfl empty

/-- Accepted transfers always move between two distinct account identities. -/
theorem AcceptedTransfer.accountsDistinct
    {resourceCatalog : ResourceCatalog}
    {state : WorldState resourceCatalog}
    {proposal : Transfer}
    (accepted : AcceptedTransfer state proposal) :
    proposal.source ≠ proposal.destination := by
  intro same
  have issuesEmpty := accepted.issuesEmpty
  simp [transferIssues, same] at issuesEmpty

/-- Every entry in an accepted basket resolves to a resource definition. -/
theorem AcceptedTransfer.resourceKnown
    {resourceCatalog : ResourceCatalog}
    {state : WorldState resourceCatalog}
    {proposal : Transfer}
    (accepted : AcceptedTransfer state proposal)
    {entry : BasketEntry}
    (entryMem : entry ∈ proposal.basket.entries) :
    ∃ spec, resourceCatalog.lookup entry.resourceId = some spec := by
  have flatEmpty :
      proposal.basket.entries.flatMap
          (entryIssues state proposal.source) = [] := by
    have issuesEmpty := accepted.issuesEmpty
    unfold transferIssues at issuesEmpty
    exact (List.append_eq_nil_iff.mp issuesEmpty).2
  have issueEmpty : entryIssues state proposal.source entry = [] :=
    (List.flatMap_eq_nil_iff.mp flatEmpty) entry entryMem
  cases found : resourceCatalog.lookup entry.resourceId with
  | none => simp [entryIssues, found] at issueEmpty
  | some spec => exact ⟨spec, rfl⟩

/-- Every entry in an accepted basket is fully funded by the source balance. -/
theorem AcceptedTransfer.funded
    {resourceCatalog : ResourceCatalog}
    {state : WorldState resourceCatalog}
    {proposal : Transfer}
    (accepted : AcceptedTransfer state proposal)
    {entry : BasketEntry}
    (entryMem : entry ∈ proposal.basket.entries) :
    entry.quantity.atoms ≤
      (state.balance proposal.source entry.resourceId).atoms := by
  have flatEmpty :
      proposal.basket.entries.flatMap
          (entryIssues state proposal.source) = [] := by
    have issuesEmpty := accepted.issuesEmpty
    unfold transferIssues at issuesEmpty
    exact (List.append_eq_nil_iff.mp issuesEmpty).2
  have issueEmpty : entryIssues state proposal.source entry = [] :=
    (List.flatMap_eq_nil_iff.mp flatEmpty) entry entryMem
  obtain ⟨spec, found⟩ := accepted.resourceKnown entryMem
  by_cases funded : entry.quantity.atoms ≤
      (state.balance proposal.source entry.resourceId).atoms
  · exact funded
  · simp [entryIssues, found, funded] at issueEmpty

/-! ## Receipt vocabulary -/

/-- The exact before/after evidence for one transferred resource. -/
structure TransferReceiptLine where
  resourceId : ResourceId
  quantity : Quantity
  positive : 0 < quantity.atoms
  sourceBefore : Quantity
  sourceAfter : Quantity
  destinationBefore : Quantity
  destinationAfter : Quantity
  deriving Repr

/-- An immutable account-qualified record of an applied transfer. -/
structure TransferReceipt where
  source : AccountId
  destination : AccountId
  lines : List TransferReceiptLine
  deriving Repr

namespace TransferReceiptLine

/-- Recover the canonical basket entry recorded by a receipt line. -/
def toEntry (line : TransferReceiptLine) : BasketEntry where
  resourceId := line.resourceId
  quantity := line.quantity
  positive := line.positive

end TransferReceiptLine

/-! ## Raw holding transition -/

/--
Move one basket entry between distinct accounts in sparse canonical holdings.
This raw operation is total; the accepted-transfer witness supplies the funding
premise used to prove conservation.
-/
def transferEntryHoldings
    (holdings : List (Holding AccountId))
    (source destination : AccountId)
    (entry : BasketEntry) : List (Holding AccountId) :=
  let sourceAfter :=
    balanceAtoms holdings source entry.resourceId - entry.quantity.atoms
  let debited :=
    setBalance holdings source entry.resourceId sourceAfter
  let destinationAfter :=
    balanceAtoms holdings destination entry.resourceId + entry.quantity.atoms
  setBalance debited destination entry.resourceId destinationAfter

/-- Moving one entry preserves canonical `(account, resource)` key uniqueness. -/
theorem transferEntryHoldings_keysUnique
    (holdings : List (Holding AccountId))
    (source destination : AccountId)
    (entry : BasketEntry)
    (unique : (holdings.map Holding.key).Nodup) :
    ((transferEntryHoldings holdings source destination entry).map
      Holding.key).Nodup := by
  unfold transferEntryHoldings
  apply setBalance_keysUnique
  apply setBalance_keysUnique
  exact unique

/-- Moving a known resource preserves the known-resource invariant. -/
theorem transferEntryHoldings_resourcesKnown
    {resourceCatalog : ResourceCatalog}
    (holdings : List (Holding AccountId))
    (source destination : AccountId)
    (entry : BasketEntry)
    (known : ResourcesKnown resourceCatalog holdings)
    (entryKnown : ∃ spec, resourceCatalog.lookup entry.resourceId = some spec) :
    ResourcesKnown resourceCatalog
      (transferEntryHoldings holdings source destination entry) := by
  unfold transferEntryHoldings
  apply ResourcesKnown.setBalance
  · apply ResourcesKnown.setBalance
    · exact known
    · exact entryKnown
  · exact entryKnown

/-- The source loses exactly the requested atoms for one funded entry. -/
theorem transferEntryHoldings_source
    (holdings : List (Holding AccountId))
    (source destination : AccountId)
    (entry : BasketEntry)
    (distinct : source ≠ destination) :
    balanceAtoms (transferEntryHoldings holdings source destination entry)
        source entry.resourceId =
      balanceAtoms holdings source entry.resourceId - entry.quantity.atoms := by
  unfold transferEntryHoldings
  rw [balanceAtoms_setBalance_other]
  · exact balanceAtoms_setBalance_same _ _ _ _
  · exact Or.inl distinct.symm

/-- The destination gains exactly the requested atoms for one entry. -/
theorem transferEntryHoldings_destination
    (holdings : List (Holding AccountId))
    (source destination : AccountId)
    (entry : BasketEntry) :
    balanceAtoms (transferEntryHoldings holdings source destination entry)
        destination entry.resourceId =
      balanceAtoms holdings destination entry.resourceId + entry.quantity.atoms := by
  unfold transferEntryHoldings
  exact balanceAtoms_setBalance_same _ _ _ _

/-- Moving one entry leaves every other resource balance unchanged. -/
theorem transferEntryHoldings_otherResource
    (holdings : List (Holding AccountId))
    (source destination queriedAccount : AccountId)
    (entry : BasketEntry)
    (queriedResource : ResourceId)
    (different : entry.resourceId ≠ queriedResource) :
    balanceAtoms (transferEntryHoldings holdings source destination entry)
        queriedAccount queriedResource =
      balanceAtoms holdings queriedAccount queriedResource := by
  unfold transferEntryHoldings
  rw [balanceAtoms_setBalance_other]
  · rw [balanceAtoms_setBalance_other]
    exact Or.inr different
  · exact Or.inr different

/-- A funded single-entry move conserves that resource's global total. -/
theorem transferEntryHoldings_total
    (holdings : List (Holding AccountId))
    (source destination : AccountId)
    (entry : BasketEntry)
    (unique : (holdings.map Holding.key).Nodup)
    (distinct : source ≠ destination)
    (funded : entry.quantity.atoms ≤
      balanceAtoms holdings source entry.resourceId) :
    totalAtomsFor (transferEntryHoldings holdings source destination entry)
        entry.resourceId =
      totalAtomsFor holdings entry.resourceId := by
  let sourceAfter :=
    balanceAtoms holdings source entry.resourceId - entry.quantity.atoms
  let debited := setBalance holdings source entry.resourceId sourceAfter
  have debitedUnique : (debited.map Holding.key).Nodup := by
    exact setBalance_keysUnique holdings source entry.resourceId sourceAfter unique
  have destinationLe :
      balanceAtoms debited destination entry.resourceId ≤
        totalAtomsFor debited entry.resourceId :=
    balanceAtoms_le_totalAtomsFor debited destination entry.resourceId
  have sourceLe :
      balanceAtoms holdings source entry.resourceId ≤
        totalAtomsFor holdings entry.resourceId :=
    balanceAtoms_le_totalAtomsFor holdings source entry.resourceId
  have destinationUnchanged :
      balanceAtoms debited destination entry.resourceId =
        balanceAtoms holdings destination entry.resourceId := by
    exact balanceAtoms_setBalance_other holdings source destination
      entry.resourceId entry.resourceId sourceAfter (Or.inl distinct)
  have debitedTotal :
      totalAtomsFor debited entry.resourceId =
        totalAtomsFor holdings entry.resourceId -
          balanceAtoms holdings source entry.resourceId + sourceAfter := by
    exact totalAtomsFor_setBalance_same holdings source entry.resourceId
      sourceAfter unique
  unfold transferEntryHoldings
  change totalAtomsFor
      (setBalance debited destination entry.resourceId
        (balanceAtoms holdings destination entry.resourceId +
          entry.quantity.atoms)) entry.resourceId = _
  rw [totalAtomsFor_setBalance_same _ _ _ _ debitedUnique]
  rw [destinationUnchanged, debitedTotal]
  rw [destinationUnchanged, debitedTotal] at destinationLe
  dsimp [sourceAfter] at destinationLe ⊢
  omega

/-- A single-entry move preserves every unrelated resource's global total. -/
theorem transferEntryHoldings_total_other
    (holdings : List (Holding AccountId))
    (source destination : AccountId)
    (entry : BasketEntry)
    (queriedResource : ResourceId)
    (different : entry.resourceId ≠ queriedResource) :
    totalAtomsFor (transferEntryHoldings holdings source destination entry)
        queriedResource =
      totalAtomsFor holdings queriedResource := by
  unfold transferEntryHoldings
  rw [totalAtomsFor_setBalance_other]
  · exact totalAtomsFor_setBalance_other _ _ _ _ _ different
  · exact different

/-! ## Atomic basket transition -/

/--
Apply every entry in a basket to raw holdings. Recursing through the tail first
lets resource uniqueness make each entry independent of every other entry.
-/
def transferEntriesHoldings
    (source destination : AccountId) :
    List BasketEntry →
    List (Holding AccountId) →
    List (Holding AccountId)
  | [], holdings => holdings
  | entry :: rest, holdings =>
      transferEntryHoldings
        (transferEntriesHoldings source destination rest holdings)
        source destination entry

/-- A whole basket transition preserves canonical key uniqueness. -/
theorem transferEntriesHoldings_keysUnique
    (source destination : AccountId)
    (entries : List BasketEntry)
    (holdings : List (Holding AccountId))
    (unique : (holdings.map Holding.key).Nodup) :
    ((transferEntriesHoldings source destination entries holdings).map
      Holding.key).Nodup := by
  induction entries generalizing holdings with
  | nil => exact unique
  | cons entry rest ih =>
      apply transferEntryHoldings_keysUnique
      exact ih holdings unique

/-- A whole basket of known resources preserves the known-resource invariant. -/
theorem transferEntriesHoldings_resourcesKnown
    {resourceCatalog : ResourceCatalog}
    (source destination : AccountId)
    (entries : List BasketEntry)
    (holdings : List (Holding AccountId))
    (known : ResourcesKnown resourceCatalog holdings)
    (entriesKnown : ∀ entry, entry ∈ entries →
      ∃ spec, resourceCatalog.lookup entry.resourceId = some spec) :
    ResourcesKnown resourceCatalog
      (transferEntriesHoldings source destination entries holdings) := by
  induction entries generalizing holdings with
  | nil => exact known
  | cons entry rest ih =>
      apply transferEntryHoldings_resourcesKnown
      · exact ih holdings known fun restEntry restMem =>
          entriesKnown restEntry (List.mem_cons_of_mem entry restMem)
      · exact entriesKnown entry (by simp)

/-- Entries for other resources cannot affect a queried balance. -/
theorem transferEntriesHoldings_balance_not_mem
    (source destination : AccountId)
    (entries : List BasketEntry)
    (holdings : List (Holding AccountId))
    (queriedAccount : AccountId)
    (queriedResource : ResourceId)
    (absent : queriedResource ∉ entries.map BasketEntry.resourceId) :
    balanceAtoms
        (transferEntriesHoldings source destination entries holdings)
        queriedAccount queriedResource =
      balanceAtoms holdings queriedAccount queriedResource := by
  induction entries generalizing holdings with
  | nil => rfl
  | cons entry rest ih =>
      simp only [List.map_cons, List.mem_cons, not_or] at absent
      rw [transferEntriesHoldings]
      rw [transferEntryHoldings_otherResource]
      · exact ih holdings absent.2
      · intro same
        exact absent.1 same.symm

/-- A funded, resource-unique basket transition conserves every global total. -/
theorem transferEntriesHoldings_total
    (source destination : AccountId)
    (entries : List BasketEntry)
    (holdings : List (Holding AccountId))
    (unique : (holdings.map Holding.key).Nodup)
    (distinct : source ≠ destination)
    (entriesUnique : (entries.map BasketEntry.resourceId).Nodup)
    (funded : ∀ entry, entry ∈ entries →
      entry.quantity.atoms ≤ balanceAtoms holdings source entry.resourceId)
    (queriedResource : ResourceId) :
    totalAtomsFor
        (transferEntriesHoldings source destination entries holdings)
        queriedResource =
      totalAtomsFor holdings queriedResource := by
  induction entries generalizing holdings with
  | nil => rfl
  | cons entry rest ih =>
      have uniqueParts := List.nodup_cons.mp entriesUnique
      have restFunded : ∀ restEntry, restEntry ∈ rest →
          restEntry.quantity.atoms ≤
            balanceAtoms holdings source restEntry.resourceId :=
        fun restEntry restMem =>
          funded restEntry (List.mem_cons_of_mem entry restMem)
      have restKeysUnique :=
        transferEntriesHoldings_keysUnique source destination rest holdings unique
      have restTotal := ih holdings unique uniqueParts.2 restFunded
      rw [transferEntriesHoldings]
      by_cases sameResource : entry.resourceId = queriedResource
      · subst queriedResource
        have sourceUnchanged :=
          transferEntriesHoldings_balance_not_mem source destination rest
            holdings source entry.resourceId uniqueParts.1
        apply Eq.trans
          (transferEntryHoldings_total
            (transferEntriesHoldings source destination rest holdings)
            source destination entry restKeysUnique distinct ?_)
        · exact restTotal
        · rw [sourceUnchanged]
          exact funded entry (by simp)
      · apply Eq.trans
          (transferEntryHoldings_total_other
            (transferEntriesHoldings source destination rest holdings)
            source destination entry queriedResource sameResource)
        exact restTotal

/-- A basket entry's source balance changes by exactly its own quantity. -/
theorem transferEntriesHoldings_source
    (source destination : AccountId)
    (entries : List BasketEntry)
    (holdings : List (Holding AccountId))
    (distinct : source ≠ destination)
    (entriesUnique : (entries.map BasketEntry.resourceId).Nodup)
    (entry : BasketEntry)
    (entryMem : entry ∈ entries) :
    balanceAtoms
        (transferEntriesHoldings source destination entries holdings)
        source entry.resourceId =
      balanceAtoms holdings source entry.resourceId - entry.quantity.atoms := by
  induction entries generalizing holdings with
  | nil => simp at entryMem
  | cons head rest ih =>
      have uniqueParts := List.nodup_cons.mp entriesUnique
      rcases List.mem_cons.mp entryMem with isHead | inRest
      · subst head
        rw [transferEntriesHoldings]
        rw [transferEntryHoldings_source _ _ _ _ distinct]
        rw [transferEntriesHoldings_balance_not_mem source destination rest
          holdings source entry.resourceId uniqueParts.1]
      · have different : head.resourceId ≠ entry.resourceId := by
          intro same
          apply uniqueParts.1
          rw [List.mem_map]
          exact ⟨entry, inRest, same.symm⟩
        rw [transferEntriesHoldings]
        rw [transferEntryHoldings_otherResource _ _ _ _ _ _ different]
        exact ih holdings uniqueParts.2 inRest

/-- A basket entry's destination balance changes by exactly its own quantity. -/
theorem transferEntriesHoldings_destination
    (source destination : AccountId)
    (entries : List BasketEntry)
    (holdings : List (Holding AccountId))
    (entriesUnique : (entries.map BasketEntry.resourceId).Nodup)
    (entry : BasketEntry)
    (entryMem : entry ∈ entries) :
    balanceAtoms
        (transferEntriesHoldings source destination entries holdings)
        destination entry.resourceId =
      balanceAtoms holdings destination entry.resourceId +
        entry.quantity.atoms := by
  induction entries generalizing holdings with
  | nil => simp at entryMem
  | cons head rest ih =>
      have uniqueParts := List.nodup_cons.mp entriesUnique
      rcases List.mem_cons.mp entryMem with isHead | inRest
      · subst head
        rw [transferEntriesHoldings]
        rw [transferEntryHoldings_destination]
        rw [transferEntriesHoldings_balance_not_mem source destination rest
          holdings destination entry.resourceId uniqueParts.1]
      · have different : head.resourceId ≠ entry.resourceId := by
          intro same
          apply uniqueParts.1
          rw [List.mem_map]
          exact ⟨entry, inRest, same.symm⟩
        rw [transferEntriesHoldings]
        rw [transferEntryHoldings_otherResource _ _ _ _ _ _ different]
        exact ih holdings uniqueParts.2 inRest

/-- Moving one entry leaves balances of every third account unchanged. -/
theorem transferEntryHoldings_otherAccount
    (holdings : List (Holding AccountId))
    (source destination queriedAccount : AccountId)
    (entry : BasketEntry)
    (notSource : source ≠ queriedAccount)
    (notDestination : destination ≠ queriedAccount) :
    balanceAtoms (transferEntryHoldings holdings source destination entry)
        queriedAccount entry.resourceId =
      balanceAtoms holdings queriedAccount entry.resourceId := by
  unfold transferEntryHoldings
  rw [balanceAtoms_setBalance_other]
  · exact balanceAtoms_setBalance_other _ _ _ _ _ _ (Or.inl notSource)
  · exact Or.inl notDestination

/-- A basket transition leaves every third account balance unchanged. -/
theorem transferEntriesHoldings_otherAccount
    (source destination : AccountId)
    (entries : List BasketEntry)
    (holdings : List (Holding AccountId))
    (queriedAccount : AccountId)
    (queriedResource : ResourceId)
    (notSource : source ≠ queriedAccount)
    (notDestination : destination ≠ queriedAccount) :
    balanceAtoms
        (transferEntriesHoldings source destination entries holdings)
        queriedAccount queriedResource =
      balanceAtoms holdings queriedAccount queriedResource := by
  induction entries generalizing holdings with
  | nil => rfl
  | cons entry rest ih =>
      rw [transferEntriesHoldings]
      by_cases sameResource : entry.resourceId = queriedResource
      · subst queriedResource
        rw [transferEntryHoldings_otherAccount _ _ _ _ _
          notSource notDestination]
        exact ih holdings
      · rw [transferEntryHoldings_otherResource _ _ _ _ _ _ sameResource]
        exact ih holdings

/-! ## Proof-carrying world-state application -/

/-- The raw successor holdings determined by one transfer proposal. -/
def transferredHoldings
    {resourceCatalog : ResourceCatalog}
    (state : WorldState resourceCatalog)
    (proposal : Transfer) : List (Holding AccountId) :=
  transferEntriesHoldings proposal.source proposal.destination
    proposal.basket.entries state.holdings

/--
Apply an accepted transfer to the authoritative world. Every `WorldState`
invariant is reconstructed from the accepted witness and transition proofs.
-/
def applyTransferState
    {resourceCatalog : ResourceCatalog}
    {state : WorldState resourceCatalog}
    {proposal : Transfer}
    (accepted : AcceptedTransfer state proposal) : WorldState resourceCatalog where
  holdings := transferredHoldings state proposal
  keysUnique := by
    exact transferEntriesHoldings_keysUnique proposal.source
      proposal.destination proposal.basket.entries state.holdings
      state.keysUnique
  resourcesKnown := by
    exact transferEntriesHoldings_resourcesKnown proposal.source
      proposal.destination proposal.basket.entries state.holdings
      state.resourcesKnown fun entry entryMem => accepted.resourceKnown entryMem
  respectsLimits := by
    intro resourceId spec maximum positive found limitEq
    unfold transferredHoldings
    rw [transferEntriesHoldings_total proposal.source proposal.destination
      proposal.basket.entries state.holdings state.keysUnique
      accepted.accountsDistinct proposal.basket.resourcesUnique
      (fun entry entryMem => accepted.funded entryMem) resourceId]
    exact state.respectsLimits found limitEq

/-- Application conserves the global total of every resource identity. -/
theorem applyTransferState_total
    {resourceCatalog : ResourceCatalog}
    {state : WorldState resourceCatalog}
    {proposal : Transfer}
    (accepted : AcceptedTransfer state proposal)
    (resourceId : ResourceId) :
    ((applyTransferState accepted).total resourceId).atoms =
      (state.total resourceId).atoms := by
  exact transferEntriesHoldings_total proposal.source proposal.destination
    proposal.basket.entries state.holdings state.keysUnique
    accepted.accountsDistinct proposal.basket.resourcesUnique
    (fun entry entryMem => accepted.funded entryMem) resourceId

/-- Every transferred entry is debited from its source by exactly its quantity. -/
theorem applyTransferState_source
    {resourceCatalog : ResourceCatalog}
    {state : WorldState resourceCatalog}
    {proposal : Transfer}
    (accepted : AcceptedTransfer state proposal)
    (entry : BasketEntry)
    (entryMem : entry ∈ proposal.basket.entries) :
    ((applyTransferState accepted).balance proposal.source entry.resourceId).atoms =
      (state.balance proposal.source entry.resourceId).atoms -
        entry.quantity.atoms := by
  exact transferEntriesHoldings_source proposal.source proposal.destination
    proposal.basket.entries state.holdings accepted.accountsDistinct
    proposal.basket.resourcesUnique entry entryMem

/-- Every transferred entry is credited to its destination by exactly its quantity. -/
theorem applyTransferState_destination
    {resourceCatalog : ResourceCatalog}
    {state : WorldState resourceCatalog}
    {proposal : Transfer}
    (accepted : AcceptedTransfer state proposal)
    (entry : BasketEntry)
    (entryMem : entry ∈ proposal.basket.entries) :
    ((applyTransferState accepted).balance proposal.destination entry.resourceId).atoms =
      (state.balance proposal.destination entry.resourceId).atoms +
        entry.quantity.atoms := by
  exact transferEntriesHoldings_destination proposal.source
    proposal.destination proposal.basket.entries state.holdings
    proposal.basket.resourcesUnique entry entryMem

/-- Application cannot change a balance for a resource absent from the basket. -/
theorem applyTransferState_unlistedResource
    {resourceCatalog : ResourceCatalog}
    {state : WorldState resourceCatalog}
    {proposal : Transfer}
    (accepted : AcceptedTransfer state proposal)
    (account : AccountId)
    (resourceId : ResourceId)
    (absent : resourceId ∉
      proposal.basket.entries.map BasketEntry.resourceId) :
    ((applyTransferState accepted).balance account resourceId).atoms =
      (state.balance account resourceId).atoms := by
  exact transferEntriesHoldings_balance_not_mem proposal.source
    proposal.destination proposal.basket.entries state.holdings
    account resourceId absent

/-- Application cannot change balances owned by a third account. -/
theorem applyTransferState_otherAccount
    {resourceCatalog : ResourceCatalog}
    {state : WorldState resourceCatalog}
    {proposal : Transfer}
    (accepted : AcceptedTransfer state proposal)
    (account : AccountId)
    (resourceId : ResourceId)
    (notSource : proposal.source ≠ account)
    (notDestination : proposal.destination ≠ account) :
    ((applyTransferState accepted).balance account resourceId).atoms =
      (state.balance account resourceId).atoms := by
  exact transferEntriesHoldings_otherAccount proposal.source
    proposal.destination proposal.basket.entries state.holdings account
    resourceId notSource notDestination

/-! ## Receipts, replay, and all-or-none execution -/

/-- Build the auditable before/after record for one applied basket entry. -/
def makeTransferReceiptLine
    {resourceCatalog : ResourceCatalog}
    (state after : WorldState resourceCatalog)
    (proposal : Transfer)
    (entry : BasketEntry) : TransferReceiptLine where
  resourceId := entry.resourceId
  quantity := entry.quantity
  positive := entry.positive
  sourceBefore := state.balance proposal.source entry.resourceId
  sourceAfter := after.balance proposal.source entry.resourceId
  destinationBefore := state.balance proposal.destination entry.resourceId
  destinationAfter := after.balance proposal.destination entry.resourceId

@[simp]
theorem makeTransferReceiptLine_toEntry
    {resourceCatalog : ResourceCatalog}
    (state after : WorldState resourceCatalog)
    (proposal : Transfer)
    (entry : BasketEntry) :
    (makeTransferReceiptLine state after proposal entry).toEntry = entry := by
  cases entry
  rfl

/-- The immutable receipt determined by one accepted transition. -/
def transferReceipt
    {resourceCatalog : ResourceCatalog}
    {state : WorldState resourceCatalog}
    {proposal : Transfer}
    (accepted : AcceptedTransfer state proposal) : TransferReceipt :=
  let after := applyTransferState accepted
  { source := proposal.source
    destination := proposal.destination
    lines := proposal.basket.entries.map
      (makeTransferReceiptLine state after proposal) }

/-- A generated receipt names exactly the basket entries that were moved. -/
@[simp]
theorem transferReceipt_entries
    {resourceCatalog : ResourceCatalog}
    {state : WorldState resourceCatalog}
    {proposal : Transfer}
    (accepted : AcceptedTransfer state proposal) :
    (transferReceipt accepted).lines.map TransferReceiptLine.toEntry =
      proposal.basket.entries := by
  simp [transferReceipt, Function.comp_def]

/-- Apply an accepted transfer and return its replayable receipt atomically. -/
def applyTransfer
    {resourceCatalog : ResourceCatalog}
    {state : WorldState resourceCatalog}
    {proposal : Transfer}
    (accepted : AcceptedTransfer state proposal) :
    WorldState resourceCatalog × TransferReceipt :=
  (applyTransferState accepted, transferReceipt accepted)

/-- Replay a receipt's resource movements against raw canonical holdings. -/
def replayReceipt
    (receipt : TransferReceipt)
    (holdings : List (Holding AccountId)) : List (Holding AccountId) :=
  transferEntriesHoldings receipt.source receipt.destination
    (receipt.lines.map TransferReceiptLine.toEntry) holdings

/-- Replaying a generated receipt reconstructs the exact successor holdings. -/
theorem replay_transferReceipt
    {resourceCatalog : ResourceCatalog}
    {state : WorldState resourceCatalog}
    {proposal : Transfer}
    (accepted : AcceptedTransfer state proposal) :
    replayReceipt (transferReceipt accepted) state.holdings =
      (applyTransferState accepted).holdings := by
  let after := applyTransferState accepted
  have recovered :
      ((proposal.basket.entries.map
        (makeTransferReceiptLine state after proposal)).map
          TransferReceiptLine.toEntry) = proposal.basket.entries := by
    rw [List.map_map]
    induction proposal.basket.entries with
    | nil => rfl
    | cons entry rest ih =>
        simp only [List.map_cons, Function.comp_apply]
        rw [makeTransferReceiptLine_toEntry, ih]
  change transferEntriesHoldings proposal.source proposal.destination
      ((proposal.basket.entries.map
        (makeTransferReceiptLine state after proposal)).map
          TransferReceiptLine.toEntry) state.holdings =
    transferEntriesHoldings proposal.source proposal.destination
      proposal.basket.entries state.holdings
  rw [recovered]

/-- Reconstruct the proved successor state from its generated receipt. -/
def replayTransferState
    {resourceCatalog : ResourceCatalog}
    {state : WorldState resourceCatalog}
    {proposal : Transfer}
    (accepted : AcceptedTransfer state proposal) : WorldState resourceCatalog :=
  let after := applyTransferState accepted
  let replayed := replayReceipt (transferReceipt accepted) state.holdings
  { holdings := replayed
    keysUnique := by
      dsimp [replayed]
      rw [replay_transferReceipt accepted]
      exact after.keysUnique
    resourcesKnown := by
      dsimp [replayed]
      rw [replay_transferReceipt accepted]
      exact after.resourcesKnown
    respectsLimits := by
      dsimp [replayed]
      rw [replay_transferReceipt accepted]
      exact after.respectsLimits }

/-- Receipt replay reconstructs the exact successor `WorldState`. -/
theorem replay_transferReceipt_state
    {resourceCatalog : ResourceCatalog}
    {state : WorldState resourceCatalog}
    {proposal : Transfer}
    (accepted : AcceptedTransfer state proposal) :
    replayTransferState accepted = applyTransferState accepted := by
  apply WorldState.ext_holdings
  exact replay_transferReceipt accepted

/-- Application is independent of which proof term witnesses acceptance. -/
theorem applyTransfer_deterministic
    {resourceCatalog : ResourceCatalog}
    {state : WorldState resourceCatalog}
    {proposal : Transfer}
    (left right : AcceptedTransfer state proposal) :
    applyTransfer left = applyTransfer right := by
  have same : left = right := Subsingleton.elim left right
  subst right
  rfl

/--
Applying an assessment returns one complete successor or no successor. There
is no constructor for a partially applied basket.
-/
def applyAssessment
    {resourceCatalog : ResourceCatalog}
    {state : WorldState resourceCatalog}
    {proposal : Transfer} :
    TransferAssessment state proposal →
      Option (WorldState resourceCatalog × TransferReceipt)
  | .accepted witness => some (applyTransfer witness)
  | .rejected _ _ _ => none

@[simp]
theorem applyAssessment_rejected
    {resourceCatalog : ResourceCatalog}
    {state : WorldState resourceCatalog}
    {proposal : Transfer}
    (issues : List TransferIssue)
    (issuesExact : issues = transferIssues state proposal)
    (nonempty : issues ≠ []) :
    applyAssessment
      (TransferAssessment.rejected issues issuesExact nonempty) = none := rfl

@[simp]
theorem applyAssessment_accepted
    {resourceCatalog : ResourceCatalog}
    {state : WorldState resourceCatalog}
    {proposal : Transfer}
    (accepted : AcceptedTransfer state proposal) :
    applyAssessment (TransferAssessment.accepted accepted) =
      some (applyTransfer accepted) := rfl

/-- Assess and, only on complete acceptance, apply one proposal. -/
def assessAndApply
    {resourceCatalog : ResourceCatalog}
    (state : WorldState resourceCatalog)
    (proposal : Transfer) : Option (WorldState resourceCatalog × TransferReceipt) :=
  applyAssessment (assessTransfer state proposal)

/-- Pure assessment and application have one deterministic result. -/
theorem assessAndApply_deterministic
    {resourceCatalog : ResourceCatalog}
    (state : WorldState resourceCatalog)
    (proposal : Transfer)
    (left right : Option (WorldState resourceCatalog × TransferReceipt))
    (leftExact : left = assessAndApply state proposal)
    (rightExact : right = assessAndApply state proposal) :
    left = right :=
  leftExact.trans rightExact.symm

end Maquina
