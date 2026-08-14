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
  | unknownObject (objectId : ObjectId)
  | shortfall
      (objectId : ObjectId)
      (requested : Nat)
      (available : Nat)
      (missing : Nat)
  deriving DecidableEq, Repr

private def entryIssues
    {catalog : Catalog}
    (state : WorldState catalog)
    (source : AccountId)
    (entry : BasketEntry) : List TransferIssue :=
  match catalog.lookup entry.objectId with
  | none => [.unknownObject entry.objectId]
  | some _ =>
      let available := (state.balance source entry.objectId).atoms
      if entry.quantity.atoms ≤ available then
        []
      else
        [.shortfall
          entry.objectId
          entry.quantity.atoms
          available
          (entry.quantity.atoms - available)]

/--
Assessment collects all independent object issues instead of stopping at the
first failure.
-/
def transferIssues
    {catalog : Catalog}
    (state : WorldState catalog)
    (proposal : Transfer) : List TransferIssue :=
  let accountIssues :=
    if proposal.source = proposal.destination then [.sameAccount] else []
  accountIssues ++
    proposal.basket.entries.flatMap (entryIssues state proposal.source)

/-- Proof that a concrete proposal passed the authoritative assessment. -/
structure AcceptedTransfer
    {catalog : Catalog}
    (state : WorldState catalog)
    (proposal : Transfer) : Prop where
  issuesEmpty : transferIssues state proposal = []

/-- Assessment returns either every issue or a proof-carrying acceptance. -/
inductive TransferAssessment
    {catalog : Catalog}
    (state : WorldState catalog)
    (proposal : Transfer) where
  | accepted (witness : AcceptedTransfer state proposal)
  | rejected
      (issues : List TransferIssue)
      (issuesExact : issues = transferIssues state proposal)
      (nonempty : issues ≠ [])

/-- Pure, deterministic assessment of one transfer proposal. -/
def assessTransfer
    {catalog : Catalog}
    (state : WorldState catalog)
    (proposal : Transfer) : TransferAssessment state proposal :=
  let issues := transferIssues state proposal
  if empty : issues = [] then
    .accepted ⟨empty⟩
  else
    .rejected issues rfl empty

/-- Accepted transfers always move between two distinct account identities. -/
theorem AcceptedTransfer.accountsDistinct
    {catalog : Catalog}
    {state : WorldState catalog}
    {proposal : Transfer}
    (accepted : AcceptedTransfer state proposal) :
    proposal.source ≠ proposal.destination := by
  intro same
  have issuesEmpty := accepted.issuesEmpty
  simp [transferIssues, same] at issuesEmpty

/-- Every entry in an accepted basket resolves to an object definition. -/
theorem AcceptedTransfer.objectKnown
    {catalog : Catalog}
    {state : WorldState catalog}
    {proposal : Transfer}
    (accepted : AcceptedTransfer state proposal)
    {entry : BasketEntry}
    (entryMem : entry ∈ proposal.basket.entries) :
    ∃ spec, catalog.lookup entry.objectId = some spec := by
  have flatEmpty :
      proposal.basket.entries.flatMap
          (entryIssues state proposal.source) = [] := by
    have issuesEmpty := accepted.issuesEmpty
    unfold transferIssues at issuesEmpty
    exact (List.append_eq_nil_iff.mp issuesEmpty).2
  have issueEmpty : entryIssues state proposal.source entry = [] :=
    (List.flatMap_eq_nil_iff.mp flatEmpty) entry entryMem
  cases found : catalog.lookup entry.objectId with
  | none => simp [entryIssues, found] at issueEmpty
  | some spec => exact ⟨spec, rfl⟩

/-- Every entry in an accepted basket is fully funded by the source balance. -/
theorem AcceptedTransfer.funded
    {catalog : Catalog}
    {state : WorldState catalog}
    {proposal : Transfer}
    (accepted : AcceptedTransfer state proposal)
    {entry : BasketEntry}
    (entryMem : entry ∈ proposal.basket.entries) :
    entry.quantity.atoms ≤
      (state.balance proposal.source entry.objectId).atoms := by
  have flatEmpty :
      proposal.basket.entries.flatMap
          (entryIssues state proposal.source) = [] := by
    have issuesEmpty := accepted.issuesEmpty
    unfold transferIssues at issuesEmpty
    exact (List.append_eq_nil_iff.mp issuesEmpty).2
  have issueEmpty : entryIssues state proposal.source entry = [] :=
    (List.flatMap_eq_nil_iff.mp flatEmpty) entry entryMem
  obtain ⟨spec, found⟩ := accepted.objectKnown entryMem
  by_cases funded : entry.quantity.atoms ≤
      (state.balance proposal.source entry.objectId).atoms
  · exact funded
  · simp [entryIssues, found, funded] at issueEmpty

/-! ## Receipt vocabulary -/

/-- The exact before/after evidence for one transferred object. -/
structure TransferReceiptLine where
  objectId : ObjectId
  quantity : Quantity
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
    balanceAtoms holdings source entry.objectId - entry.quantity.atoms
  let debited :=
    setBalance holdings source entry.objectId sourceAfter
  let destinationAfter :=
    balanceAtoms holdings destination entry.objectId + entry.quantity.atoms
  setBalance debited destination entry.objectId destinationAfter

/-- Moving one entry preserves canonical `(account, object)` key uniqueness. -/
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

/-- Moving a known object preserves the known-object invariant. -/
theorem transferEntryHoldings_objectsKnown
    {catalog : Catalog}
    (holdings : List (Holding AccountId))
    (source destination : AccountId)
    (entry : BasketEntry)
    (known : ObjectsKnown catalog holdings)
    (entryKnown : ∃ spec, catalog.lookup entry.objectId = some spec) :
    ObjectsKnown catalog
      (transferEntryHoldings holdings source destination entry) := by
  unfold transferEntryHoldings
  apply ObjectsKnown.setBalance
  · apply ObjectsKnown.setBalance
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
        source entry.objectId =
      balanceAtoms holdings source entry.objectId - entry.quantity.atoms := by
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
        destination entry.objectId =
      balanceAtoms holdings destination entry.objectId + entry.quantity.atoms := by
  unfold transferEntryHoldings
  exact balanceAtoms_setBalance_same _ _ _ _

/-- Moving one entry leaves every other object balance unchanged. -/
theorem transferEntryHoldings_otherObject
    (holdings : List (Holding AccountId))
    (source destination queriedAccount : AccountId)
    (entry : BasketEntry)
    (queriedObject : ObjectId)
    (different : entry.objectId ≠ queriedObject) :
    balanceAtoms (transferEntryHoldings holdings source destination entry)
        queriedAccount queriedObject =
      balanceAtoms holdings queriedAccount queriedObject := by
  unfold transferEntryHoldings
  rw [balanceAtoms_setBalance_other]
  · rw [balanceAtoms_setBalance_other]
    exact Or.inr different
  · exact Or.inr different

/-- A funded single-entry move conserves that object's global total. -/
theorem transferEntryHoldings_total
    (holdings : List (Holding AccountId))
    (source destination : AccountId)
    (entry : BasketEntry)
    (unique : (holdings.map Holding.key).Nodup)
    (distinct : source ≠ destination)
    (funded : entry.quantity.atoms ≤
      balanceAtoms holdings source entry.objectId) :
    totalAtomsFor (transferEntryHoldings holdings source destination entry)
        entry.objectId =
      totalAtomsFor holdings entry.objectId := by
  let sourceAfter :=
    balanceAtoms holdings source entry.objectId - entry.quantity.atoms
  let debited := setBalance holdings source entry.objectId sourceAfter
  have debitedUnique : (debited.map Holding.key).Nodup := by
    exact setBalance_keysUnique holdings source entry.objectId sourceAfter unique
  have destinationLe :
      balanceAtoms debited destination entry.objectId ≤
        totalAtomsFor debited entry.objectId :=
    balanceAtoms_le_totalAtomsFor debited destination entry.objectId
  have sourceLe :
      balanceAtoms holdings source entry.objectId ≤
        totalAtomsFor holdings entry.objectId :=
    balanceAtoms_le_totalAtomsFor holdings source entry.objectId
  have destinationUnchanged :
      balanceAtoms debited destination entry.objectId =
        balanceAtoms holdings destination entry.objectId := by
    exact balanceAtoms_setBalance_other holdings source destination
      entry.objectId entry.objectId sourceAfter (Or.inl distinct)
  have debitedTotal :
      totalAtomsFor debited entry.objectId =
        totalAtomsFor holdings entry.objectId -
          balanceAtoms holdings source entry.objectId + sourceAfter := by
    exact totalAtomsFor_setBalance_same holdings source entry.objectId
      sourceAfter unique
  unfold transferEntryHoldings
  change totalAtomsFor
      (setBalance debited destination entry.objectId
        (balanceAtoms holdings destination entry.objectId +
          entry.quantity.atoms)) entry.objectId = _
  rw [totalAtomsFor_setBalance_same _ _ _ _ debitedUnique]
  rw [destinationUnchanged, debitedTotal]
  rw [destinationUnchanged, debitedTotal] at destinationLe
  dsimp [sourceAfter] at destinationLe ⊢
  omega

/-- A single-entry move preserves every unrelated object's global total. -/
theorem transferEntryHoldings_total_other
    (holdings : List (Holding AccountId))
    (source destination : AccountId)
    (entry : BasketEntry)
    (queriedObject : ObjectId)
    (different : entry.objectId ≠ queriedObject) :
    totalAtomsFor (transferEntryHoldings holdings source destination entry)
        queriedObject =
      totalAtomsFor holdings queriedObject := by
  unfold transferEntryHoldings
  rw [totalAtomsFor_setBalance_other]
  · exact totalAtomsFor_setBalance_other _ _ _ _ _ different
  · exact different

/-! ## Atomic basket transition -/

/--
Apply every entry in a basket to raw holdings. Recursing through the tail first
lets object uniqueness make each entry independent of every other entry.
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

/-- A whole basket of known objects preserves the known-object invariant. -/
theorem transferEntriesHoldings_objectsKnown
    {catalog : Catalog}
    (source destination : AccountId)
    (entries : List BasketEntry)
    (holdings : List (Holding AccountId))
    (known : ObjectsKnown catalog holdings)
    (entriesKnown : ∀ entry, entry ∈ entries →
      ∃ spec, catalog.lookup entry.objectId = some spec) :
    ObjectsKnown catalog
      (transferEntriesHoldings source destination entries holdings) := by
  induction entries generalizing holdings with
  | nil => exact known
  | cons entry rest ih =>
      apply transferEntryHoldings_objectsKnown
      · exact ih holdings known fun restEntry restMem =>
          entriesKnown restEntry (List.mem_cons_of_mem entry restMem)
      · exact entriesKnown entry (by simp)

/-- Entries for other objects cannot affect a queried balance. -/
theorem transferEntriesHoldings_balance_not_mem
    (source destination : AccountId)
    (entries : List BasketEntry)
    (holdings : List (Holding AccountId))
    (queriedAccount : AccountId)
    (queriedObject : ObjectId)
    (absent : queriedObject ∉ entries.map BasketEntry.objectId) :
    balanceAtoms
        (transferEntriesHoldings source destination entries holdings)
        queriedAccount queriedObject =
      balanceAtoms holdings queriedAccount queriedObject := by
  induction entries generalizing holdings with
  | nil => rfl
  | cons entry rest ih =>
      simp only [List.map_cons, List.mem_cons, not_or] at absent
      rw [transferEntriesHoldings]
      rw [transferEntryHoldings_otherObject]
      · exact ih holdings absent.2
      · intro same
        exact absent.1 same.symm

/-- A funded, object-unique basket transition conserves every global total. -/
theorem transferEntriesHoldings_total
    (source destination : AccountId)
    (entries : List BasketEntry)
    (holdings : List (Holding AccountId))
    (unique : (holdings.map Holding.key).Nodup)
    (distinct : source ≠ destination)
    (entriesUnique : (entries.map BasketEntry.objectId).Nodup)
    (funded : ∀ entry, entry ∈ entries →
      entry.quantity.atoms ≤ balanceAtoms holdings source entry.objectId)
    (queriedObject : ObjectId) :
    totalAtomsFor
        (transferEntriesHoldings source destination entries holdings)
        queriedObject =
      totalAtomsFor holdings queriedObject := by
  induction entries generalizing holdings with
  | nil => rfl
  | cons entry rest ih =>
      have uniqueParts := List.nodup_cons.mp entriesUnique
      have restFunded : ∀ restEntry, restEntry ∈ rest →
          restEntry.quantity.atoms ≤
            balanceAtoms holdings source restEntry.objectId :=
        fun restEntry restMem =>
          funded restEntry (List.mem_cons_of_mem entry restMem)
      have restKeysUnique :=
        transferEntriesHoldings_keysUnique source destination rest holdings unique
      have restTotal := ih holdings unique uniqueParts.2 restFunded
      rw [transferEntriesHoldings]
      by_cases sameObject : entry.objectId = queriedObject
      · subst queriedObject
        have sourceUnchanged :=
          transferEntriesHoldings_balance_not_mem source destination rest
            holdings source entry.objectId uniqueParts.1
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
            source destination entry queriedObject sameObject)
        exact restTotal

end Maquina
