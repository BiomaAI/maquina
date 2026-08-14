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
  | unknownSource (accountId : AccountId)
  | unknownDestination (accountId : AccountId)
  | unknownObject (objectId : ObjectId)
  | shortfall
      (objectId : ObjectId)
      (requested : Nat)
      (available : Nat)
      (missing : Nat)
  deriving DecidableEq, Repr

private def entryIssues
    {accounts : AccountCatalog}
    {catalog : Catalog}
    (state : WorldState accounts catalog)
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
    {accounts : AccountCatalog}
    {catalog : Catalog}
    (state : WorldState accounts catalog)
    (proposal : Transfer) : List TransferIssue :=
  let sameAccountIssues :=
    if proposal.source = proposal.destination then [.sameAccount] else []
  let sourceIssues :=
    match accounts.lookup proposal.source with
    | none => [.unknownSource proposal.source]
    | some _ => []
  let destinationIssues :=
    match accounts.lookup proposal.destination with
    | none => [.unknownDestination proposal.destination]
    | some _ => []
  sameAccountIssues ++ sourceIssues ++ destinationIssues ++
    proposal.basket.entries.flatMap (entryIssues state proposal.source)

/-- Proof that a concrete proposal passed the authoritative assessment. -/
structure AcceptedTransfer
    {accounts : AccountCatalog}
    {catalog : Catalog}
    (state : WorldState accounts catalog)
    (proposal : Transfer) : Prop where
  issuesEmpty : transferIssues state proposal = []

/-- Assessment returns either every issue or a proof-carrying acceptance. -/
inductive TransferAssessment
    {accounts : AccountCatalog}
    {catalog : Catalog}
    (state : WorldState accounts catalog)
    (proposal : Transfer) where
  | accepted (witness : AcceptedTransfer state proposal)
  | rejected
      (issues : List TransferIssue)
      (issuesExact : issues = transferIssues state proposal)
      (nonempty : issues ≠ [])

/-- Pure, deterministic assessment of one transfer proposal. -/
def assessTransfer
    {accounts : AccountCatalog}
    {catalog : Catalog}
    (state : WorldState accounts catalog)
    (proposal : Transfer) : TransferAssessment state proposal :=
  let issues := transferIssues state proposal
  if empty : issues = [] then
    .accepted ⟨empty⟩
  else
    .rejected issues rfl empty

/-! ## Account assessment guarantees -/

/-- An accepted transfer cannot use an unknown source account. -/
theorem AcceptedTransfer.sourceKnown
    {accounts : AccountCatalog}
    {catalog : Catalog}
    {state : WorldState accounts catalog}
    {proposal : Transfer}
    (accepted : AcceptedTransfer state proposal) :
    AccountCatalog.Known accounts proposal.source := by
  cases found : accounts.lookup proposal.source with
  | none =>
      have issuesEmpty := accepted.issuesEmpty
      simp [transferIssues, found] at issuesEmpty
  | some spec =>
      exact ⟨spec, found⟩

/-- An accepted transfer cannot use an unknown destination account. -/
theorem AcceptedTransfer.destinationKnown
    {accounts : AccountCatalog}
    {catalog : Catalog}
    {state : WorldState accounts catalog}
    {proposal : Transfer}
    (accepted : AcceptedTransfer state proposal) :
    AccountCatalog.Known accounts proposal.destination := by
  cases found : accounts.lookup proposal.destination with
  | none =>
      have issuesEmpty := accepted.issuesEmpty
      simp [transferIssues, found] at issuesEmpty
  | some spec =>
      exact ⟨spec, found⟩

/-- Accepted transfers always move between two distinct account identities. -/
theorem AcceptedTransfer.accountsDistinct
    {accounts : AccountCatalog}
    {catalog : Catalog}
    {state : WorldState accounts catalog}
    {proposal : Transfer}
    (accepted : AcceptedTransfer state proposal) :
    proposal.source ≠ proposal.destination := by
  intro same
  have issuesEmpty := accepted.issuesEmpty
  simp [transferIssues, same] at issuesEmpty

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

end Maquina
