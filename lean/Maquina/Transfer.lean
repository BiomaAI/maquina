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
