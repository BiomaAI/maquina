import Maquina.Inventory

/-!
# Maquina Transfers

Pure transfer proposals, structured assessment, accepted witnesses, and
receipt vocabulary.
-/

namespace Maquina

/-- A proposal to move one canonical basket atomically between two accounts. -/
structure Transfer (Account : Type) where
  source : Account
  destination : Account
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

private def entryIssues {Account : Type} [DecidableEq Account]
    {catalog : Catalog}
    (state : WorldState Account catalog)
    (source : Account)
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
def transferIssues {Account : Type} [DecidableEq Account]
    {catalog : Catalog}
    (state : WorldState Account catalog)
    (proposal : Transfer Account) : List TransferIssue :=
  let accountIssues :=
    if proposal.source = proposal.destination then [.sameAccount] else []
  accountIssues ++
    proposal.basket.entries.flatMap (entryIssues state proposal.source)

/-- Proof that a concrete proposal passed the authoritative assessment. -/
structure AcceptedTransfer {Account : Type} [DecidableEq Account]
    {catalog : Catalog}
    (state : WorldState Account catalog)
    (proposal : Transfer Account) : Prop where
  issuesEmpty : transferIssues state proposal = []

/-- Assessment returns either every issue or a proof-carrying acceptance. -/
inductive TransferAssessment {Account : Type} [DecidableEq Account]
    {catalog : Catalog}
    (state : WorldState Account catalog)
    (proposal : Transfer Account) where
  | accepted (witness : AcceptedTransfer state proposal)
  | rejected
      (issues : List TransferIssue)
      (issuesExact : issues = transferIssues state proposal)
      (nonempty : issues ≠ [])

/-- Pure, deterministic assessment of one transfer proposal. -/
def assessTransfer {Account : Type} [DecidableEq Account]
    {catalog : Catalog}
    (state : WorldState Account catalog)
    (proposal : Transfer Account) : TransferAssessment state proposal :=
  let issues := transferIssues state proposal
  if empty : issues = [] then
    .accepted ⟨empty⟩
  else
    .rejected issues rfl empty

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
structure TransferReceipt (Account : Type) where
  source : Account
  destination : Account
  lines : List TransferReceiptLine
  deriving Repr

end Maquina
