import Maquina.Inventory

/-!
# Maquina Possession

Proof-carrying, non-mutating observation that one account currently holds an
entire basket. Possession is indexed by the exact world being observed; it is
an eligibility fact, not a reservation or transferable authority.
-/

namespace Maquina

/-- A game-defined account role attached to one required basket. -/
structure PossessionPort (Label : Type) where
  label : Label
  basket : Basket
  nonempty : basket.entries ≠ []
  deriving Repr

/-- Runtime resolution of game-defined possession roles to concrete accounts. -/
structure PossessionBindings (Label : Type) where
  resolve : Label → AccountId

/-- One declarative request to observe a basket at an account. -/
structure PossessionRequirement where
  account : AccountId
  basket : Basket
  deriving Repr

/-- Every reason a possession requirement is not currently satisfied. -/
inductive PossessionIssue where
  | unknownResource (resourceId : ResourceId)
  | shortfall
      (resourceId : ResourceId)
      (required available missing : Nat)
  deriving DecidableEq, Repr

/-- One account-qualified rejected requirement for operation diagnostics. -/
structure PossessionFailure where
  account : AccountId
  issues : List PossessionIssue
  deriving DecidableEq, Repr

private def possessionEntryIssues
    {resourceCatalog : ResourceCatalog}
    (state : WorldState resourceCatalog)
    (account : AccountId)
    (entry : BasketEntry) : List PossessionIssue :=
  match resourceCatalog.lookup entry.resourceId with
  | none => [.unknownResource entry.resourceId]
  | some _ =>
      let available := (state.balance account entry.resourceId).atoms
      if entry.quantity.atoms ≤ available then []
      else
        [.shortfall entry.resourceId entry.quantity.atoms available
          (entry.quantity.atoms - available)]

/-- Assess every basket entry and retain every independent shortfall. -/
def possessionIssues
    {resourceCatalog : ResourceCatalog}
    (state : WorldState resourceCatalog)
    (requirement : PossessionRequirement) : List PossessionIssue :=
  requirement.basket.entries.flatMap
    (possessionEntryIssues state requirement.account)

/-- Proof that an exact requirement is satisfied in an exact world. -/
structure AcceptedPossession
    {resourceCatalog : ResourceCatalog}
    (state : WorldState resourceCatalog)
    (requirement : PossessionRequirement) : Prop where
  issuesEmpty : possessionIssues state requirement = []

/-- Assessment exposes either proof-carrying acceptance or all exact issues. -/
inductive PossessionAssessment
    {resourceCatalog : ResourceCatalog}
    (state : WorldState resourceCatalog)
    (requirement : PossessionRequirement) where
  | accepted (witness : AcceptedPossession state requirement)
  | rejected
      (issues : List PossessionIssue)
      (issuesExact : issues = possessionIssues state requirement)
      (nonempty : issues ≠ [])

def assessPossession
    {resourceCatalog : ResourceCatalog}
    (state : WorldState resourceCatalog)
    (requirement : PossessionRequirement) :
    PossessionAssessment state requirement :=
  let issues := possessionIssues state requirement
  if empty : issues = [] then .accepted ⟨empty⟩
  else .rejected issues rfl empty

theorem AcceptedPossession.resourceKnown
    {resourceCatalog : ResourceCatalog}
    {state : WorldState resourceCatalog}
    {requirement : PossessionRequirement}
    (accepted : AcceptedPossession state requirement)
    {entry : BasketEntry}
    (entryMem : entry ∈ requirement.basket.entries) :
    ∃ spec, resourceCatalog.lookup entry.resourceId = some spec := by
  have flatEmpty := accepted.issuesEmpty
  unfold possessionIssues at flatEmpty
  have entryEmpty :
      possessionEntryIssues state requirement.account entry = [] :=
    (List.flatMap_eq_nil_iff.mp flatEmpty) entry entryMem
  cases found : resourceCatalog.lookup entry.resourceId with
  | none => simp [possessionEntryIssues, found] at entryEmpty
  | some spec => exact ⟨spec, rfl⟩

theorem AcceptedPossession.funded
    {resourceCatalog : ResourceCatalog}
    {state : WorldState resourceCatalog}
    {requirement : PossessionRequirement}
    (accepted : AcceptedPossession state requirement)
    {entry : BasketEntry}
    (entryMem : entry ∈ requirement.basket.entries) :
    entry.quantity.atoms ≤
      (state.balance requirement.account entry.resourceId).atoms := by
  have flatEmpty := accepted.issuesEmpty
  unfold possessionIssues at flatEmpty
  have entryEmpty :
      possessionEntryIssues state requirement.account entry = [] :=
    (List.flatMap_eq_nil_iff.mp flatEmpty) entry entryMem
  obtain ⟨spec, found⟩ := accepted.resourceKnown entryMem
  by_cases enough : entry.quantity.atoms ≤
      (state.balance requirement.account entry.resourceId).atoms
  · exact enough
  · simp [possessionEntryIssues, found, enough] at entryEmpty

/-- Exact observable evidence for one satisfied basket entry. -/
structure PossessionReceiptLine where
  resourceId : ResourceId
  required : Quantity
  available : Quantity
  deriving Repr

/-- A non-mutating account-qualified observation receipt. -/
structure PossessionReceipt where
  account : AccountId
  lines : List PossessionReceiptLine
  deriving Repr

def possessionReceipt
    {resourceCatalog : ResourceCatalog}
    {state : WorldState resourceCatalog}
    {requirement : PossessionRequirement}
    (_accepted : AcceptedPossession state requirement) : PossessionReceipt :=
  { account := requirement.account
    lines := requirement.basket.entries.map fun entry =>
      { resourceId := entry.resourceId
        required := entry.quantity
        available := state.balance requirement.account entry.resourceId } }

@[simp]
theorem possessionReceipt_account
    {resourceCatalog : ResourceCatalog}
    {state : WorldState resourceCatalog}
    {requirement : PossessionRequirement}
    (accepted : AcceptedPossession state requirement) :
    (possessionReceipt accepted).account = requirement.account := rfl

theorem possessionReceipt_lines
    {resourceCatalog : ResourceCatalog}
    {state : WorldState resourceCatalog}
    {requirement : PossessionRequirement}
    (accepted : AcceptedPossession state requirement) :
    (possessionReceipt accepted).lines.map
        (fun line => (line.resourceId, line.required)) =
      requirement.basket.entries.map
        (fun entry => (entry.resourceId, entry.quantity)) := by
  simp [possessionReceipt]

/-- Observing possession cannot produce a successor world. -/
theorem possession_observes_exact_world
    {resourceCatalog : ResourceCatalog}
    {state : WorldState resourceCatalog}
    {requirement : PossessionRequirement}
    (_accepted : AcceptedPossession state requirement) : state = state := rfl

end Maquina
