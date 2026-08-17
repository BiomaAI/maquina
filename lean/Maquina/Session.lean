import Maquina.Custody
import Maquina.Operation

/-!
# Maquina Active Machine Sessions

An admitted process may wait without holding a worker in place. When dispatch
makes the process active, every declared `activeCustody` port is bound to one
open machine-custody position. The active process carries those exact bindings,
and the simulator state proves they remain open until completion or
cancellation removes the active entry.
-/

namespace Maquina

namespace Basket

/-- `available` contains at least every quantity declared by `required`. -/
def Covers (available required : Basket) : Prop :=
  ∀ entry ∈ required.entries,
    entry.quantity.atoms ≤ available.lookupAtoms entry.resourceId

end Basket

inductive ActiveCustodyIssue where
  | bindingMissing
  | positionMissing (positionId : Nat)
  | shortfall
      (resourceId : ResourceId)
      (required available missing : Nat)
  deriving DecidableEq, Repr

structure ActiveCustodyFailure where
  requirementIndex : Nat
  issues : List ActiveCustodyIssue
  deriving DecidableEq, Repr

private def coverageEntryIssues
    (available : Basket)
    (entry : BasketEntry) : List ActiveCustodyIssue :=
  let held := available.lookupAtoms entry.resourceId
  if entry.quantity.atoms ≤ held then []
  else
    [.shortfall entry.resourceId entry.quantity.atoms held
      (entry.quantity.atoms - held)]

/-- Every independent resource shortfall inside one custody requirement. -/
def activeCustodyCoverageIssues
    (available required : Basket) : List ActiveCustodyIssue :=
  required.entries.flatMap (coverageEntryIssues available)

theorem activeCustodyCoverageIssues_empty_covers
    {available required : Basket}
    (empty : activeCustodyCoverageIssues available required = []) :
    available.Covers required := by
  intro entry entryMem
  have entryEmpty : coverageEntryIssues available entry = [] :=
    (List.flatMap_eq_nil_iff.mp empty) entry entryMem
  by_cases enough :
      entry.quantity.atoms ≤ available.lookupAtoms entry.resourceId
  · exact enough
  · simp [coverageEntryIssues, enough] at entryEmpty

namespace ActiveCustodyDependency

/-- The selected position is open and covers the dependency's exact basket. -/
def HeldBy
    (custody : MachineCustody inventory)
    (dependency : ActiveCustodyDependency Label) : Prop :=
  ∃ position ∈ custody.positions,
    position.id = dependency.positionId ∧
      position.basket.Covers dependency.basket

theorem HeldBy.deposit
    {resourceCatalog : ResourceCatalog}
    {state : WorldState resourceCatalog}
    {proposal : Transfer}
    {custody : MachineCustody inventory}
    {dependency : ActiveCustodyDependency Label}
    (held : dependency.HeldBy custody)
    (accepted : AcceptedTransfer state proposal)
    (destinationExact : proposal.destination = inventory) :
    dependency.HeldBy (custody.deposit accepted destinationExact) := by
  obtain ⟨position, positionMem, idExact, covers⟩ := held
  exact ⟨position, by simp [MachineCustody.deposit, positionMem], idExact, covers⟩

theorem HeldBy.remove
    {custody : MachineCustody inventory}
    {dependency : ActiveCustodyDependency Label}
    {removedId : Nat}
    (held : dependency.HeldBy custody)
    (different : dependency.positionId ≠ removedId) :
    dependency.HeldBy (custody.remove removedId) := by
  obtain ⟨position, positionMem, idExact, covers⟩ := held
  refine ⟨position, ?_, idExact, covers⟩
  simp only [MachineCustody.remove, List.mem_filter]
  exact ⟨positionMem, by
    simp only [decide_eq_true_eq]
    intro same
    apply different
    rw [← idExact, same]⟩

end ActiveCustodyDependency

structure AcceptedActiveCustodyPort
    (custody : MachineCustody inventory)
    (bindings : CustodyBindings Label)
    (port : ProcessPort Label) where
  dependency : ActiveCustodyDependency Label
  requirementExact : ActiveCustodyDependency.Matches port dependency
  bindingExact : bindings.resolve port.label = some dependency.positionId
  held : dependency.HeldBy custody

inductive ActiveCustodyPortAssessment
    (custody : MachineCustody inventory)
    (bindings : CustodyBindings Label)
    (port : ProcessPort Label) where
  | accepted (witness : AcceptedActiveCustodyPort custody bindings port)
  | rejected (issues : List ActiveCustodyIssue) (nonempty : issues ≠ [])

def assessActiveCustodyPort
    (custody : MachineCustody inventory)
    (bindings : CustodyBindings Label)
    (port : ProcessPort Label) :
    ActiveCustodyPortAssessment custody bindings port :=
  match bindingExact : bindings.resolve port.label with
  | none => .rejected [.bindingMissing] (by simp)
  | some positionId =>
      match positionExact : custody.position? positionId with
      | none => .rejected [.positionMissing positionId] (by simp)
      | some position =>
          let issues := activeCustodyCoverageIssues position.basket port.basket
          if empty : issues = [] then
            .accepted
              { dependency :=
                  { label := port.label
                    basket := port.basket
                    positionId }
                requirementExact := ⟨rfl, rfl⟩
                bindingExact := bindingExact
                held :=
                  ⟨position, custody.position?_mem positionExact,
                    custody.position?_id positionExact,
                    activeCustodyCoverageIssues_empty_covers empty⟩ }
          else .rejected issues empty

/-- Exact, proof-backed bindings for every declared active-custody port. -/
structure ActiveCustodyBinding
    (custody : MachineCustody inventory)
    (bindings : CustodyBindings Label)
    (ports : List (ProcessPort Label)) where
  dependencies : List (ActiveCustodyDependency Label)
  exact : dependencies.map (fun dependency =>
      (dependency.label, dependency.basket)) =
    ports.map (fun port => (port.label, port.basket))
  bindingsExact : ∀ dependency ∈ dependencies,
    bindings.resolve dependency.label = some dependency.positionId
  held : ∀ dependency ∈ dependencies, dependency.HeldBy custody

inductive ActiveCustodyAssessment
    (custody : MachineCustody inventory)
    (bindings : CustodyBindings Label)
    (ports : List (ProcessPort Label)) where
  | accepted (witness : ActiveCustodyBinding custody bindings ports)
  | rejected
      (failures : List ActiveCustodyFailure)
      (nonempty : failures ≠ [])

private def assessActiveCustodyFrom
    (custody : MachineCustody inventory)
    (bindings : CustodyBindings Label)
    (index : Nat) :
    (ports : List (ProcessPort Label)) →
      ActiveCustodyAssessment custody bindings ports
  | [] =>
      .accepted
        { dependencies := []
          exact := rfl
          bindingsExact := by simp
          held := by simp }
  | port :: rest =>
      let current := assessActiveCustodyPort custody bindings port
      let suffix := assessActiveCustodyFrom custody bindings (index + 1) rest
      match current, suffix with
      | .accepted accepted, .accepted acceptedRest =>
          .accepted
            { dependencies := accepted.dependency :: acceptedRest.dependencies
              exact := by
                simp only [List.map_cons]
                rw [acceptedRest.exact]
                rw [accepted.requirementExact.1, accepted.requirementExact.2]
              bindingsExact := by
                intro dependency dependencyMem
                simp only [List.mem_cons] at dependencyMem
                rcases dependencyMem with isCurrent | inRest
                · subst dependency
                  simpa [accepted.requirementExact.1] using accepted.bindingExact
                · exact acceptedRest.bindingsExact dependency inRest
              held := by
                intro dependency dependencyMem
                simp only [List.mem_cons] at dependencyMem
                rcases dependencyMem with isCurrent | inRest
                · subst dependency
                  exact accepted.held
                · exact acceptedRest.held dependency inRest }
      | .rejected issues _, .accepted _ =>
          .rejected [{ requirementIndex := index, issues }] (by simp)
      | .accepted _, .rejected failures nonempty =>
          .rejected failures nonempty
      | .rejected issues _, .rejected failures _ =>
          .rejected ({ requirementIndex := index, issues } :: failures) (by simp)

/-- Assess every active-custody port and retain every independent failure. -/
def assessActiveCustody
    (custody : MachineCustody inventory)
    (bindings : CustodyBindings Label)
    (ports : List (ProcessPort Label)) :
    ActiveCustodyAssessment custody bindings ports :=
  assessActiveCustodyFrom custody bindings 0 ports

theorem Machine.positionId_mem_of_activeDependency
    {machine : Machine schema}
    {queue : MachineProcessingQueue schema}
    {dependency : ActiveCustodyDependency schema.Label}
    (queueMem : queue ∈ machine.processingQueues)
    (dependencyMem : dependency ∈ queue.activeCustodyDependencies) :
    dependency.positionId ∈ machine.activeCustodyPositionIds := by
  apply List.mem_map.mpr
  refine ⟨dependency, ?_, rfl⟩
  exact List.mem_flatMap.mpr ⟨queue, queueMem, dependencyMem⟩

theorem Machine.ActiveDependenciesSatisfy.deposit
    {resourceCatalog : ResourceCatalog}
    {state : WorldState resourceCatalog}
    {proposal : Transfer}
    {machine : Machine schema}
    {custody : MachineCustody machine.inventory}
    (satisfies : machine.ActiveDependenciesSatisfy
      (ActiveCustodyDependency.HeldBy custody))
    (accepted : AcceptedTransfer state proposal)
    (destinationExact : proposal.destination = machine.inventory) :
    machine.ActiveDependenciesSatisfy
      (ActiveCustodyDependency.HeldBy
        (custody.deposit accepted destinationExact)) := by
  intro queue queueMem dependency dependencyMem
  exact (satisfies queue queueMem dependency dependencyMem).deposit
    accepted destinationExact

theorem Machine.ActiveDependenciesSatisfy.remove
    {machine : Machine schema}
    {custody : MachineCustody machine.inventory}
    {removedId : Nat}
    (satisfies : machine.ActiveDependenciesSatisfy
      (ActiveCustodyDependency.HeldBy custody))
    (unused : ¬machine.CustodyPositionInUse removedId) :
    machine.ActiveDependenciesSatisfy
      (ActiveCustodyDependency.HeldBy (custody.remove removedId)) := by
  intro queue queueMem dependency dependencyMem
  apply (satisfies queue queueMem dependency dependencyMem).remove
  intro same
  apply unused
  rw [← same]
  exact machine.positionId_mem_of_activeDependency queueMem dependencyMem

end Maquina
