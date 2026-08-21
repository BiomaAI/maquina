import Maquina.Relation

/-!
# Derived Machine Manifests

A manifest is proof about Resources reachable through active resource-backed
relations. It is never stored as authoritative inventory and has no mutation
API. Operations use these facts as guards and still transform resources only
through their declared Processes.
-/

namespace Maquina

/-- Directory data connecting a Body identity to its inventory account. -/
structure MachineAddress where
  body : ResourceId
  inventory : AccountId
  deriving DecidableEq, Repr

/-- A finite game-owned directory with one address per Body. -/
structure MachineDirectory where
  entries : List MachineAddress
  bodiesUnique : (entries.map MachineAddress.body).Nodup
  deriving Repr

namespace MachineDirectory

def resolve (directory : MachineDirectory) (body : ResourceId) : Option AccountId :=
  (directory.entries.find? fun entry => decide (entry.body = body)).map
    MachineAddress.inventory

end MachineDirectory

/-- A resource requirement routed through one proposed relation path. -/
structure ReachableResourceRequirement (LinkKey : Type) where
  root : ResourceId
  path : RelationPath LinkKey
  resourceId : ResourceId
  minimum : Quantity
  positive : 0 < minimum.atoms
  deriving Repr

inductive ReachableResourceIssue where
  | wrongOrigin (expected actual : ResourceId)
  | pathRejected (issues : List RelationPathIssue)
  | destinationUnknown (body : ResourceId)
  | insufficient (account : AccountId) (resourceId : ResourceId)
      (required available : Nat)
  deriving DecidableEq, Repr

/-- Complete assessment against current relations, directory, and holdings. -/
def reachableResourceIssues
    [DecidableEq RelationEndpoint]
    (model : RelationModel Kind EndpointKey LinkKey)
    (policy : RelationPolicy Kind)
    (directory : MachineDirectory)
    (world : WorldState resourceCatalog)
    (requirement : ReachableResourceRequirement LinkKey) :
    List ReachableResourceIssue :=
  let originIssues :=
    if requirement.path.origin.body = requirement.root then []
    else [.wrongOrigin requirement.root requirement.path.origin.body]
  let pathIssues := relationPathIssues model policy world requirement.path
  let pathFailures := if pathIssues = [] then [] else [.pathRejected pathIssues]
  match directory.resolve (requirement.path.destination model).body with
  | none => originIssues ++ pathFailures ++
      [.destinationUnknown (requirement.path.destination model).body]
  | some account =>
      let available := (world.balance account requirement.resourceId).atoms
      let holdingIssues :=
        if requirement.minimum.atoms ≤ available then []
        else [.insufficient account requirement.resourceId
          requirement.minimum.atoms available]
      originIssues ++ pathFailures ++ holdingIssues

/-- Accepted evidence is tied to the exact world and exact candidate path. -/
structure AcceptedReachableResource
    [DecidableEq RelationEndpoint]
    (model : RelationModel Kind EndpointKey LinkKey)
    (policy : RelationPolicy Kind)
    (directory : MachineDirectory)
    (world : WorldState resourceCatalog)
    (requirement : ReachableResourceRequirement LinkKey) : Type where
  issuesEmpty :
    reachableResourceIssues model policy directory world requirement = []

def assessReachableResource
    [DecidableEq RelationEndpoint]
    (model : RelationModel Kind EndpointKey LinkKey)
    (policy : RelationPolicy Kind)
    (directory : MachineDirectory)
    (world : WorldState resourceCatalog)
    (requirement : ReachableResourceRequirement LinkKey) :
    Except (List ReachableResourceIssue)
      (AcceptedReachableResource model policy directory world requirement) :=
  let issues := reachableResourceIssues model policy directory world requirement
  if empty : issues = [] then .ok ⟨empty⟩ else .error issues

/-- One entry in a pure, rebuildable Machine manifest. -/
structure MachineManifestEntry
    [DecidableEq RelationEndpoint]
    (model : RelationModel Kind EndpointKey LinkKey)
    (policy : RelationPolicy Kind)
    (directory : MachineDirectory)
    (world : WorldState resourceCatalog)
    (root : ResourceId) where
  requirement : ReachableResourceRequirement LinkKey
  rootExact : requirement.root = root
  reachable : AcceptedReachableResource model policy directory world requirement

/-- A manifest is only a collection of accepted reachability evidence. -/
structure MachineManifest
    [DecidableEq RelationEndpoint]
    (model : RelationModel Kind EndpointKey LinkKey)
    (policy : RelationPolicy Kind)
    (directory : MachineDirectory)
    (world : WorldState resourceCatalog)
    (root : ResourceId) where
  entries : List (MachineManifestEntry model policy directory world root)

end Maquina
