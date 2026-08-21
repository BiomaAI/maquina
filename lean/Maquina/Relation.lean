import Maquina.Machine
import Maquina.ResourceFamily

/-!
# Resource-backed Machine Relations

Relations are not a second mutable world model. Open endpoints, attached links,
and link leases are Resources. Ordinary declared Processes consume and produce
those Resources; this module only validates and projects the resulting graph.
-/

namespace Maquina

/-- One finite attachment position owned by a Machine Body. -/
structure RelationEndpoint where
  body : ResourceId
  slot : Nat
  deriving DecidableEq, Repr

/-- One typed edge between two concrete Machine endpoints. -/
structure RelationLink (Kind : Type) where
  kind : Kind
  left : RelationEndpoint
  right : RelationEndpoint
  deriving Repr

namespace RelationLink

def reversed (link : RelationLink Kind) : RelationLink Kind where
  kind := link.kind
  left := link.right
  right := link.left

end RelationLink

/-- Game-owned compatibility and traversal policy for relation kinds. -/
structure RelationPolicy (Kind : Type) where
  compatible : Kind → RelationEndpoint → RelationEndpoint → Bool
  traversableForward : Kind → Bool
  traversableBackward : Kind → Bool

/--
Resource representation of a relation graph. `linkFamily` identifies attached
edges; `leaseFamily` identifies the unique lock token for each edge. A Process
that depends on a path reserves its leases. A detach Process must consume the
same leases, so ordinary inventory assessment blocks detachment while in use.
-/
structure RelationModel (Kind EndpointKey LinkKey : Type) where
  endpointFamily : ResourceFamily EndpointKey
  describeEndpoint : EndpointKey → RelationEndpoint
  linkFamily : ResourceFamily LinkKey
  leaseFamily : ResourceFamily LinkKey
  describe : LinkKey → RelationLink Kind
  ledger : AccountId
  endpointLinkDisjoint : ResourceFamily.Disjoint endpointFamily linkFamily
  endpointLeaseDisjoint : ResourceFamily.Disjoint endpointFamily leaseFamily
  linkLeaseDisjoint : ResourceFamily.Disjoint linkFamily leaseFamily

namespace RelationModel

def endpointId (model : RelationModel Kind EndpointKey LinkKey) (endpoint : EndpointKey) : ResourceId :=
  model.endpointFamily.encode endpoint

def linkId (model : RelationModel Kind EndpointKey LinkKey) (link : LinkKey) : ResourceId :=
  model.linkFamily.encode link

def leaseId (model : RelationModel Kind EndpointKey LinkKey) (link : LinkKey) : ResourceId :=
  model.leaseFamily.encode link

/-- A Link is active exactly when its unique Link Resource is in the ledger. -/
def LinkActive
    (model : RelationModel Kind EndpointKey LinkKey)
    (world : WorldState resourceCatalog)
    (link : LinkKey) : Prop :=
  (world.balance model.ledger (model.linkId link)).atoms = 1

/-- An endpoint is open exactly when its endpoint token is held by its Machine. -/
def EndpointOpen
    (model : RelationModel Kind EndpointKey LinkKey)
    (world : WorldState resourceCatalog)
    (account : AccountId)
    (endpoint : EndpointKey) : Prop :=
  (world.balance account (model.endpointId endpoint)).atoms = 1

/-- The lock token required to detach one active Link is currently available. -/
def LeaseAvailable
    (model : RelationModel Kind EndpointKey LinkKey)
    (world : WorldState resourceCatalog)
    (link : LinkKey) : Prop :=
  (world.balance model.ledger (model.leaseId link)).atoms = 1

end RelationModel

/-- One proposed traversal of a concrete Link. -/
structure RelationHop (LinkKey : Type) where
  link : LinkKey
  forward : Bool
  deriving Repr

namespace RelationHop

def source (model : RelationModel Kind EndpointKey LinkKey) (hop : RelationHop LinkKey) : RelationEndpoint :=
  if hop.forward then (model.describe hop.link).left else (model.describe hop.link).right

def destination (model : RelationModel Kind EndpointKey LinkKey) (hop : RelationHop LinkKey) : RelationEndpoint :=
  if hop.forward then (model.describe hop.link).right else (model.describe hop.link).left

end RelationHop

/--
A candidate path names its origin and exact Links. Links cannot repeat, which
also makes its lease basket canonical.
-/
structure RelationPath (LinkKey : Type) where
  origin : RelationEndpoint
  hops : List (RelationHop LinkKey)
  linksUnique : (hops.map (fun hop => hop.link)).Nodup
  deriving Repr

namespace RelationPath

def destination (model : RelationModel Kind EndpointKey LinkKey) (path : RelationPath LinkKey) : RelationEndpoint :=
  path.hops.foldl (fun _ hop => hop.destination model) path.origin

private def connectedFrom [DecidableEq RelationEndpoint]
    (model : RelationModel Kind EndpointKey LinkKey)
    (current : RelationEndpoint) : List (RelationHop LinkKey) → Bool
  | [] => true
  | hop :: rest =>
      hop.source model == current && connectedFrom model (hop.destination model) rest

def connected [DecidableEq RelationEndpoint]
    (model : RelationModel Kind EndpointKey LinkKey) (path : RelationPath LinkKey) : Bool :=
  connectedFrom model path.origin path.hops

end RelationPath

inductive RelationPathIssue where
  | disconnected (hopIndex : Nat)
  | incompatible (hopIndex : Nat)
  | traversalForbidden (hopIndex : Nat)
  | linkInactive (hopIndex : Nat) (linkId : ResourceId)
  deriving DecidableEq, Repr

private def relationPathIssuesFrom
    [DecidableEq RelationEndpoint]
    (model : RelationModel Kind EndpointKey LinkKey)
    (policy : RelationPolicy Kind)
    (world : WorldState resourceCatalog) :
    Nat → RelationEndpoint → List (RelationHop LinkKey) → List RelationPathIssue
  | _, _, [] => []
  | index, current, hop :: rest =>
      let connectedIssues :=
        if hop.source model = current then [] else [.disconnected index]
      let compatibilityIssues :=
        if policy.compatible (model.describe hop.link).kind
            (model.describe hop.link).left (model.describe hop.link).right then []
        else [.incompatible index]
      let traversalAllowed :=
        if hop.forward then policy.traversableForward (model.describe hop.link).kind
        else policy.traversableBackward (model.describe hop.link).kind
      let traversalIssues :=
        if traversalAllowed then [] else [.traversalForbidden index]
      let activeIssues :=
        if (world.balance model.ledger (model.linkId hop.link)).atoms = 1 then []
        else [.linkInactive index (model.linkId hop.link)]
      connectedIssues ++ compatibilityIssues ++ traversalIssues ++ activeIssues ++
        relationPathIssuesFrom model policy world (index + 1)
          (hop.destination model) rest

/-- Complete, declaration-ordered validation of a candidate relation path. -/
def relationPathIssues
    [DecidableEq RelationEndpoint]
    (model : RelationModel Kind EndpointKey LinkKey)
    (policy : RelationPolicy Kind)
    (world : WorldState resourceCatalog)
    (path : RelationPath LinkKey) : List RelationPathIssue :=
  relationPathIssuesFrom model policy world 0 path.origin path.hops

/-- Proof-carrying reachability in the exact authoritative world. -/
structure AcceptedRelationPath
    [DecidableEq RelationEndpoint]
    (model : RelationModel Kind EndpointKey LinkKey)
    (policy : RelationPolicy Kind)
    (world : WorldState resourceCatalog)
    (path : RelationPath LinkKey) : Type where
  issuesEmpty : relationPathIssues model policy world path = []

def assessRelationPath
    [DecidableEq RelationEndpoint]
    (model : RelationModel Kind EndpointKey LinkKey)
    (policy : RelationPolicy Kind)
    (world : WorldState resourceCatalog)
    (path : RelationPath LinkKey) :
    Except (List RelationPathIssue) (AcceptedRelationPath model policy world path) :=
  let issues := relationPathIssues model policy world path
  if empty : issues = [] then .ok ⟨empty⟩ else .error issues

theorem assessRelationPath_rejected_exact
    [DecidableEq RelationEndpoint]
    (model : RelationModel Kind EndpointKey LinkKey)
    (policy : RelationPolicy Kind)
    (world : WorldState resourceCatalog)
    (path : RelationPath LinkKey)
    (issues : List RelationPathIssue)
    (rejected : assessRelationPath model policy world path = .error issues) :
    issues = relationPathIssues model policy world path := by
  simp only [assessRelationPath] at rejected
  split at rejected
  · contradiction
  · exact (Except.error.inj rejected).symm

theorem assessRelationPath_rejected_nonempty
    [DecidableEq RelationEndpoint]
    (model : RelationModel Kind EndpointKey LinkKey)
    (policy : RelationPolicy Kind)
    (world : WorldState resourceCatalog)
    (path : RelationPath LinkKey)
    (issues : List RelationPathIssue)
    (rejected : assessRelationPath model policy world path = .error issues) :
    issues ≠ [] := by
  simp only [assessRelationPath] at rejected
  split at rejected
  · contradiction
  · rename_i nonempty
    exact (Except.error.inj rejected) ▸ nonempty

/-- One ordinary Resource reservation that keeps a traversed Link attached. -/
def relationLeaseBasket
    (model : RelationModel Kind EndpointKey LinkKey)
    (link : LinkKey) : Basket :=
  Basket.singleton (model.leaseId link) .one (by decide)

/-- A path dependency is expressed as ordinary reserved Process input. -/
def RelationPathDependency
    (model : RelationModel Kind EndpointKey LinkKey)
    (link : LinkKey)
    (port : ProcessPort Label) : Prop :=
  port.basket = relationLeaseBasket model link

/--
Every Link in a declared path has one ordinary reserved Process port, and no
reserved port is presented as a path dependency without naming a path Link.
-/
def RelationPathDependenciesExact
    (model : RelationModel Kind EndpointKey LinkKey)
    (path : RelationPath LinkKey)
    (ports : List (ProcessPort Label)) : Prop :=
  (∀ hop ∈ path.hops,
      ∃ port ∈ ports, RelationPathDependency model hop.link port) ∧
  (∀ port ∈ ports,
      ∃ hop ∈ path.hops, RelationPathDependency model hop.link port)

end Maquina
