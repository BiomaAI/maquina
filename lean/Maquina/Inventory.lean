import Maquina.Object

/-!
# Maquina Inventories

Canonical baskets, holdings, world state, and derived supply views.
-/

namespace Maquina

/-! ## Canonical baskets -/

/-- One positive, object-qualified entry in a basket. -/
structure BasketEntry where
  objectId : ObjectId
  quantity : Quantity
  positive : 0 < quantity.atoms
  deriving Repr

/-- A finite basket with at most one entry for each object identity. -/
structure Basket where
  entries : List BasketEntry
  objectsUnique : (entries.map BasketEntry.objectId).Nodup
  deriving Repr

namespace Basket

def empty : Basket where
  entries := []
  objectsUnique := by simp

def singleton
    (objectId : ObjectId)
    (quantity : Quantity)
    (positive : 0 < quantity.atoms) : Basket where
  entries := [{ objectId, quantity, positive }]
  objectsUnique := by simp

private def lookupAtomsIn (objectId : ObjectId) : List BasketEntry → Nat
  | [] => 0
  | entry :: rest =>
      if entry.objectId = objectId then entry.quantity.atoms
      else lookupAtomsIn objectId rest

/-- Missing basket entries have quantity zero. -/
def lookupAtoms (basket : Basket) (objectId : ObjectId) : Nat :=
  lookupAtomsIn objectId basket.entries

@[simp]
theorem lookupAtoms_empty (objectId : ObjectId) :
    empty.lookupAtoms objectId = 0 := rfl

@[simp]
theorem lookupAtoms_singleton_same
    (objectId : ObjectId)
    (quantity : Quantity)
    (positive : 0 < quantity.atoms) :
    (singleton objectId quantity positive).lookupAtoms objectId = quantity.atoms := by
  simp [lookupAtoms, singleton, lookupAtomsIn]

end Basket

/-! ## Canonical world holdings -/

/-- One positive balance at a concrete `(account, object)` key. -/
structure Holding (Account : Type) where
  account : Account
  objectId : ObjectId
  quantity : Quantity
  positive : 0 < quantity.atoms
  deriving Repr

def Holding.key {Account : Type} (holding : Holding Account) : Account × ObjectId :=
  (holding.account, holding.objectId)

private def balanceAtomsIn {Account : Type} [DecidableEq Account]
    (account : Account)
    (objectId : ObjectId) : List (Holding Account) → Nat
  | [] => 0
  | holding :: rest =>
      if holding.account = account ∧ holding.objectId = objectId then
        holding.quantity.atoms
      else
        balanceAtomsIn account objectId rest

/-- Missing holdings have quantity zero. -/
def balanceAtoms {Account : Type} [DecidableEq Account]
    (holdings : List (Holding Account))
    (account : Account)
    (objectId : ObjectId) : Nat :=
  balanceAtomsIn account objectId holdings

/-- The global quantity of one object across every account. -/
def totalAtomsFor {Account : Type}
    (holdings : List (Holding Account))
    (objectId : ObjectId) : Nat :=
  (holdings.map fun holding =>
    if holding.objectId = objectId then holding.quantity.atoms else 0).sum

/-- Every held object resolves to an authoritative catalog specification. -/
def ObjectsKnown {Account : Type}
    (catalog : Catalog)
    (holdings : List (Holding Account)) : Prop :=
  ∀ holding, holding ∈ holdings →
    ∃ spec, catalog.lookup holding.objectId = some spec

/-- Every bounded catalog object respects its global maximum in the holdings. -/
def RespectsCatalogLimits {Account : Type}
    (catalog : Catalog)
    (holdings : List (Holding Account)) : Prop :=
  ∀ {objectId spec maximum positive},
    catalog.lookup objectId = some spec →
    spec.limit = .bounded maximum positive →
    totalAtomsFor holdings objectId ≤ maximum.atoms

/--
The one authoritative finite sparse holding state. Inventories and global
supplies are projections of this value rather than separate mutable stores.
-/
structure WorldState (Account : Type) (catalog : Catalog) where
  holdings : List (Holding Account)
  keysUnique : (holdings.map Holding.key).Nodup
  objectsKnown : ObjectsKnown catalog holdings
  respectsLimits : RespectsCatalogLimits catalog holdings
  deriving Repr

namespace WorldState

def empty (Account : Type) (catalog : Catalog) : WorldState Account catalog where
  holdings := []
  keysUnique := by simp
  objectsKnown := by simp [ObjectsKnown]
  respectsLimits := by simp [RespectsCatalogLimits, totalAtomsFor]

def balance {Account : Type} [DecidableEq Account] {catalog : Catalog}
    (state : WorldState Account catalog)
    (account : Account)
    (objectId : ObjectId) : Quantity :=
  ⟨balanceAtoms state.holdings account objectId⟩

def total {Account : Type} {catalog : Catalog}
    (state : WorldState Account catalog)
    (objectId : ObjectId) : Quantity :=
  ⟨totalAtomsFor state.holdings objectId⟩

/-- A world's derived total is a legal supply for the catalog object. -/
def supply {Account : Type} {catalog : Catalog}
    (state : WorldState Account catalog)
    {objectId : ObjectId}
    {spec : ObjectSpec}
    (found : catalog.lookup objectId = some spec) : Supply spec := by
  unfold Supply
  cases limitEq : spec.limit with
  | unbounded =>
      exact state.total objectId
  | bounded maximum positive =>
      refine ⟨state.total objectId, ?_⟩
      exact state.respectsLimits found limitEq

/-- Every bounded object total satisfies its declared global maximum. -/
theorem bounded_total_le {Account : Type} {catalog : Catalog}
    (state : WorldState Account catalog)
    {objectId : ObjectId}
    {spec : ObjectSpec}
    (maximum : Quantity)
    (positive : 0 < maximum.atoms)
    (found : catalog.lookup objectId = some spec)
    (limitEq : spec.limit = .bounded maximum positive) :
    (state.total objectId).atoms ≤ maximum.atoms :=
  state.respectsLimits found limitEq

/-- A declared unique object has at most one atom globally. -/
theorem unique_total_le_one {Account : Type} {catalog : Catalog}
    (state : WorldState Account catalog)
    (header : ObjectHeader)
    (found : catalog.lookup header.id = some (ObjectSpec.unique header)) :
    (state.total header.id).atoms ≤ 1 :=
  state.respectsLimits found rfl

/-- A declared edition cannot exceed its positive copy limit. -/
theorem edition_total_le_max {Account : Type} {catalog : Catalog}
    (state : WorldState Account catalog)
    (header : ObjectHeader)
    (maxCopies : Nat)
    (positive : 0 < maxCopies)
    (found : catalog.lookup header.id =
      some (ObjectSpec.edition header maxCopies positive)) :
    (state.total header.id).atoms ≤ maxCopies :=
  state.respectsLimits found rfl

end WorldState

end Maquina
