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

@[simp]
theorem balanceAtoms_nil {Account : Type} [DecidableEq Account]
    (account : Account) (objectId : ObjectId) :
    balanceAtoms ([] : List (Holding Account)) account objectId = 0 := rfl

@[simp]
theorem balanceAtoms_cons {Account : Type} [DecidableEq Account]
    (holding : Holding Account)
    (holdings : List (Holding Account))
    (account : Account)
    (objectId : ObjectId) :
    balanceAtoms (holding :: holdings) account objectId =
      if holding.account = account ∧ holding.objectId = objectId then
        holding.quantity.atoms
      else
        balanceAtoms holdings account objectId := rfl

/-- The global quantity of one object across every account. -/
def totalAtomsFor {Account : Type}
    (holdings : List (Holding Account))
    (objectId : ObjectId) : Nat :=
  (holdings.map fun holding =>
    if holding.objectId = objectId then holding.quantity.atoms else 0).sum

@[simp]
theorem totalAtomsFor_nil {Account : Type} (objectId : ObjectId) :
    totalAtomsFor ([] : List (Holding Account)) objectId = 0 := rfl

@[simp]
theorem totalAtomsFor_cons {Account : Type}
    (holding : Holding Account)
    (holdings : List (Holding Account))
    (objectId : ObjectId) :
    totalAtomsFor (holding :: holdings) objectId =
      (if holding.objectId = objectId then holding.quantity.atoms else 0) +
        totalAtomsFor holdings objectId := rfl

/-! ## Canonical balance replacement -/

/-- Remove every holding at one concrete `(account, object)` key. -/
def withoutBalance {Account : Type} [DecidableEq Account]
    (holdings : List (Holding Account))
    (account : Account)
    (objectId : ObjectId) : List (Holding Account) :=
  holdings.filter fun holding =>
    decide (¬(holding.account = account ∧ holding.objectId = objectId))

/--
Replace one balance canonically. A zero replacement is represented by absence;
a positive replacement is the sole holding at that key.
-/
def setBalance {Account : Type} [DecidableEq Account]
    (holdings : List (Holding Account))
    (account : Account)
    (objectId : ObjectId)
    (atoms : Nat) : List (Holding Account) :=
  if zero : atoms = 0 then
    withoutBalance holdings account objectId
  else
    { account
      objectId
      quantity := ⟨atoms⟩
      positive := Nat.pos_of_ne_zero zero } ::
      withoutBalance holdings account objectId

theorem withoutBalance_target_absent {Account : Type} [DecidableEq Account]
    (holdings : List (Holding Account))
    (account : Account)
    (objectId : ObjectId) :
    (account, objectId) ∉
      (withoutBalance holdings account objectId).map Holding.key := by
  intro targetMem
  rw [List.mem_map] at targetMem
  obtain ⟨holding, holdingMem, keyEq⟩ := targetMem
  have kept := (List.mem_filter.mp holdingMem).2
  simp at kept
  have accountEq : holding.account = account := congrArg Prod.fst keyEq
  have objectEq : holding.objectId = objectId := congrArg Prod.snd keyEq
  rcases kept with accountNe | objectNe
  · exact accountNe accountEq
  · exact objectNe objectEq

theorem withoutBalance_keysUnique {Account : Type} [DecidableEq Account]
    (holdings : List (Holding Account))
    (account : Account)
    (objectId : ObjectId)
    (unique : (holdings.map Holding.key).Nodup) :
    ((withoutBalance holdings account objectId).map Holding.key).Nodup := by
  apply List.Sublist.nodup
  · exact List.Sublist.map Holding.key List.filter_sublist
  · exact unique

theorem setBalance_keysUnique {Account : Type} [DecidableEq Account]
    (holdings : List (Holding Account))
    (account : Account)
    (objectId : ObjectId)
    (atoms : Nat)
    (unique : (holdings.map Holding.key).Nodup) :
    ((setBalance holdings account objectId atoms).map Holding.key).Nodup := by
  by_cases zero : atoms = 0
  · simp only [setBalance, dif_pos zero]
    exact withoutBalance_keysUnique holdings account objectId unique
  · simp only [setBalance, dif_neg zero, List.map_cons, List.nodup_cons]
    exact ⟨withoutBalance_target_absent holdings account objectId,
      withoutBalance_keysUnique holdings account objectId unique⟩

theorem balanceAtoms_withoutBalance_same {Account : Type} [DecidableEq Account]
    (holdings : List (Holding Account))
    (account : Account)
    (objectId : ObjectId) :
    balanceAtoms (withoutBalance holdings account objectId) account objectId = 0 := by
  induction holdings with
  | nil => rfl
  | cons holding rest ih =>
      simp only [withoutBalance, List.filter_cons]
      by_cases same : holding.account = account ∧ holding.objectId = objectId
      · have keepTest :
          decide (¬(holding.account = account ∧ holding.objectId = objectId)) =
            false := by
            simp [same]
        rw [keepTest]
        simp only [Bool.false_eq_true, ↓reduceIte]
        change balanceAtoms (withoutBalance rest account objectId) account objectId = 0
        exact ih
      · have keepTest :
          decide (¬(holding.account = account ∧ holding.objectId = objectId)) =
            true := by
            simp [same]
        rw [keepTest]
        simp only [↓reduceIte]
        rw [balanceAtoms_cons, if_neg same]
        change balanceAtoms (withoutBalance rest account objectId) account objectId = 0
        exact ih

theorem balanceAtoms_withoutBalance_other {Account : Type} [DecidableEq Account]
    (holdings : List (Holding Account))
    (removedAccount queriedAccount : Account)
    (removedObject queriedObject : ObjectId)
    (different : removedAccount ≠ queriedAccount ∨ removedObject ≠ queriedObject) :
    balanceAtoms (withoutBalance holdings removedAccount removedObject)
        queriedAccount queriedObject =
      balanceAtoms holdings queriedAccount queriedObject := by
  induction holdings with
  | nil => rfl
  | cons holding rest ih =>
      simp only [withoutBalance, List.filter_cons]
      by_cases removed :
          holding.account = removedAccount ∧ holding.objectId = removedObject
      · have keepTest :
          decide (¬(holding.account = removedAccount ∧
            holding.objectId = removedObject)) = false := by
            simp [removed]
        rw [keepTest]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [balanceAtoms_cons]
        have notQueried :
            ¬(holding.account = queriedAccount ∧
              holding.objectId = queriedObject) := by
          intro queried
          rcases different with accountDifferent | objectDifferent
          · exact accountDifferent (removed.1.symm.trans queried.1)
          · exact objectDifferent (removed.2.symm.trans queried.2)
        rw [if_neg notQueried]
        change balanceAtoms (withoutBalance rest removedAccount removedObject)
            queriedAccount queriedObject =
          balanceAtoms rest queriedAccount queriedObject
        exact ih
      · have keepTest :
          decide (¬(holding.account = removedAccount ∧
            holding.objectId = removedObject)) = true := by
            simp [removed]
        rw [keepTest]
        simp only [↓reduceIte]
        rw [balanceAtoms_cons, balanceAtoms_cons]
        by_cases queried :
            holding.account = queriedAccount ∧ holding.objectId = queriedObject
        · simp [queried]
        · rw [if_neg queried, if_neg queried]
          change balanceAtoms (withoutBalance rest removedAccount removedObject)
              queriedAccount queriedObject =
            balanceAtoms rest queriedAccount queriedObject
          exact ih

theorem balanceAtoms_setBalance_same {Account : Type} [DecidableEq Account]
    (holdings : List (Holding Account))
    (account : Account)
    (objectId : ObjectId)
    (atoms : Nat) :
    balanceAtoms (setBalance holdings account objectId atoms) account objectId = atoms := by
  by_cases zero : atoms = 0
  · simp [setBalance, zero, balanceAtoms_withoutBalance_same]
  · rw [setBalance]
    simp only [dif_neg zero]
    rw [balanceAtoms_cons]
    simp

theorem balanceAtoms_setBalance_other {Account : Type} [DecidableEq Account]
    (holdings : List (Holding Account))
    (setAccount queriedAccount : Account)
    (setObject queriedObject : ObjectId)
    (atoms : Nat)
    (different : setAccount ≠ queriedAccount ∨ setObject ≠ queriedObject) :
    balanceAtoms (setBalance holdings setAccount setObject atoms)
        queriedAccount queriedObject =
      balanceAtoms holdings queriedAccount queriedObject := by
  by_cases zero : atoms = 0
  · simp only [setBalance, dif_pos zero]
    exact balanceAtoms_withoutBalance_other holdings
      setAccount queriedAccount setObject queriedObject different
  · simp only [setBalance, dif_neg zero]
    rw [balanceAtoms_cons]
    have notQueried :
        ¬(setAccount = queriedAccount ∧ setObject = queriedObject) := by
      intro same
      rcases different with accountDifferent | objectDifferent
      · exact accountDifferent same.1
      · exact objectDifferent same.2
    rw [if_neg notQueried]
    exact balanceAtoms_withoutBalance_other holdings
      setAccount queriedAccount setObject queriedObject different

theorem balanceAtoms_le_totalAtomsFor {Account : Type} [DecidableEq Account]
    (holdings : List (Holding Account))
    (account : Account)
    (objectId : ObjectId) :
    balanceAtoms holdings account objectId ≤ totalAtomsFor holdings objectId := by
  induction holdings with
  | nil => exact Nat.le_refl 0
  | cons holding rest ih =>
      rw [balanceAtoms_cons, totalAtomsFor_cons]
      by_cases same : holding.account = account ∧ holding.objectId = objectId
      · rw [if_pos same, if_pos same.2]
        exact Nat.le_add_right _ _
      · rw [if_neg same]
        by_cases sameObject : holding.objectId = objectId
        · rw [if_pos sameObject]
          exact Nat.le_trans ih (Nat.le_add_left _ _)
        · rw [if_neg sameObject, Nat.zero_add]
          exact ih

theorem balanceAtoms_eq_zero_of_key_absent {Account : Type} [DecidableEq Account]
    (holdings : List (Holding Account))
    (account : Account)
    (objectId : ObjectId)
    (absent : (account, objectId) ∉ holdings.map Holding.key) :
    balanceAtoms holdings account objectId = 0 := by
  induction holdings with
  | nil => rfl
  | cons holding rest ih =>
      rw [balanceAtoms_cons]
      simp only [List.map_cons, List.mem_cons, not_or] at absent
      by_cases same : holding.account = account ∧ holding.objectId = objectId
      · exact False.elim (absent.1 (Prod.ext same.1.symm same.2.symm))
      · rw [if_neg same]
        exact ih absent.2

theorem totalAtomsFor_withoutBalance_other {Account : Type} [DecidableEq Account]
    (holdings : List (Holding Account))
    (account : Account)
    (removedObject queriedObject : ObjectId)
    (different : removedObject ≠ queriedObject) :
    totalAtomsFor (withoutBalance holdings account removedObject) queriedObject =
      totalAtomsFor holdings queriedObject := by
  induction holdings with
  | nil => rfl
  | cons holding rest ih =>
      simp only [withoutBalance, List.filter_cons]
      by_cases removed :
          holding.account = account ∧ holding.objectId = removedObject
      · have keepTest :
          decide (¬(holding.account = account ∧
            holding.objectId = removedObject)) = false := by
            simp [removed]
        rw [keepTest]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [totalAtomsFor_cons]
        have holdingDifferent : holding.objectId ≠ queriedObject := by
          intro equal
          exact different (removed.2.symm.trans equal)
        rw [if_neg holdingDifferent, Nat.zero_add]
        change totalAtomsFor (withoutBalance rest account removedObject) queriedObject =
          totalAtomsFor rest queriedObject
        exact ih
      · have keepTest :
          decide (¬(holding.account = account ∧
            holding.objectId = removedObject)) = true := by
            simp [removed]
        rw [keepTest]
        simp only [↓reduceIte]
        rw [totalAtomsFor_cons, totalAtomsFor_cons]
        change
          (if holding.objectId = queriedObject then holding.quantity.atoms else 0) +
              totalAtomsFor (withoutBalance rest account removedObject) queriedObject =
            (if holding.objectId = queriedObject then holding.quantity.atoms else 0) +
              totalAtomsFor rest queriedObject
        rw [ih]

theorem totalAtomsFor_withoutBalance_same {Account : Type} [DecidableEq Account]
    (holdings : List (Holding Account))
    (account : Account)
    (objectId : ObjectId)
    (unique : (holdings.map Holding.key).Nodup) :
    totalAtomsFor (withoutBalance holdings account objectId) objectId =
      totalAtomsFor holdings objectId - balanceAtoms holdings account objectId := by
  induction holdings with
  | nil => rfl
  | cons holding rest ih =>
      simp only [List.map_cons, List.nodup_cons] at unique
      simp only [withoutBalance, List.filter_cons]
      by_cases removed : holding.account = account ∧ holding.objectId = objectId
      · have keepTest :
          decide (¬(holding.account = account ∧ holding.objectId = objectId)) =
            false := by
            simp [removed]
        rw [keepTest]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [totalAtomsFor_cons, if_pos removed.2]
        rw [balanceAtoms_cons, if_pos removed]
        have targetAbsent :
            (account, objectId) ∉ rest.map Holding.key := by
          intro targetMem
          apply unique.1
          rw [List.mem_map] at targetMem ⊢
          obtain ⟨targetHolding, targetHoldingMem, targetKey⟩ := targetMem
          exact ⟨targetHolding, targetHoldingMem,
            targetKey.trans (Prod.ext removed.1.symm removed.2.symm)⟩
        have restBalanceZero :=
          balanceAtoms_eq_zero_of_key_absent rest account objectId targetAbsent
        rw [Nat.add_sub_cancel_left]
        change totalAtomsFor (withoutBalance rest account objectId) objectId =
          totalAtomsFor rest objectId
        rw [ih unique.2, restBalanceZero, Nat.sub_zero]
      · have keepTest :
          decide (¬(holding.account = account ∧ holding.objectId = objectId)) =
            true := by
            simp [removed]
        rw [keepTest]
        simp only [↓reduceIte]
        rw [totalAtomsFor_cons, totalAtomsFor_cons]
        rw [balanceAtoms_cons, if_neg removed]
        change
          (if holding.objectId = objectId then holding.quantity.atoms else 0) +
              totalAtomsFor (withoutBalance rest account objectId) objectId =
            (if holding.objectId = objectId then holding.quantity.atoms else 0) +
              totalAtomsFor rest objectId - balanceAtoms rest account objectId
        rw [ih unique.2]
        by_cases sameObject : holding.objectId = objectId
        · rw [if_pos sameObject]
          rw [Nat.add_sub_assoc (balanceAtoms_le_totalAtomsFor rest account objectId)]
        · simp [sameObject]

theorem totalAtomsFor_setBalance_same {Account : Type} [DecidableEq Account]
    (holdings : List (Holding Account))
    (account : Account)
    (objectId : ObjectId)
    (atoms : Nat)
    (unique : (holdings.map Holding.key).Nodup) :
    totalAtomsFor (setBalance holdings account objectId atoms) objectId =
      totalAtomsFor holdings objectId -
        balanceAtoms holdings account objectId + atoms := by
  by_cases zero : atoms = 0
  · simp only [setBalance, dif_pos zero]
    rw [totalAtomsFor_withoutBalance_same holdings account objectId unique,
      zero, Nat.add_zero]
  · simp only [setBalance, dif_neg zero]
    rw [totalAtomsFor_cons]
    simp only [↓reduceIte]
    rw [totalAtomsFor_withoutBalance_same holdings account objectId unique]
    exact Nat.add_comm _ _

theorem totalAtomsFor_setBalance_other {Account : Type} [DecidableEq Account]
    (holdings : List (Holding Account))
    (account : Account)
    (setObject queriedObject : ObjectId)
    (atoms : Nat)
    (different : setObject ≠ queriedObject) :
    totalAtomsFor (setBalance holdings account setObject atoms) queriedObject =
      totalAtomsFor holdings queriedObject := by
  by_cases zero : atoms = 0
  · simp only [setBalance, dif_pos zero]
    exact totalAtomsFor_withoutBalance_other holdings
      account setObject queriedObject different
  · simp only [setBalance, dif_neg zero]
    rw [totalAtomsFor_cons, if_neg different, Nat.zero_add]
    exact totalAtomsFor_withoutBalance_other holdings
      account setObject queriedObject different

/-- Every held object resolves to an authoritative catalog specification. -/
def ObjectsKnown {Account : Type}
    (catalog : Catalog)
    (holdings : List (Holding Account)) : Prop :=
  ∀ holding, holding ∈ holdings →
    ∃ spec, catalog.lookup holding.objectId = some spec

theorem ObjectsKnown.withoutBalance {Account : Type} [DecidableEq Account]
    {catalog : Catalog}
    {holdings : List (Holding Account)}
    (known : ObjectsKnown catalog holdings)
    (account : Account)
    (objectId : ObjectId) :
    ObjectsKnown catalog (withoutBalance holdings account objectId) := by
  intro holding holdingMem
  apply known holding
  exact (List.mem_filter.mp holdingMem).1

theorem ObjectsKnown.setBalance {Account : Type} [DecidableEq Account]
    {catalog : Catalog}
    {holdings : List (Holding Account)}
    (known : ObjectsKnown catalog holdings)
    (account : Account)
    (objectId : ObjectId)
    (atoms : Nat)
    (setObjectKnown : ∃ spec, catalog.lookup objectId = some spec) :
  ObjectsKnown catalog (setBalance holdings account objectId atoms) := by
  by_cases zero : atoms = 0
  · simp only [Maquina.setBalance, dif_pos zero]
    exact known.withoutBalance account objectId
  · simp only [Maquina.setBalance, dif_neg zero]
    intro holding holdingMem
    rw [List.mem_cons] at holdingMem
    rcases holdingMem with isNew | isOld
    · subst holding
      exact setObjectKnown
    · exact known.withoutBalance account objectId holding isOld

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
