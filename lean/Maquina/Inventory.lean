import Maquina.Account
import Maquina.Resource

/-!
# Maquina Inventories

Canonical baskets, holdings, world state, and derived supply views.
-/

namespace Maquina

/-! ## Canonical baskets -/

/-- One positive, resource-qualified entry in a basket. -/
structure BasketEntry where
  resourceId : ResourceId
  quantity : Quantity
  positive : 0 < quantity.atoms
  deriving Repr

/-- A finite basket with at most one entry for each resource identity. -/
structure Basket where
  entries : List BasketEntry
  resourcesUnique : (entries.map BasketEntry.resourceId).Nodup
  deriving Repr

namespace Basket

def empty : Basket where
  entries := []
  resourcesUnique := by simp

def singleton
    (resourceId : ResourceId)
    (quantity : Quantity)
    (positive : 0 < quantity.atoms) : Basket where
  entries := [{ resourceId, quantity, positive }]
  resourcesUnique := by simp

private def lookupAtomsIn (resourceId : ResourceId) : List BasketEntry → Nat
  | [] => 0
  | entry :: rest =>
      if entry.resourceId = resourceId then entry.quantity.atoms
      else lookupAtomsIn resourceId rest

private theorem lookupAtomsIn_eq_of_mem
    (entries : List BasketEntry)
    (unique : (entries.map BasketEntry.resourceId).Nodup)
    (entry : BasketEntry)
    (entryMem : entry ∈ entries) :
    lookupAtomsIn entry.resourceId entries = entry.quantity.atoms := by
  induction entries with
  | nil => simp at entryMem
  | cons head rest ih =>
      have uniqueParts := List.nodup_cons.mp unique
      rcases List.mem_cons.mp entryMem with isHead | inRest
      · subst head
        simp [lookupAtomsIn]
      · have different : head.resourceId ≠ entry.resourceId := by
          intro same
          apply uniqueParts.1
          rw [List.mem_map]
          exact ⟨entry, inRest, same.symm⟩
        simp only [lookupAtomsIn, different, ↓reduceIte]
        exact ih uniqueParts.2 inRest

private theorem lookupAtomsIn_eq_zero_of_not_mem
    (entries : List BasketEntry)
    (resourceId : ResourceId)
    (absent : resourceId ∉ entries.map BasketEntry.resourceId) :
    lookupAtomsIn resourceId entries = 0 := by
  induction entries with
  | nil => rfl
  | cons head rest ih =>
      simp only [List.map_cons, List.mem_cons, not_or] at absent
      simp only [lookupAtomsIn]
      have different : head.resourceId ≠ resourceId := by
        intro same
        exact absent.1 same.symm
      rw [if_neg different]
      exact ih absent.2

/-- Missing basket entries have quantity zero. -/
def lookupAtoms (basket : Basket) (resourceId : ResourceId) : Nat :=
  lookupAtomsIn resourceId basket.entries

/-- Looking up a canonical basket entry returns its exact quantity. -/
theorem lookupAtoms_eq_of_mem
    (basket : Basket)
    (entry : BasketEntry)
    (entryMem : entry ∈ basket.entries) :
    basket.lookupAtoms entry.resourceId = entry.quantity.atoms := by
  exact lookupAtomsIn_eq_of_mem basket.entries basket.resourcesUnique entry entryMem

/-- A resource absent from a canonical basket has quantity zero. -/
theorem lookupAtoms_eq_zero_of_not_mem
    (basket : Basket)
    (resourceId : ResourceId)
    (absent : resourceId ∉ basket.entries.map BasketEntry.resourceId) :
    basket.lookupAtoms resourceId = 0 := by
  exact lookupAtomsIn_eq_zero_of_not_mem basket.entries resourceId absent

@[simp]
theorem lookupAtoms_empty (resourceId : ResourceId) :
    empty.lookupAtoms resourceId = 0 := rfl

@[simp]
theorem lookupAtoms_singleton_same
    (resourceId : ResourceId)
    (quantity : Quantity)
    (positive : 0 < quantity.atoms) :
    (singleton resourceId quantity positive).lookupAtoms resourceId = quantity.atoms := by
  simp [lookupAtoms, singleton, lookupAtomsIn]

end Basket

/-! ## Canonical world holdings -/

/-- One positive balance at a concrete `(account, resource)` key. -/
structure Holding (Account : Type) where
  account : Account
  resourceId : ResourceId
  quantity : Quantity
  positive : 0 < quantity.atoms
  deriving Repr

def Holding.key {Account : Type} (holding : Holding Account) : Account × ResourceId :=
  (holding.account, holding.resourceId)

private def balanceAtomsIn {Account : Type} [DecidableEq Account]
    (account : Account)
    (resourceId : ResourceId) : List (Holding Account) → Nat
  | [] => 0
  | holding :: rest =>
      if holding.account = account ∧ holding.resourceId = resourceId then
        holding.quantity.atoms
      else
        balanceAtomsIn account resourceId rest

/-- Missing holdings have quantity zero. -/
def balanceAtoms {Account : Type} [DecidableEq Account]
    (holdings : List (Holding Account))
    (account : Account)
    (resourceId : ResourceId) : Nat :=
  balanceAtomsIn account resourceId holdings

@[simp]
theorem balanceAtoms_nil {Account : Type} [DecidableEq Account]
    (account : Account) (resourceId : ResourceId) :
    balanceAtoms ([] : List (Holding Account)) account resourceId = 0 := rfl

@[simp]
theorem balanceAtoms_cons {Account : Type} [DecidableEq Account]
    (holding : Holding Account)
    (holdings : List (Holding Account))
    (account : Account)
    (resourceId : ResourceId) :
    balanceAtoms (holding :: holdings) account resourceId =
      if holding.account = account ∧ holding.resourceId = resourceId then
        holding.quantity.atoms
      else
        balanceAtoms holdings account resourceId := rfl

/-- The global quantity of one resource across every account. -/
def totalAtomsFor {Account : Type}
    (holdings : List (Holding Account))
    (resourceId : ResourceId) : Nat :=
  (holdings.map fun holding =>
    if holding.resourceId = resourceId then holding.quantity.atoms else 0).sum

@[simp]
theorem totalAtomsFor_nil {Account : Type} (resourceId : ResourceId) :
    totalAtomsFor ([] : List (Holding Account)) resourceId = 0 := rfl

@[simp]
theorem totalAtomsFor_cons {Account : Type}
    (holding : Holding Account)
    (holdings : List (Holding Account))
    (resourceId : ResourceId) :
    totalAtomsFor (holding :: holdings) resourceId =
      (if holding.resourceId = resourceId then holding.quantity.atoms else 0) +
        totalAtomsFor holdings resourceId := rfl

/-! ## Canonical balance replacement -/

/-- Remove every holding at one concrete `(account, resource)` key. -/
def withoutBalance {Account : Type} [DecidableEq Account]
    (holdings : List (Holding Account))
    (account : Account)
    (resourceId : ResourceId) : List (Holding Account) :=
  holdings.filter fun holding =>
    decide (¬(holding.account = account ∧ holding.resourceId = resourceId))

/--
Replace one balance canonically. A zero replacement is represented by absence;
a positive replacement is the sole holding at that key.
-/
def setBalance {Account : Type} [DecidableEq Account]
    (holdings : List (Holding Account))
    (account : Account)
    (resourceId : ResourceId)
    (atoms : Nat) : List (Holding Account) :=
  if zero : atoms = 0 then
    withoutBalance holdings account resourceId
  else
    { account
      resourceId
      quantity := ⟨atoms⟩
      positive := Nat.pos_of_ne_zero zero } ::
      withoutBalance holdings account resourceId

theorem withoutBalance_target_absent {Account : Type} [DecidableEq Account]
    (holdings : List (Holding Account))
    (account : Account)
    (resourceId : ResourceId) :
    (account, resourceId) ∉
      (withoutBalance holdings account resourceId).map Holding.key := by
  intro targetMem
  rw [List.mem_map] at targetMem
  obtain ⟨holding, holdingMem, keyEq⟩ := targetMem
  have kept := (List.mem_filter.mp holdingMem).2
  simp at kept
  have accountEq : holding.account = account := congrArg Prod.fst keyEq
  have resourceEq : holding.resourceId = resourceId := congrArg Prod.snd keyEq
  rcases kept with accountNe | resourceNe
  · exact accountNe accountEq
  · exact resourceNe resourceEq

theorem withoutBalance_keysUnique {Account : Type} [DecidableEq Account]
    (holdings : List (Holding Account))
    (account : Account)
    (resourceId : ResourceId)
    (unique : (holdings.map Holding.key).Nodup) :
    ((withoutBalance holdings account resourceId).map Holding.key).Nodup := by
  apply List.Sublist.nodup
  · exact List.Sublist.map Holding.key List.filter_sublist
  · exact unique

theorem setBalance_keysUnique {Account : Type} [DecidableEq Account]
    (holdings : List (Holding Account))
    (account : Account)
    (resourceId : ResourceId)
    (atoms : Nat)
    (unique : (holdings.map Holding.key).Nodup) :
    ((setBalance holdings account resourceId atoms).map Holding.key).Nodup := by
  by_cases zero : atoms = 0
  · simp only [setBalance, dif_pos zero]
    exact withoutBalance_keysUnique holdings account resourceId unique
  · simp only [setBalance, dif_neg zero, List.map_cons, List.nodup_cons]
    exact ⟨withoutBalance_target_absent holdings account resourceId,
      withoutBalance_keysUnique holdings account resourceId unique⟩

theorem balanceAtoms_withoutBalance_same {Account : Type} [DecidableEq Account]
    (holdings : List (Holding Account))
    (account : Account)
    (resourceId : ResourceId) :
    balanceAtoms (withoutBalance holdings account resourceId) account resourceId = 0 := by
  induction holdings with
  | nil => rfl
  | cons holding rest ih =>
      simp only [withoutBalance, List.filter_cons]
      by_cases same : holding.account = account ∧ holding.resourceId = resourceId
      · have keepTest :
          decide (¬(holding.account = account ∧ holding.resourceId = resourceId)) =
            false := by
            simp [same]
        rw [keepTest]
        simp only [Bool.false_eq_true, ↓reduceIte]
        change balanceAtoms (withoutBalance rest account resourceId) account resourceId = 0
        exact ih
      · have keepTest :
          decide (¬(holding.account = account ∧ holding.resourceId = resourceId)) =
            true := by
            simp [same]
        rw [keepTest]
        simp only [↓reduceIte]
        rw [balanceAtoms_cons, if_neg same]
        change balanceAtoms (withoutBalance rest account resourceId) account resourceId = 0
        exact ih

theorem balanceAtoms_withoutBalance_other {Account : Type} [DecidableEq Account]
    (holdings : List (Holding Account))
    (removedAccount queriedAccount : Account)
    (removedResource queriedResource : ResourceId)
    (different : removedAccount ≠ queriedAccount ∨ removedResource ≠ queriedResource) :
    balanceAtoms (withoutBalance holdings removedAccount removedResource)
        queriedAccount queriedResource =
      balanceAtoms holdings queriedAccount queriedResource := by
  induction holdings with
  | nil => rfl
  | cons holding rest ih =>
      simp only [withoutBalance, List.filter_cons]
      by_cases removed :
          holding.account = removedAccount ∧ holding.resourceId = removedResource
      · have keepTest :
          decide (¬(holding.account = removedAccount ∧
            holding.resourceId = removedResource)) = false := by
            simp [removed]
        rw [keepTest]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [balanceAtoms_cons]
        have notQueried :
            ¬(holding.account = queriedAccount ∧
              holding.resourceId = queriedResource) := by
          intro queried
          rcases different with accountDifferent | resourceDifferent
          · exact accountDifferent (removed.1.symm.trans queried.1)
          · exact resourceDifferent (removed.2.symm.trans queried.2)
        rw [if_neg notQueried]
        change balanceAtoms (withoutBalance rest removedAccount removedResource)
            queriedAccount queriedResource =
          balanceAtoms rest queriedAccount queriedResource
        exact ih
      · have keepTest :
          decide (¬(holding.account = removedAccount ∧
            holding.resourceId = removedResource)) = true := by
            simp [removed]
        rw [keepTest]
        simp only [↓reduceIte]
        rw [balanceAtoms_cons, balanceAtoms_cons]
        by_cases queried :
            holding.account = queriedAccount ∧ holding.resourceId = queriedResource
        · simp [queried]
        · rw [if_neg queried, if_neg queried]
          change balanceAtoms (withoutBalance rest removedAccount removedResource)
              queriedAccount queriedResource =
            balanceAtoms rest queriedAccount queriedResource
          exact ih

theorem balanceAtoms_setBalance_same {Account : Type} [DecidableEq Account]
    (holdings : List (Holding Account))
    (account : Account)
    (resourceId : ResourceId)
    (atoms : Nat) :
    balanceAtoms (setBalance holdings account resourceId atoms) account resourceId = atoms := by
  by_cases zero : atoms = 0
  · simp [setBalance, zero, balanceAtoms_withoutBalance_same]
  · rw [setBalance]
    simp only [dif_neg zero]
    rw [balanceAtoms_cons]
    simp

theorem balanceAtoms_setBalance_other {Account : Type} [DecidableEq Account]
    (holdings : List (Holding Account))
    (setAccount queriedAccount : Account)
    (setResource queriedResource : ResourceId)
    (atoms : Nat)
    (different : setAccount ≠ queriedAccount ∨ setResource ≠ queriedResource) :
    balanceAtoms (setBalance holdings setAccount setResource atoms)
        queriedAccount queriedResource =
      balanceAtoms holdings queriedAccount queriedResource := by
  by_cases zero : atoms = 0
  · simp only [setBalance, dif_pos zero]
    exact balanceAtoms_withoutBalance_other holdings
      setAccount queriedAccount setResource queriedResource different
  · simp only [setBalance, dif_neg zero]
    rw [balanceAtoms_cons]
    have notQueried :
        ¬(setAccount = queriedAccount ∧ setResource = queriedResource) := by
      intro same
      rcases different with accountDifferent | resourceDifferent
      · exact accountDifferent same.1
      · exact resourceDifferent same.2
    rw [if_neg notQueried]
    exact balanceAtoms_withoutBalance_other holdings
      setAccount queriedAccount setResource queriedResource different

theorem balanceAtoms_le_totalAtomsFor {Account : Type} [DecidableEq Account]
    (holdings : List (Holding Account))
    (account : Account)
    (resourceId : ResourceId) :
    balanceAtoms holdings account resourceId ≤ totalAtomsFor holdings resourceId := by
  induction holdings with
  | nil => exact Nat.le_refl 0
  | cons holding rest ih =>
      rw [balanceAtoms_cons, totalAtomsFor_cons]
      by_cases same : holding.account = account ∧ holding.resourceId = resourceId
      · rw [if_pos same, if_pos same.2]
        exact Nat.le_add_right _ _
      · rw [if_neg same]
        by_cases sameResource : holding.resourceId = resourceId
        · rw [if_pos sameResource]
          exact Nat.le_trans ih (Nat.le_add_left _ _)
        · rw [if_neg sameResource, Nat.zero_add]
          exact ih

theorem balanceAtoms_eq_zero_of_key_absent {Account : Type} [DecidableEq Account]
    (holdings : List (Holding Account))
    (account : Account)
    (resourceId : ResourceId)
    (absent : (account, resourceId) ∉ holdings.map Holding.key) :
    balanceAtoms holdings account resourceId = 0 := by
  induction holdings with
  | nil => rfl
  | cons holding rest ih =>
      rw [balanceAtoms_cons]
      simp only [List.map_cons, List.mem_cons, not_or] at absent
      by_cases same : holding.account = account ∧ holding.resourceId = resourceId
      · exact False.elim (absent.1 (Prod.ext same.1.symm same.2.symm))
      · rw [if_neg same]
        exact ih absent.2

theorem totalAtomsFor_withoutBalance_other {Account : Type} [DecidableEq Account]
    (holdings : List (Holding Account))
    (account : Account)
    (removedResource queriedResource : ResourceId)
    (different : removedResource ≠ queriedResource) :
    totalAtomsFor (withoutBalance holdings account removedResource) queriedResource =
      totalAtomsFor holdings queriedResource := by
  induction holdings with
  | nil => rfl
  | cons holding rest ih =>
      simp only [withoutBalance, List.filter_cons]
      by_cases removed :
          holding.account = account ∧ holding.resourceId = removedResource
      · have keepTest :
          decide (¬(holding.account = account ∧
            holding.resourceId = removedResource)) = false := by
            simp [removed]
        rw [keepTest]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [totalAtomsFor_cons]
        have holdingDifferent : holding.resourceId ≠ queriedResource := by
          intro equal
          exact different (removed.2.symm.trans equal)
        rw [if_neg holdingDifferent, Nat.zero_add]
        change totalAtomsFor (withoutBalance rest account removedResource) queriedResource =
          totalAtomsFor rest queriedResource
        exact ih
      · have keepTest :
          decide (¬(holding.account = account ∧
            holding.resourceId = removedResource)) = true := by
            simp [removed]
        rw [keepTest]
        simp only [↓reduceIte]
        rw [totalAtomsFor_cons, totalAtomsFor_cons]
        change
          (if holding.resourceId = queriedResource then holding.quantity.atoms else 0) +
              totalAtomsFor (withoutBalance rest account removedResource) queriedResource =
            (if holding.resourceId = queriedResource then holding.quantity.atoms else 0) +
              totalAtomsFor rest queriedResource
        rw [ih]

theorem totalAtomsFor_withoutBalance_same {Account : Type} [DecidableEq Account]
    (holdings : List (Holding Account))
    (account : Account)
    (resourceId : ResourceId)
    (unique : (holdings.map Holding.key).Nodup) :
    totalAtomsFor (withoutBalance holdings account resourceId) resourceId =
      totalAtomsFor holdings resourceId - balanceAtoms holdings account resourceId := by
  induction holdings with
  | nil => rfl
  | cons holding rest ih =>
      simp only [List.map_cons, List.nodup_cons] at unique
      simp only [withoutBalance, List.filter_cons]
      by_cases removed : holding.account = account ∧ holding.resourceId = resourceId
      · have keepTest :
          decide (¬(holding.account = account ∧ holding.resourceId = resourceId)) =
            false := by
            simp [removed]
        rw [keepTest]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [totalAtomsFor_cons, if_pos removed.2]
        rw [balanceAtoms_cons, if_pos removed]
        have targetAbsent :
            (account, resourceId) ∉ rest.map Holding.key := by
          intro targetMem
          apply unique.1
          rw [List.mem_map] at targetMem ⊢
          obtain ⟨targetHolding, targetHoldingMem, targetKey⟩ := targetMem
          exact ⟨targetHolding, targetHoldingMem,
            targetKey.trans (Prod.ext removed.1.symm removed.2.symm)⟩
        have restBalanceZero :=
          balanceAtoms_eq_zero_of_key_absent rest account resourceId targetAbsent
        rw [Nat.add_sub_cancel_left]
        change totalAtomsFor (withoutBalance rest account resourceId) resourceId =
          totalAtomsFor rest resourceId
        rw [ih unique.2, restBalanceZero, Nat.sub_zero]
      · have keepTest :
          decide (¬(holding.account = account ∧ holding.resourceId = resourceId)) =
            true := by
            simp [removed]
        rw [keepTest]
        simp only [↓reduceIte]
        rw [totalAtomsFor_cons, totalAtomsFor_cons]
        rw [balanceAtoms_cons, if_neg removed]
        change
          (if holding.resourceId = resourceId then holding.quantity.atoms else 0) +
              totalAtomsFor (withoutBalance rest account resourceId) resourceId =
            (if holding.resourceId = resourceId then holding.quantity.atoms else 0) +
              totalAtomsFor rest resourceId - balanceAtoms rest account resourceId
        rw [ih unique.2]
        by_cases sameResource : holding.resourceId = resourceId
        · rw [if_pos sameResource]
          rw [Nat.add_sub_assoc (balanceAtoms_le_totalAtomsFor rest account resourceId)]
        · simp [sameResource]

/-- Two distinct account balances together cannot exceed global supply. -/
theorem twoBalances_le_totalAtomsFor
    {Account : Type}
    [DecidableEq Account]
    (holdings : List (Holding Account))
    (left right : Account)
    (resourceId : ResourceId)
    (distinct : left ≠ right) :
    balanceAtoms holdings left resourceId +
        balanceAtoms holdings right resourceId ≤
      totalAtomsFor holdings resourceId := by
  induction holdings with
  | nil => simp [balanceAtoms, balanceAtomsIn, totalAtomsFor]
  | cons holding rest ih =>
      rw [balanceAtoms_cons, balanceAtoms_cons, totalAtomsFor_cons]
      by_cases leftMatch :
          holding.account = left ∧ holding.resourceId = resourceId
      · have notRight :
            ¬(holding.account = right ∧ holding.resourceId = resourceId) := by
          intro rightMatch
          exact distinct (leftMatch.1.symm.trans rightMatch.1)
        rw [if_pos leftMatch, if_neg notRight, if_pos leftMatch.2]
        exact Nat.add_le_add_left
          (balanceAtoms_le_totalAtomsFor rest right resourceId)
          holding.quantity.atoms
      · by_cases rightMatch :
          holding.account = right ∧ holding.resourceId = resourceId
        · have notLeft := leftMatch
          rw [if_neg notLeft, if_pos rightMatch, if_pos rightMatch.2]
          rw [Nat.add_comm]
          exact Nat.add_le_add_left
            (balanceAtoms_le_totalAtomsFor rest left resourceId)
            holding.quantity.atoms
        · rw [if_neg leftMatch, if_neg rightMatch]
          by_cases sameResource : holding.resourceId = resourceId
          · rw [if_pos sameResource]
            exact Nat.le_add_left_of_le ih
          · rw [if_neg sameResource, Nat.zero_add]
            exact ih

theorem totalAtomsFor_setBalance_same {Account : Type} [DecidableEq Account]
    (holdings : List (Holding Account))
    (account : Account)
    (resourceId : ResourceId)
    (atoms : Nat)
    (unique : (holdings.map Holding.key).Nodup) :
    totalAtomsFor (setBalance holdings account resourceId atoms) resourceId =
      totalAtomsFor holdings resourceId -
        balanceAtoms holdings account resourceId + atoms := by
  by_cases zero : atoms = 0
  · simp only [setBalance, dif_pos zero]
    rw [totalAtomsFor_withoutBalance_same holdings account resourceId unique,
      zero, Nat.add_zero]
  · simp only [setBalance, dif_neg zero]
    rw [totalAtomsFor_cons]
    simp only [↓reduceIte]
    rw [totalAtomsFor_withoutBalance_same holdings account resourceId unique]
    exact Nat.add_comm _ _

theorem totalAtomsFor_setBalance_other {Account : Type} [DecidableEq Account]
    (holdings : List (Holding Account))
    (account : Account)
    (setResource queriedResource : ResourceId)
    (atoms : Nat)
    (different : setResource ≠ queriedResource) :
    totalAtomsFor (setBalance holdings account setResource atoms) queriedResource =
      totalAtomsFor holdings queriedResource := by
  by_cases zero : atoms = 0
  · simp only [setBalance, dif_pos zero]
    exact totalAtomsFor_withoutBalance_other holdings
      account setResource queriedResource different
  · simp only [setBalance, dif_neg zero]
    rw [totalAtomsFor_cons, if_neg different, Nat.zero_add]
    exact totalAtomsFor_withoutBalance_other holdings
      account setResource queriedResource different

/-- Every held resource resolves to an authoritative catalog specification. -/
def ResourcesKnown {Account : Type}
    (resourceCatalog : ResourceCatalog)
    (holdings : List (Holding Account)) : Prop :=
  ∀ holding, holding ∈ holdings →
    ∃ spec, resourceCatalog.lookup holding.resourceId = some spec

theorem ResourcesKnown.withoutBalance {Account : Type} [DecidableEq Account]
    {resourceCatalog : ResourceCatalog}
    {holdings : List (Holding Account)}
    (known : ResourcesKnown resourceCatalog holdings)
    (account : Account)
    (resourceId : ResourceId) :
    ResourcesKnown resourceCatalog (withoutBalance holdings account resourceId) := by
  intro holding holdingMem
  apply known holding
  exact (List.mem_filter.mp holdingMem).1

theorem ResourcesKnown.setBalance {Account : Type} [DecidableEq Account]
    {resourceCatalog : ResourceCatalog}
    {holdings : List (Holding Account)}
    (known : ResourcesKnown resourceCatalog holdings)
    (account : Account)
    (resourceId : ResourceId)
    (atoms : Nat)
    (setResourceKnown : ∃ spec, resourceCatalog.lookup resourceId = some spec) :
  ResourcesKnown resourceCatalog (setBalance holdings account resourceId atoms) := by
  by_cases zero : atoms = 0
  · simp only [Maquina.setBalance, dif_pos zero]
    exact known.withoutBalance account resourceId
  · simp only [Maquina.setBalance, dif_neg zero]
    intro holding holdingMem
    rw [List.mem_cons] at holdingMem
    rcases holdingMem with isNew | isOld
    · subst holding
      exact setResourceKnown
    · exact known.withoutBalance account resourceId holding isOld

/-- Every bounded resource respects its declared global maximum. -/
def RespectsResourceLimits {Account : Type}
    (resourceCatalog : ResourceCatalog)
    (holdings : List (Holding Account)) : Prop :=
  ∀ {resourceId spec maximum positive},
    resourceCatalog.lookup resourceId = some spec →
    spec.limit = .bounded maximum positive →
    totalAtomsFor holdings resourceId ≤ maximum.atoms

/--
The one authoritative finite sparse holding state. Inventories and global
supplies are projections of this value rather than separate mutable stores.
Every `AccountId` is valid by construction; held resource identities must
resolve in the authoritative resource catalog.
-/
structure WorldState (resourceCatalog : ResourceCatalog) where
  holdings : List (Holding AccountId)
  keysUnique : (holdings.map Holding.key).Nodup
  resourcesKnown : ResourcesKnown resourceCatalog holdings
  respectsLimits : RespectsResourceLimits resourceCatalog holdings
  deriving Repr

namespace WorldState

/-- Canonical worlds are equal when their authoritative holdings are equal. -/
theorem ext_holdings
    {resourceCatalog : ResourceCatalog}
    (left right : WorldState resourceCatalog)
    (same : left.holdings = right.holdings) :
    left = right := by
  cases left
  cases right
  simp_all

def empty (resourceCatalog : ResourceCatalog) : WorldState resourceCatalog where
  holdings := []
  keysUnique := by simp
  resourcesKnown := by simp [ResourcesKnown]
  respectsLimits := by simp [RespectsResourceLimits, totalAtomsFor]

/--
Construct a world with exactly one positive holding. The final premise states
that the quantity respects any bounded limit carried by the resolved resource.
-/
def singleton
    (resourceCatalog : ResourceCatalog)
    (account : AccountId)
    (resourceId : ResourceId)
    (quantity : Quantity)
    (positive : 0 < quantity.atoms)
    {spec : ResourceSpec}
    (found : resourceCatalog.lookup resourceId = some spec)
    (withinLimit : ∀ maximum limitPositive,
      spec.limit = .bounded maximum limitPositive →
        quantity.atoms ≤ maximum.atoms) : WorldState resourceCatalog where
  holdings := [{ account, resourceId, quantity, positive }]
  keysUnique := by simp
  resourcesKnown := by
    intro holding holdingMem
    simp only [List.mem_singleton] at holdingMem
    subst holding
    exact ⟨spec, found⟩
  respectsLimits := by
    intro queriedId queriedSpec maximum limitPositive queriedFound limitEq
    by_cases same : queriedId = resourceId
    · subst queriedId
      have specEq : queriedSpec = spec :=
        resourceCatalog.spec_unique queriedFound found
      subst queriedSpec
      simpa [totalAtomsFor] using withinLimit maximum limitPositive limitEq
    · have different : resourceId ≠ queriedId := Ne.symm same
      simp [totalAtomsFor, different]

def balance {resourceCatalog : ResourceCatalog}
    (state : WorldState resourceCatalog)
    (account : AccountId)
    (resourceId : ResourceId) : Quantity :=
  ⟨balanceAtoms state.holdings account resourceId⟩

def total {resourceCatalog : ResourceCatalog}
    (state : WorldState resourceCatalog)
    (resourceId : ResourceId) : Quantity :=
  ⟨totalAtomsFor state.holdings resourceId⟩

/-- A world's derived total is a legal supply for the catalog resource. -/
def supply {resourceCatalog : ResourceCatalog}
    (state : WorldState resourceCatalog)
    {resourceId : ResourceId}
    {spec : ResourceSpec}
    (found : resourceCatalog.lookup resourceId = some spec) : Supply spec := by
  unfold Supply
  cases limitEq : spec.limit with
  | unbounded =>
      exact state.total resourceId
  | bounded maximum positive =>
      refine ⟨state.total resourceId, ?_⟩
      exact state.respectsLimits found limitEq

/-- Every bounded resource total satisfies its declared global maximum. -/
theorem bounded_total_le {resourceCatalog : ResourceCatalog}
    (state : WorldState resourceCatalog)
    {resourceId : ResourceId}
    {spec : ResourceSpec}
    (maximum : Quantity)
    (positive : 0 < maximum.atoms)
    (found : resourceCatalog.lookup resourceId = some spec)
    (limitEq : spec.limit = .bounded maximum positive) :
    (state.total resourceId).atoms ≤ maximum.atoms :=
  state.respectsLimits found limitEq

/-- A declared unique resource has at most one atom globally. -/
theorem unique_total_le_one {resourceCatalog : ResourceCatalog}
    (state : WorldState resourceCatalog)
    (header : ResourceHeader)
    (found : resourceCatalog.lookup header.id = some (ResourceSpec.unique header)) :
    (state.total header.id).atoms ≤ 1 :=
  state.respectsLimits found rfl

/-- A unique resource cannot simultaneously occupy two distinct accounts. -/
theorem unique_not_held_by_distinct_accounts
    {resourceCatalog : ResourceCatalog}
    (state : WorldState resourceCatalog)
    (header : ResourceHeader)
    (found : resourceCatalog.lookup header.id = some (ResourceSpec.unique header))
    (left right : AccountId)
    (distinct : left ≠ right)
    (leftHeld : (state.balance left header.id).atoms = 1)
    (rightHeld : (state.balance right header.id).atoms = 1) : False := by
  have together := twoBalances_le_totalAtomsFor state.holdings left right
    header.id distinct
  have maximum := state.unique_total_le_one header found
  change
    (state.balance left header.id).atoms +
        (state.balance right header.id).atoms ≤
      (state.total header.id).atoms at together
  omega

/-- A declared edition cannot exceed its positive copy limit. -/
theorem edition_total_le_max {resourceCatalog : ResourceCatalog}
    (state : WorldState resourceCatalog)
    (header : ResourceHeader)
    (maxCopies : Nat)
    (positive : 0 < maxCopies)
    (found : resourceCatalog.lookup header.id =
      some (ResourceSpec.edition header maxCopies positive)) :
    (state.total header.id).atoms ≤ maxCopies :=
  state.respectsLimits found rfl

end WorldState

end Maquina
