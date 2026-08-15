import Maquina.Possession
import Maquina.Transfer

/-!
# Constructible Maquina Examples

Small closed examples showing that the model's proof premises can be built and
that accepted and rejected transfers compute as specified.
-/

namespace Maquina.Examples

def alice : AccountId := ⟨1⟩
def bob : AccountId := ⟨2⟩
def carol : AccountId := ⟨3⟩

def coinId : ResourceId := ⟨10⟩
def clockId : ResourceId := ⟨20⟩
def artifactId : ResourceId := ⟨30⟩
def editionId : ResourceId := ⟨40⟩

def coinHeader : ResourceHeader := { id := coinId, name := "coin" }
def clockHeader : ResourceHeader := { id := clockId, name := "clock time" }
def artifactHeader : ResourceHeader := { id := artifactId, name := "artifact" }
def editionHeader : ResourceHeader := { id := editionId, name := "edition" }

def coinSpec : ResourceSpec := ResourceSpec.discrete coinHeader

def oneSecond : PositiveRat where
  value := 1
  positive := by decide

def clockSpec : ResourceSpec :=
  ResourceSpec.measured clockHeader Dimension.time .plain oneSecond

def artifactSpec : ResourceSpec := ResourceSpec.unique artifactHeader

def editionSpec : ResourceSpec :=
  ResourceSpec.edition editionHeader 10 (by decide)

def coinResourceCatalog : ResourceCatalog := ResourceCatalog.singleton coinSpec
def clockResourceCatalog : ResourceCatalog := ResourceCatalog.singleton clockSpec
def artifactResourceCatalog : ResourceCatalog := ResourceCatalog.singleton artifactSpec
def editionResourceCatalog : ResourceCatalog := ResourceCatalog.singleton editionSpec

/-! ## Empty, discrete, and measured inventories -/

def emptyInventory : WorldState coinResourceCatalog := WorldState.empty coinResourceCatalog

example : (emptyInventory.balance alice coinId).atoms = 0 := rfl

def fungibleInventory : WorldState coinResourceCatalog :=
  WorldState.singleton coinResourceCatalog alice coinId ⟨10⟩ (by decide)
    (spec := coinSpec)
    (ResourceCatalog.singleton_lookup_same coinSpec)
    (by
      intro maximum positive limitEq
      cases limitEq)

example : (fungibleInventory.balance alice coinId).atoms = 10 := by
  native_decide

def measuredInventory : WorldState clockResourceCatalog :=
  WorldState.singleton clockResourceCatalog alice clockId ⟨90⟩ (by decide)
    (spec := clockSpec)
    (ResourceCatalog.singleton_lookup_same clockSpec)
    (by
      intro maximum positive limitEq
      cases limitEq)

example : clockSpec.definition =
    .measured Dimension.time .plain oneSecond := rfl

example : (measuredInventory.balance alice clockId).atoms = 90 := by
  native_decide

/-! ## Unique resource movement -/

def uniqueInventory : WorldState artifactResourceCatalog :=
  WorldState.singleton artifactResourceCatalog alice artifactId ⟨1⟩ (by decide)
    (spec := artifactSpec)
    (ResourceCatalog.singleton_lookup_same artifactSpec)
    (by
      intro maximum positive limitEq
      cases limitEq
      decide)

def uniqueEntry : BasketEntry where
  resourceId := artifactId
  quantity := .one
  positive := by decide

def uniqueTransfer : Transfer where
  source := alice
  destination := bob
  basket := Basket.singleton artifactId .one (by decide)

theorem uniqueAccepted : AcceptedTransfer uniqueInventory uniqueTransfer where
  issuesEmpty := by native_decide

example :
    ((applyTransferState uniqueAccepted).balance alice artifactId).atoms = 0 := by
  native_decide

example :
    ((applyTransferState uniqueAccepted).balance bob artifactId).atoms = 1 := by
  native_decide

/-! ## Bounded edition split across accounts -/

def editionInitial : WorldState editionResourceCatalog :=
  WorldState.singleton editionResourceCatalog alice editionId ⟨10⟩ (by decide)
    (spec := editionSpec)
    (ResourceCatalog.singleton_lookup_same editionSpec)
    (by
      intro maximum positive limitEq
      cases limitEq
      decide)

def editionTransfer : Transfer where
  source := alice
  destination := bob
  basket := Basket.singleton editionId ⟨4⟩ (by decide)

theorem editionAccepted : AcceptedTransfer editionInitial editionTransfer where
  issuesEmpty := by native_decide

def editionSplit : WorldState editionResourceCatalog :=
  applyTransferState editionAccepted

example : (editionSplit.balance alice editionId).atoms = 6 := by
  native_decide

example : (editionSplit.balance bob editionId).atoms = 4 := by
  native_decide

example : (editionSplit.total editionId).atoms = 10 := by
  exact applyTransferState_total editionAccepted editionId

/-! ## Successful and rejected multi-resource baskets -/

/-- An example catalog assigning an unbounded discrete definition to every ID. -/
def openDiscreteResourceCatalog : ResourceCatalog where
  lookup := fun id => some (ResourceSpec.discrete { id, name := "example" })
  idMatches := by
    intro id spec found
    have specEq : ResourceSpec.discrete { id, name := "example" } = spec :=
      Option.some.inj found
    rw [← specEq]
    rfl

def multiInventory : WorldState openDiscreteResourceCatalog where
  holdings :=
    [ { account := alice, resourceId := coinId, quantity := ⟨10⟩,
        positive := by decide },
      { account := alice, resourceId := clockId, quantity := ⟨20⟩,
        positive := by decide } ]
  keysUnique := by native_decide
  resourcesKnown := by
    intro holding holdingMem
    exact ⟨ResourceSpec.discrete { id := holding.resourceId, name := "example" }, rfl⟩
  respectsLimits := by
    intro resourceId spec maximum positive found limitEq
    have specEq :
        ResourceSpec.discrete { id := resourceId, name := "example" } = spec :=
      Option.some.inj found
    rw [← specEq] at limitEq
    simp [ResourceSpec.discrete] at limitEq

def multiBasket : Basket where
  entries :=
    [ { resourceId := coinId, quantity := ⟨3⟩, positive := by decide },
      { resourceId := clockId, quantity := ⟨5⟩, positive := by decide } ]
  resourcesUnique := by native_decide

def multiTransfer : Transfer where
  source := alice
  destination := bob
  basket := multiBasket

theorem multiAccepted : AcceptedTransfer multiInventory multiTransfer where
  issuesEmpty := by native_decide

example :
    ((applyTransferState multiAccepted).balance alice coinId).atoms = 7 := by
  native_decide

example :
    ((applyTransferState multiAccepted).balance bob clockId).atoms = 5 := by
  native_decide

example :
    replayReceipt (transferReceipt multiAccepted) multiInventory.holdings =
      (applyTransferState multiAccepted).holdings :=
  replay_transferReceipt multiAccepted

def rejectedBasket : Basket where
  entries :=
    [ { resourceId := coinId, quantity := ⟨50⟩, positive := by decide },
      { resourceId := clockId, quantity := ⟨30⟩, positive := by decide } ]
  resourcesUnique := by native_decide

def rejectedTransfer : Transfer where
  source := alice
  destination := bob
  basket := rejectedBasket

example : transferIssues multiInventory rejectedTransfer =
    [ .shortfall coinId 50 10 40,
      .shortfall clockId 30 20 10 ] := by
  native_decide

example : assessAndApply multiInventory rejectedTransfer = none := by
  native_decide

/-! ## Non-mutating possession assessment -/

def heldRequirement : PossessionRequirement where
  account := alice
  basket := multiBasket

theorem heldAccepted : AcceptedPossession multiInventory heldRequirement where
  issuesEmpty := by native_decide

example : (possessionReceipt heldAccepted).lines.map
    (fun line => (line.required.atoms, line.available.atoms)) =
    [(3, 10), (5, 20)] := by
  native_decide

def missingRequirement : PossessionRequirement where
  account := bob
  basket := multiBasket

example : possessionIssues multiInventory missingRequirement =
    [ .shortfall coinId 3 0 3,
      .shortfall clockId 5 0 5 ] := by
  native_decide

end Maquina.Examples
