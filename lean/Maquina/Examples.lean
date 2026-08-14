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

def coinId : ObjectId := ⟨10⟩
def clockId : ObjectId := ⟨20⟩
def artifactId : ObjectId := ⟨30⟩
def editionId : ObjectId := ⟨40⟩

def coinHeader : ObjectHeader := { id := coinId, name := "coin" }
def clockHeader : ObjectHeader := { id := clockId, name := "clock time" }
def artifactHeader : ObjectHeader := { id := artifactId, name := "artifact" }
def editionHeader : ObjectHeader := { id := editionId, name := "edition" }

def coinSpec : ObjectSpec := ObjectSpec.discrete coinHeader

def oneSecond : PositiveRat where
  value := 1
  positive := by decide

def clockSpec : ObjectSpec :=
  ObjectSpec.measured clockHeader Dimension.time .plain oneSecond

def artifactSpec : ObjectSpec := ObjectSpec.unique artifactHeader

def editionSpec : ObjectSpec :=
  ObjectSpec.edition editionHeader 10 (by decide)

def coinCatalog : Catalog := Catalog.singleton coinSpec
def clockCatalog : Catalog := Catalog.singleton clockSpec
def artifactCatalog : Catalog := Catalog.singleton artifactSpec
def editionCatalog : Catalog := Catalog.singleton editionSpec

/-! ## Empty, discrete, and measured inventories -/

def emptyInventory : WorldState coinCatalog := WorldState.empty coinCatalog

example : (emptyInventory.balance alice coinId).atoms = 0 := rfl

def fungibleInventory : WorldState coinCatalog :=
  WorldState.singleton coinCatalog alice coinId ⟨10⟩ (by decide)
    (spec := coinSpec)
    (Catalog.singleton_lookup_same coinSpec)
    (by
      intro maximum positive limitEq
      cases limitEq)

example : (fungibleInventory.balance alice coinId).atoms = 10 := by
  native_decide

def measuredInventory : WorldState clockCatalog :=
  WorldState.singleton clockCatalog alice clockId ⟨90⟩ (by decide)
    (spec := clockSpec)
    (Catalog.singleton_lookup_same clockSpec)
    (by
      intro maximum positive limitEq
      cases limitEq)

example : clockSpec.definition =
    .measured Dimension.time .plain oneSecond := rfl

example : (measuredInventory.balance alice clockId).atoms = 90 := by
  native_decide

/-! ## Unique object movement -/

def uniqueInventory : WorldState artifactCatalog :=
  WorldState.singleton artifactCatalog alice artifactId ⟨1⟩ (by decide)
    (spec := artifactSpec)
    (Catalog.singleton_lookup_same artifactSpec)
    (by
      intro maximum positive limitEq
      cases limitEq
      decide)

def uniqueEntry : BasketEntry where
  objectId := artifactId
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

def editionInitial : WorldState editionCatalog :=
  WorldState.singleton editionCatalog alice editionId ⟨10⟩ (by decide)
    (spec := editionSpec)
    (Catalog.singleton_lookup_same editionSpec)
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

def editionSplit : WorldState editionCatalog :=
  applyTransferState editionAccepted

example : (editionSplit.balance alice editionId).atoms = 6 := by
  native_decide

example : (editionSplit.balance bob editionId).atoms = 4 := by
  native_decide

example : (editionSplit.total editionId).atoms = 10 := by
  exact applyTransferState_total editionAccepted editionId

/-! ## Successful and rejected multi-object baskets -/

/-- An example catalog assigning an unbounded discrete definition to every ID. -/
def openDiscreteCatalog : Catalog where
  lookup := fun id => some (ObjectSpec.discrete { id, name := "example" })
  idMatches := by
    intro id spec found
    have specEq : ObjectSpec.discrete { id, name := "example" } = spec :=
      Option.some.inj found
    rw [← specEq]
    rfl

def multiInventory : WorldState openDiscreteCatalog where
  holdings :=
    [ { account := alice, objectId := coinId, quantity := ⟨10⟩,
        positive := by decide },
      { account := alice, objectId := clockId, quantity := ⟨20⟩,
        positive := by decide } ]
  keysUnique := by native_decide
  objectsKnown := by
    intro holding holdingMem
    exact ⟨ObjectSpec.discrete { id := holding.objectId, name := "example" }, rfl⟩
  respectsLimits := by
    intro objectId spec maximum positive found limitEq
    have specEq :
        ObjectSpec.discrete { id := objectId, name := "example" } = spec :=
      Option.some.inj found
    rw [← specEq] at limitEq
    simp [ObjectSpec.discrete] at limitEq

def multiBasket : Basket where
  entries :=
    [ { objectId := coinId, quantity := ⟨3⟩, positive := by decide },
      { objectId := clockId, quantity := ⟨5⟩, positive := by decide } ]
  objectsUnique := by native_decide

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
    [ { objectId := coinId, quantity := ⟨50⟩, positive := by decide },
      { objectId := clockId, quantity := ⟨30⟩, positive := by decide } ]
  objectsUnique := by native_decide

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

end Maquina.Examples
