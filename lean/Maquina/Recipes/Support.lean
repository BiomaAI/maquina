import Maquina.Game

/-!
# Composition Recipe Fixture

Only shared names, identities, and projections live here. This module contains
no transition helper and no world mutation function. Every recipe declares its
own Process, typed Operation, proposal, and generic simulator execution.
-/

namespace Maquina.Recipes.Support

inductive Kind where
  | attachment
  | containment
  | membership
  | overlay
  | capability
  deriving DecidableEq, Repr

def ledger : AccountId := ⟨9000⟩
def chassisAccount : AccountId := ⟨9001⟩
def wheelAccount : AccountId := ⟨9002⟩
def bagAccount : AccountId := ⟨9003⟩
def pouchAccount : AccountId := ⟨9004⟩
def vehicleAccount : AccountId := ⟨9005⟩
def crewAccount : AccountId := ⟨9006⟩
def situationAccount : AccountId := ⟨9007⟩
def regionAccount : AccountId := ⟨9008⟩
def toolAccount : AccountId := ⟨9009⟩
def custodyAccount : AccountId := ⟨9010⟩

def chassisBody : ResourceId := ⟨13000⟩
def wheelBody : ResourceId := ⟨13001⟩
def bagBody : ResourceId := ⟨13002⟩
def pouchBody : ResourceId := ⟨13003⟩
def vehicleBody : ResourceId := ⟨13004⟩
def crewBody : ResourceId := ⟨13005⟩
def situationBody : ResourceId := ⟨13006⟩
def regionBody : ResourceId := ⟨13007⟩
def toolBody : ResourceId := ⟨13008⟩

def cargoId : ResourceId := ⟨13100⟩
def driverSeatId : ResourceId := ⟨13101⟩
def violenceId : ResourceId := ⟨13102⟩
def humidityId : ResourceId := ⟨13103⟩
def capabilityId : ResourceId := ⟨13104⟩
def phaseOpenId : ResourceId := ⟨13105⟩
def phaseActiveId : ResourceId := ⟨13106⟩

def endpointFamily : ResourceFamily Nat :=
  ResourceFamily.modularNat 3 0 (by decide) (by decide) "composition/endpoint"

def linkFamily : ResourceFamily Nat :=
  ResourceFamily.modularNat 3 1 (by decide) (by decide) "composition/link"

def leaseFamily : ResourceFamily Nat :=
  ResourceFamily.modularNat 3 2 (by decide) (by decide) "composition/link-lease"

def endpoint (body : ResourceId) (slot : Nat) : RelationEndpoint := { body, slot }

def describeEndpoint : Nat → RelationEndpoint
  | 0 => endpoint chassisBody 0
  | 1 => endpoint wheelBody 0
  | 2 => endpoint bagBody 0
  | 3 => endpoint pouchBody 0
  | 4 => endpoint vehicleBody 0
  | 5 => endpoint crewBody 0
  | 6 => endpoint situationBody 0
  | 7 => endpoint regionBody 0
  | 8 => endpoint toolBody 0
  | slot => endpoint ⟨14000 + slot⟩ slot

def describeLink : Nat → RelationLink Kind
  | 0 => { kind := .attachment, left := describeEndpoint 0, right := describeEndpoint 1 }
  | 1 => { kind := .containment, left := describeEndpoint 2, right := describeEndpoint 3 }
  | 2 => { kind := .attachment, left := describeEndpoint 4, right := describeEndpoint 0 }
  | 3 => { kind := .membership, left := describeEndpoint 4, right := describeEndpoint 5 }
  | 4 => { kind := .membership, left := describeEndpoint 6, right := describeEndpoint 5 }
  | 5 => { kind := .overlay, left := describeEndpoint 7, right := describeEndpoint 4 }
  | 6 => { kind := .capability, left := describeEndpoint 4, right := describeEndpoint 8 }
  | key =>
      { kind := .attachment
        left := endpoint ⟨15000 + key * 2⟩ 0
        right := endpoint ⟨15000 + key * 2 + 1⟩ 0 }

def relationModel : RelationModel Kind Nat Nat where
  endpointFamily := endpointFamily
  describeEndpoint := describeEndpoint
  linkFamily := linkFamily
  leaseFamily := leaseFamily
  describe := describeLink
  ledger := ledger
  endpointLinkDisjoint := ResourceFamily.modularNat_disjoint
    3 0 1 (by decide) (by decide) (by decide) (by decide)
    "composition/endpoint" "composition/link"
  endpointLeaseDisjoint := ResourceFamily.modularNat_disjoint
    3 0 2 (by decide) (by decide) (by decide) (by decide)
    "composition/endpoint" "composition/link-lease"
  linkLeaseDisjoint := ResourceFamily.modularNat_disjoint
    3 1 2 (by decide) (by decide) (by decide) (by decide)
    "composition/link" "composition/link-lease"

def relationPolicy : RelationPolicy Kind where
  compatible := fun _ left right => decide (left.body ≠ right.body)
  traversableForward := fun _ => true
  traversableBackward
    | .overlay => false
    | _ => true

def uniqueSpec (id : ResourceId) (name : String) : ResourceSpec :=
  ResourceSpec.unique { id, name }

def tokenSpec (id : ResourceId) (name : String) : ResourceSpec :=
  ResourceSpec.discrete { id, name }

def recipeCatalog : ResourceCatalog :=
  ResourceCatalog.ofList
    [ uniqueSpec chassisBody "chassis Body",
      uniqueSpec wheelBody "wheel Body",
      uniqueSpec bagBody "bag Body",
      uniqueSpec pouchBody "pouch Body",
      uniqueSpec vehicleBody "vehicle Body",
      uniqueSpec crewBody "crew Body",
      uniqueSpec situationBody "situation Body",
      uniqueSpec regionBody "region Body",
      uniqueSpec toolBody "tool Body",
      tokenSpec cargoId "cargo",
      uniqueSpec driverSeatId "driver seat",
      tokenSpec violenceId "violence opportunity",
      tokenSpec humidityId "humidity",
      uniqueSpec capabilityId "shared capability",
      uniqueSpec phaseOpenId "open phase",
      uniqueSpec phaseActiveId "active phase",
      endpointFamily.spec 0, endpointFamily.spec 1,
      endpointFamily.spec 2, endpointFamily.spec 3,
      endpointFamily.spec 4, endpointFamily.spec 5,
      endpointFamily.spec 6, endpointFamily.spec 7,
      endpointFamily.spec 8,
      linkFamily.spec 0, linkFamily.spec 1, linkFamily.spec 2,
      linkFamily.spec 3, linkFamily.spec 4, linkFamily.spec 5,
      linkFamily.spec 6,
      leaseFamily.spec 0, leaseFamily.spec 1, leaseFamily.spec 2,
      leaseFamily.spec 3, leaseFamily.spec 4, leaseFamily.spec 5,
      leaseFamily.spec 6 ]

end Maquina.Recipes.Support
