import Maquina

/-!
# Operation Veiled Accord Domain

Fictional ceasefire-corridor vocabulary owned entirely by the game. Routes,
claims, loyalty, escort doctrine, betrayal, and mission payoffs never enter the
Maquina kernel.
-/

namespace Maquina.Games.VeiledAccord

inductive Phase where
  | negotiation
  | sealed
  | resolved
  deriving DecidableEq, Repr

inductive Route where
  | ridge
  | harbor
  deriving DecidableEq, Repr

inductive PartnerNature where
  | cooperative
  | opportunist
  deriving DecidableEq, Repr

inductive TacticalOrder where
  | escort
  | seizeAsset
  deriving DecidableEq, Repr

inductive MissionOutcome where
  | active
  | paretoAccord
  | verifiedCooperation
  | exploitedCooperation
  | trustedBetrayal
  | preemptiveBetrayal
  | mutualDefection
  deriving DecidableEq, Repr

inductive Statement where
  | promiseDefense
  | claimHarborSafe
  | verifiedRidgeThreat
  | accordRatified
  deriving DecidableEq, Repr

/-- Truth and evidence are separate from the inert statement being sent. -/
structure Communication where
  statement : Statement
  verified : Bool
  deriving DecidableEq, Repr

structure AccordTerms where
  route : Route
  defenseTokens : Nat
  mutualEscort : Bool
  deriving DecidableEq, Repr

def defenseTokenId : ResourceId := ⟨800⟩
def intelligenceSealId : ResourceId := ⟨801⟩
def evacueeId : ResourceId := ⟨802⟩
def strategicAssetId : ResourceId := ⟨803⟩

def defenseTokenSpec : ResourceSpec :=
  ResourceSpec.discrete { id := defenseTokenId, name := "defense token" }

def intelligenceSealSpec : ResourceSpec :=
  ResourceSpec.unique { id := intelligenceSealId, name := "verified intelligence seal" }

def evacueeSpec : ResourceSpec :=
  ResourceSpec.edition { id := evacueeId, name := "evacuees" }
    24 (by decide)

def strategicAssetSpec : ResourceSpec :=
  ResourceSpec.unique { id := strategicAssetId, name := "strategic asset" }

def resourceCatalog : ResourceCatalog :=
  ResourceCatalog.ofList
    [defenseTokenSpec, intelligenceSealSpec, evacueeSpec, strategicAssetSpec]

end Maquina.Games.VeiledAccord
