import Maquina.Game

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
def accordBodyId : ResourceId := ⟨804⟩

def defenseTokenSpec : ResourceSpec :=
  ResourceSpec.discrete { id := defenseTokenId, name := "defense token" }

def intelligenceSealSpec : ResourceSpec :=
  ResourceSpec.unique { id := intelligenceSealId, name := "verified intelligence seal" }

def evacueeSpec : ResourceSpec :=
  ResourceSpec.edition { id := evacueeId, name := "evacuees" }
    24 (by decide)

def strategicAssetSpec : ResourceSpec :=
  ResourceSpec.unique { id := strategicAssetId, name := "strategic asset" }

def accordBodySpec : ResourceSpec :=
  ResourceSpec.unique { id := accordBodyId, name := "accord protocol Body" }

def resourceCatalog : ResourceCatalog :=
  ResourceCatalog.ofList
    [defenseTokenSpec, intelligenceSealSpec, evacueeSpec, strategicAssetSpec,
      accordBodySpec]

/-! ## Strategic Machine language -/

inductive Label where
  | evidence
  | defense
  | evacuees
  | asset
  | saved
  | lost
  | assetRecipient
  deriving DecidableEq, Repr

inductive ProcessKind where
  | shareEvidence
  | fundPact
  | settleVerified
  | settleExploited
  | settleBetrayal
  | settleMutualDefection
  | settlePareto
  deriving DecidableEq, Repr

inductive QueueKind where
  | strategic
  deriving DecidableEq, Repr

/-- Veiled Accord uses atomic zero-work Processes, so it exposes no queues. -/
inductive QueuePort : QueueStage → Type

private def positiveBasket
    (resourceId : ResourceId)
    (atoms : Nat)
    (positive : 0 < atoms) : Basket :=
  Basket.singleton resourceId ⟨atoms⟩ positive

private def port
    (label : Label)
    (basket : Basket)
    (nonempty : basket.entries ≠ []) : ProcessPort Label where
  label := label
  basket := basket
  nonempty := nonempty

def shareEvidenceProcess : Process Label where
  consumed := [port .evidence (positiveBasket intelligenceSealId 1 (by decide))
    (by simp [positiveBasket, Basket.singleton])]
  reserved := []
  activeCustody := []
  outputs := [port .evidence (positiveBasket intelligenceSealId 1 (by decide))
    (by simp [positiveBasket, Basket.singleton])]
  consumedLabelsUnique := by native_decide
  reservedLabelsUnique := by simp
  activeCustodyLabelsUnique := by simp
  outputLabelsUnique := by native_decide
  requiredWork := 0

def fundPactProcess : Process Label where
  consumed := [port .defense (positiveBasket defenseTokenId 2 (by decide))
    (by simp [positiveBasket, Basket.singleton])]
  reserved := []
  activeCustody := []
  outputs := [port .defense (positiveBasket defenseTokenId 2 (by decide))
    (by simp [positiveBasket, Basket.singleton])]
  consumedLabelsUnique := by native_decide
  reservedLabelsUnique := by simp
  activeCustodyLabelsUnique := by simp
  outputLabelsUnique := by native_decide
  requiredWork := 0

private def settlementProcess
    (saved lost : Nat)
    (savedPositive : 0 < saved)
    (lostPositive : 0 < lost) : Process Label where
  consumed :=
    [ port .evacuees (positiveBasket evacueeId 24 (by decide))
        (by simp [positiveBasket, Basket.singleton]),
      port .asset (positiveBasket strategicAssetId 1 (by decide))
        (by simp [positiveBasket, Basket.singleton]) ]
  reserved := []
  activeCustody := []
  outputs :=
    [ port .saved (positiveBasket evacueeId saved savedPositive)
        (by simp [positiveBasket, Basket.singleton]),
      port .lost (positiveBasket evacueeId lost lostPositive)
        (by simp [positiveBasket, Basket.singleton]),
      port .assetRecipient (positiveBasket strategicAssetId 1 (by decide))
        (by simp [positiveBasket, Basket.singleton]) ]
  consumedLabelsUnique := by simp [port]
  reservedLabelsUnique := by simp
  activeCustodyLabelsUnique := by simp
  outputLabelsUnique := by simp [port]
  requiredWork := 0

def paretoSettlementProcess : Process Label where
  consumed :=
    [ port .evacuees (positiveBasket evacueeId 24 (by decide))
        (by simp [positiveBasket, Basket.singleton]),
      port .asset (positiveBasket strategicAssetId 1 (by decide))
        (by simp [positiveBasket, Basket.singleton]) ]
  reserved := []
  activeCustody := []
  outputs :=
    [ port .saved (positiveBasket evacueeId 24 (by decide))
        (by simp [positiveBasket, Basket.singleton]),
      port .assetRecipient (positiveBasket strategicAssetId 1 (by decide))
        (by simp [positiveBasket, Basket.singleton]) ]
  consumedLabelsUnique := by simp [port]
  reservedLabelsUnique := by simp
  activeCustodyLabelsUnique := by simp
  outputLabelsUnique := by simp [port]
  requiredWork := 0

def process : ProcessKind → Process Label
  | .shareEvidence => shareEvidenceProcess
  | .fundPact => fundPactProcess
  | .settleVerified => settlementProcess 20 4 (by decide) (by decide)
  | .settleExploited => settlementProcess 8 16 (by decide) (by decide)
  | .settleBetrayal => settlementProcess 12 12 (by decide) (by decide)
  | .settleMutualDefection => settlementProcess 4 20 (by decide) (by decide)
  | .settlePareto => paretoSettlementProcess

def schema : MachineSchema where
  ProcessKind := ProcessKind
  Label := Label
  InputQueueKind := QueueKind
  ProcessingQueueKind := QueueKind
  OutputQueueKind := QueueKind
  processKindDecidableEq := inferInstance
  labelDecidableEq := inferInstance
  acceptsInput := fun _ _ => True
  acceptsProcessing := fun _ _ => True
  acceptsOutput := fun _ _ => True
  process := process
  acceptsInputDecidable := fun _ _ => inferInstance
  acceptsProcessingDecidable := fun _ _ => inferInstance
  acceptsOutputDecidable := fun _ _ => inferInstance

inductive Guard
  deriving DecidableEq, Repr

inductive Operation : Phase → Phase → Type where
  | broadcastClaim : Operation .negotiation .negotiation
  | shareEvidence : Operation .negotiation .negotiation
  | fundPact : Operation .negotiation .negotiation
  | closeNegotiation : Operation .negotiation .sealed
  | settleVerified : Operation .sealed .resolved
  | settleExploited : Operation .sealed .resolved
  | settleBetrayal : Operation .sealed .resolved
  | settleMutualDefection : Operation .sealed .resolved
  | settlePareto : Operation .sealed .resolved
  deriving Repr

def evidenceRequirement : PossessionPort Label where
  label := .evidence
  basket := positiveBasket intelligenceSealId 1 (by decide)
  nonempty := by simp [positiveBasket, Basket.singleton]

def defenseRequirement : PossessionPort Label where
  label := .defense
  basket := positiveBasket defenseTokenId 2 (by decide)
  nonempty := by simp [positiveBasket, Basket.singleton]

def evacueeRequirement : PossessionPort Label where
  label := .evacuees
  basket := positiveBasket evacueeId 24 (by decide)
  nonempty := by simp [positiveBasket, Basket.singleton]

def assetRequirement : PossessionPort Label where
  label := .asset
  basket := positiveBasket strategicAssetId 1 (by decide)
  nonempty := by simp [positiveBasket, Basket.singleton]

def operationDefinition {before after : Phase} :
    Operation before after → OperationDefinition schema QueuePort Guard
  | .broadcastClaim =>
      { trigger := .commanded, guards := [], requirements := [],
        processKind := none, effects := [] }
  | .shareEvidence =>
      { trigger := .commanded, guards := [], requirements := [evidenceRequirement],
        processKind := some .shareEvidence, effects := [.executeProcess] }
  | .fundPact =>
      { trigger := .commanded, guards := [], requirements := [defenseRequirement],
        processKind := some .fundPact, effects := [.executeProcess] }
  | .closeNegotiation =>
      { trigger := .commanded, guards := [], requirements := [],
        processKind := none, effects := [] }
  | .settleVerified =>
      { trigger := .reactive, guards := [],
        requirements := [evacueeRequirement, assetRequirement],
        processKind := some .settleVerified, effects := [.executeProcess] }
  | .settleExploited =>
      { trigger := .reactive, guards := [],
        requirements := [evacueeRequirement, assetRequirement],
        processKind := some .settleExploited, effects := [.executeProcess] }
  | .settleBetrayal =>
      { trigger := .reactive, guards := [],
        requirements := [evacueeRequirement, assetRequirement],
        processKind := some .settleBetrayal, effects := [.executeProcess] }
  | .settleMutualDefection =>
      { trigger := .reactive, guards := [],
        requirements := [evacueeRequirement, assetRequirement],
        processKind := some .settleMutualDefection, effects := [.executeProcess] }
  | .settlePareto =>
      { trigger := .reactive, guards := [],
        requirements := [evacueeRequirement, assetRequirement],
        processKind := some .settlePareto, effects := [.executeProcess] }

def language : OperationLanguage schema where
  Mode := Phase
  Operation := Operation
  QueuePort := QueuePort
  Guard := Guard
  modeDecidableEq := inferInstance
  definition := operationDefinition

end Maquina.Games.VeiledAccord
