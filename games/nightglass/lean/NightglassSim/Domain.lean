import Maquina

/-!
# Operation Nightglass Domain

Fictional mission vocabulary owned entirely by Nightglass. Radar, battery,
convoy, targeting, damage, and extraction concepts never enter Maquina core.
-/

namespace Maquina.Games.Nightglass

inductive Label where
  | command
  | equipment
  | arsenal
  | repairDepot
  | evacuees
  deriving DecidableEq, Repr

inductive ProcessKind where
  | idle
  deriving DecidableEq, Repr

inductive QueueKind where
  | mission
  deriving DecidableEq, Repr

/-- Nightglass machines in this mission do not expose queues. -/
inductive QueuePort : QueueStage → Type

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
  process := fun _ => Process.empty 1
  acceptsInputDecidable := fun _ _ => inferInstance
  acceptsProcessingDecidable := fun _ _ => inferInstance
  acceptsOutputDecidable := fun _ _ => inferInstance

inductive Guard where
  | missionAuthorized
  | routeClear
  deriving DecidableEq, Repr

def targetingChannelId : ResourceId := ⟨700⟩
def interceptorAmmoId : ResourceId := ⟨701⟩
def sparePartsId : ResourceId := ⟨702⟩
def evacueeId : ResourceId := ⟨703⟩

def targetingChannelSpec : ResourceSpec :=
  ResourceSpec.unique { id := targetingChannelId, name := "targeting channel" }

def interceptorAmmoSpec : ResourceSpec :=
  ResourceSpec.discrete { id := interceptorAmmoId, name := "interceptor ammunition" }

def sparePartsSpec : ResourceSpec :=
  ResourceSpec.discrete { id := sparePartsId, name := "spare parts" }

def evacueeSpec : ResourceSpec :=
  ResourceSpec.edition { id := evacueeId, name := "evacuees" }
    24 (by decide)

def resourceCatalog : ResourceCatalog :=
  ResourceCatalog.ofList
    [targetingChannelSpec, interceptorAmmoSpec, sparePartsSpec, evacueeSpec]

def targetingChannel : Basket :=
  Basket.singleton targetingChannelId .one (by decide)

def oneInterceptor : Basket :=
  Basket.singleton interceptorAmmoId .one (by decide)

def oneSparePart : Basket :=
  Basket.singleton sparePartsId .one (by decide)

def channelPresence : PossessionPort Label where
  label := .equipment
  basket := targetingChannel
  nonempty := by simp [targetingChannel, Basket.singleton]

def ammoPresence : PossessionPort Label where
  label := .arsenal
  basket := oneInterceptor
  nonempty := by simp [oneInterceptor, Basket.singleton]

def repairPresence : PossessionPort Label where
  label := .repairDepot
  basket := oneSparePart
  nonempty := by simp [oneSparePart, Basket.singleton]

namespace Radar

inductive Mode where
  | ready
  | scanning
  | tracking
  deriving DecidableEq, Repr

inductive Operation : Mode → Mode → Type where
  | beginScan : Operation .ready .scanning
  | detectContact : Operation .scanning .tracking
  | clearTrack : Operation .tracking .ready
  deriving Repr

def definition {before after : Mode} :
    Operation before after → OperationDefinition schema QueuePort Guard
  | .beginScan =>
      { trigger := .scheduled
        guards := [.missionAuthorized]
        requirements := []
        processKind := none
        effects := [] }
  | .detectContact =>
      { trigger := .reactive
        guards := [.missionAuthorized]
        requirements := []
        processKind := none
        effects := [] }
  | .clearTrack =>
      { trigger := .reactive
        guards := []
        requirements := []
        processKind := none
        effects := [] }

def language : OperationLanguage schema where
  Mode := Mode
  Operation := Operation
  QueuePort := QueuePort
  Guard := Guard
  modeDecidableEq := inferInstance
  definition := definition

end Radar

namespace Battery

inductive Mode where
  | ready
  | tracking
  | engaged
  | damaged
  deriving DecidableEq, Repr

inductive Operation : Mode → Mode → Type where
  | acquireChannel : Operation .ready .tracking
  | launch : Operation .tracking .engaged
  | completeIntercept : Operation .engaged .ready
  | sufferDamage : Operation .ready .damaged
  | repair : Operation .damaged .ready
  deriving Repr

def definition {before after : Mode} :
    Operation before after → OperationDefinition schema QueuePort Guard
  | .acquireChannel =>
      { trigger := .commanded
        guards := [.missionAuthorized]
        requirements := []
        processKind := none
        effects := [.openCustody .command targetingChannel] }
  | .launch =>
      { trigger := .commanded
        guards := [.missionAuthorized]
        requirements := [channelPresence, ammoPresence]
        processKind := none
        effects := [] }
  | .completeIntercept =>
      { trigger := .reactive
        guards := []
        requirements := []
        processKind := none
        effects := [.closeCustody .equipment] }
  | .sufferDamage =>
      { trigger := .scheduled
        guards := []
        requirements := []
        processKind := none
        effects := [] }
  | .repair =>
      { trigger := .commanded
        guards := [.missionAuthorized]
        requirements := [repairPresence]
        processKind := none
        effects := [] }

def language : OperationLanguage schema where
  Mode := Mode
  Operation := Operation
  QueuePort := QueuePort
  Guard := Guard
  modeDecidableEq := inferInstance
  definition := definition

end Battery

namespace Convoy

inductive Mode where
  | staging
  | routeOne
  | routeTwo
  | damaged
  | extracted
  deriving DecidableEq, Repr

inductive Operation : Mode → Mode → Type where
  | enterRouteOne : Operation .staging .routeOne
  | enterRouteTwo : Operation .routeOne .routeTwo
  | strike : Operation .routeOne .damaged
  | repair : Operation .damaged .routeOne
  | extract : Operation .routeTwo .extracted
  deriving Repr

def definition {before after : Mode} :
    Operation before after → OperationDefinition schema QueuePort Guard
  | .enterRouteOne =>
      { trigger := .commanded
        guards := [.routeClear]
        requirements := []
        processKind := none
        effects := [] }
  | .enterRouteTwo =>
      { trigger := .commanded
        guards := [.routeClear]
        requirements := []
        processKind := none
        effects := [] }
  | .strike =>
      { trigger := .scheduled
        guards := []
        requirements := []
        processKind := none
        effects := [] }
  | .repair =>
      { trigger := .commanded
        guards := [.missionAuthorized]
        requirements := [repairPresence]
        processKind := none
        effects := [] }
  | .extract =>
      { trigger := .commanded
        guards := [.routeClear]
        requirements := []
        processKind := none
        effects := [] }

def language : OperationLanguage schema where
  Mode := Mode
  Operation := Operation
  QueuePort := QueuePort
  Guard := Guard
  modeDecidableEq := inferInstance
  definition := definition

end Convoy

end Maquina.Games.Nightglass
