import Maquina.Game

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
  | launch
  | repair
  deriving DecidableEq, Repr

inductive QueueKind where
  | mission
  deriving DecidableEq, Repr

/-- Nightglass machines in this mission do not expose queues. -/
inductive QueuePort : QueueStage → Type

inductive Guard where
  | missionAuthorized
  | routeClear
  deriving DecidableEq, Repr

def targetingChannelId : ResourceId := ⟨700⟩
def interceptorAmmoId : ResourceId := ⟨701⟩
def sparePartsId : ResourceId := ⟨702⟩
def evacueeId : ResourceId := ⟨703⟩
def radarBodyId : ResourceId := ⟨704⟩
def alphaBodyId : ResourceId := ⟨705⟩
def bravoBodyId : ResourceId := ⟨706⟩
def convoyBodyId : ResourceId := ⟨707⟩

def targetingChannelSpec : ResourceSpec :=
  ResourceSpec.unique { id := targetingChannelId, name := "targeting channel" }

def interceptorAmmoSpec : ResourceSpec :=
  ResourceSpec.discrete { id := interceptorAmmoId, name := "interceptor ammunition" }

def sparePartsSpec : ResourceSpec :=
  ResourceSpec.discrete { id := sparePartsId, name := "spare parts" }

def evacueeSpec : ResourceSpec :=
  ResourceSpec.edition { id := evacueeId, name := "evacuees" }
    24 (by decide)

def radarBodySpec : ResourceSpec :=
  ResourceSpec.unique { id := radarBodyId, name := "radar Body" }
def alphaBodySpec : ResourceSpec :=
  ResourceSpec.unique { id := alphaBodyId, name := "battery Alpha Body" }
def bravoBodySpec : ResourceSpec :=
  ResourceSpec.unique { id := bravoBodyId, name := "battery Bravo Body" }
def convoyBodySpec : ResourceSpec :=
  ResourceSpec.unique { id := convoyBodyId, name := "convoy Body" }

def resourceCatalog : ResourceCatalog :=
  ResourceCatalog.ofList
    [targetingChannelSpec, interceptorAmmoSpec, sparePartsSpec, evacueeSpec,
      radarBodySpec, alphaBodySpec, bravoBodySpec, convoyBodySpec]

def targetingChannel : Basket :=
  Basket.singleton targetingChannelId .one (by decide)

def oneInterceptor : Basket :=
  Basket.singleton interceptorAmmoId .one (by decide)

def oneSparePart : Basket :=
  Basket.singleton sparePartsId .one (by decide)

def consumedPort (label : Label) (basket : Basket)
    (nonempty : basket.entries ≠ []) : ProcessPort Label where
  label := label
  basket := basket
  nonempty := nonempty

def launchProcess : Process Label where
  consumed := [consumedPort .arsenal oneInterceptor (by
    simp [oneInterceptor, Basket.singleton])]
  reserved := []
  activeCustody := []
  outputs := []
  consumedLabelsUnique := by simp
  reservedLabelsUnique := by simp
  activeCustodyLabelsUnique := by simp
  outputLabelsUnique := by simp
  requiredWork := 0

def repairProcess : Process Label where
  consumed := [consumedPort .repairDepot oneSparePart (by
    simp [oneSparePart, Basket.singleton])]
  reserved := []
  activeCustody := []
  outputs := []
  consumedLabelsUnique := by simp
  reservedLabelsUnique := by simp
  activeCustodyLabelsUnique := by simp
  outputLabelsUnique := by simp
  requiredWork := 0

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
  process
    | .idle => Process.empty 1
    | .launch => launchProcess
    | .repair => repairProcess
  acceptsInputDecidable := fun _ _ => inferInstance
  acceptsProcessingDecidable := fun _ _ => inferInstance
  acceptsOutputDecidable := fun _ _ => inferInstance

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
        processKind := some .launch
        effects := [.executeProcess] }
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
        processKind := some .repair
        effects := [.executeProcess] }

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
  | aborted
  deriving DecidableEq, Repr

inductive Operation : Mode → Mode → Type where
  | enterRouteOne : Operation .staging .routeOne
  | enterRouteTwo : Operation .routeOne .routeTwo
  | strike : Operation .routeOne .damaged
  | repair : Operation .damaged .routeOne
  | extract : Operation .routeTwo .extracted
  | abortStaging : Operation .staging .aborted
  | abortRouteOne : Operation .routeOne .aborted
  | abortDamaged : Operation .damaged .aborted
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
        processKind := some .repair
        effects := [.executeProcess] }
  | .extract =>
      { trigger := .commanded
        guards := [.routeClear]
        requirements := []
        processKind := none
        effects := [] }
  | .abortStaging | .abortRouteOne | .abortDamaged =>
      { trigger := .commanded
        guards := [.missionAuthorized]
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
