import NightglassSim.Simulation
import MaquinaViz

/-!
# Operation Nightglass Showcase Adapter

Nightglass owns the heterogeneous mission composition and declarative visual
vocabulary. The shared projector sees only application states and transitions.
-/

namespace Maquina.Games.Nightglass.Showcase

open Maquina.Games.Nightglass
open Simulation Visualization

def radarModeName : Radar.Mode → String
  | .ready => "radar-ready"
  | .scanning => "radar-scanning"
  | .tracking => "radar-tracking"

def batteryModeName : Battery.Mode → String
  | .ready => "battery-ready"
  | .tracking => "battery-tracking"
  | .engaged => "battery-engaged"
  | .damaged => "battery-damaged"

def convoyModeName : Convoy.Mode → String
  | .staging => "convoy-staging"
  | .routeOne => "convoy-route-one"
  | .routeTwo => "convoy-route-two"
  | .damaged => "convoy-damaged"
  | .extracted => "convoy-extracted"

def radarOperationName {before after : Radar.Mode} :
    Radar.Operation before after → String
  | .beginScan => "begin scan"
  | .detectContact => "detect contact"
  | .clearTrack => "clear track"

def batteryOperationName {before after : Battery.Mode} :
    Battery.Operation before after → String
  | .acquireChannel => "acquire targeting channel"
  | .launch => "launch interceptor"
  | .completeIntercept => "complete interception"
  | .sufferDamage => "suffer damage"
  | .repair => "repair battery"

def convoyOperationName {before after : Convoy.Mode} :
    Convoy.Operation before after → String
  | .enterRouteOne => "enter route one"
  | .enterRouteTwo => "enter route two"
  | .strike => "hostile strike"
  | .repair => "repair convoy"
  | .extract => "reach extraction"

def processKindName : ProcessKind → String
  | .idle => "idle"

def queueKindName : QueueKind → String
  | .mission => "mission"

def radarProjection : Visualization.Projection schema Radar.language where
  machineId := "machine:nightglass:radar"
  modeName := radarModeName
  operationName := radarOperationName
  processKindName := processKindName
  inputQueueKindName := queueKindName
  processingQueueKindName := queueKindName
  outputQueueKindName := queueKindName

def alphaProjection : Visualization.Projection schema Battery.language where
  machineId := "machine:nightglass:alpha"
  modeName := batteryModeName
  operationName := batteryOperationName
  processKindName := processKindName
  inputQueueKindName := queueKindName
  processingQueueKindName := queueKindName
  outputQueueKindName := queueKindName

def bravoProjection : Visualization.Projection schema Battery.language where
  machineId := "machine:nightglass:bravo"
  modeName := batteryModeName
  operationName := batteryOperationName
  processKindName := processKindName
  inputQueueKindName := queueKindName
  processingQueueKindName := queueKindName
  outputQueueKindName := queueKindName

def convoyProjection : Visualization.Projection schema Convoy.language where
  machineId := "machine:nightglass:convoy"
  modeName := convoyModeName
  operationName := convoyOperationName
  processKindName := processKindName
  inputQueueKindName := queueKindName
  processingQueueKindName := queueKindName
  outputQueueKindName := queueKindName

private def position (x y z : Float) : Vec3 := { x, y, z }

def presentation : PresentationView where
  theme :=
    { background := "#070b13"
      surface := "#101722"
      accent := "#63d7ff" }
  resources :=
    [{ id := resourceKey targetingChannelId
       label := "Targeting channel"
       symbol := "T"
       color := "#63d7ff"
       geometry := "octahedron" },
     { id := resourceKey interceptorAmmoId
       label := "Interceptor"
       symbol := "I"
       color := "#ffb34d"
       geometry := "cylinder" },
     { id := resourceKey sparePartsId
       label := "Spare parts"
       symbol := "S"
       color := "#65d59a"
       geometry := "cube" },
     { id := resourceKey evacueeId
       label := "Evacuees"
       symbol := "E"
       color := "#e9eef5"
       geometry := "sphere" }]
  accounts :=
    [{ id := accountKey commandAccount
       label := "Command uplink"
       kind := "command"
       color := "#63d7ff"
       position := position 0 0 (-7.5) },
     { id := accountKey arsenalAccount
       label := "Interceptor magazine"
       kind := "arsenal"
       color := "#ffb34d"
       position := position (-11.5) 0 (-1.5) },
     { id := accountKey repairAccount
       label := "Repair depot"
       kind := "repair"
       color := "#65d59a"
       position := position 9 0 1.5 },
     { id := accountKey radarAccount
       label := "Radar inventory"
       kind := "machine-inventory"
       color := "#63d7ff"
       position := position (-7) 0 (-3) },
     { id := accountKey alphaBatteryAccount
       label := "Alpha inventory"
       kind := "machine-inventory"
       color := "#ffb34d"
       position := position (-3) 0 2.5 },
     { id := accountKey bravoBatteryAccount
       label := "Bravo inventory"
       kind := "machine-inventory"
       color := "#ff7c66"
       position := position 4 0 2.5 },
     { id := accountKey convoyAccount
       label := "Convoy manifest"
       kind := "machine-inventory"
       color := "#e9eef5"
       position := position (-8) 0 7 }]
  machines :=
    [{ id := radarProjection.machineId
       label := "Nightglass radar"
       color := "#63d7ff"
       position := position (-7) 0 (-3)
       geometry := "radar"
       modes :=
         [{ mode := "radar-scanning", activity := some "scanning" },
          { mode := "radar-tracking", activity := some "tracking" }] },
     { id := alphaProjection.machineId
       label := "Battery Alpha"
       color := "#ffb34d"
       position := position (-3) 0 2.5
       geometry := "battery"
       modes :=
         [{ mode := "battery-tracking", activity := some "tracking" },
          { mode := "battery-engaged", activity := some "engaged" },
          { mode := "battery-damaged", activity := some "damaged" }] },
     { id := bravoProjection.machineId
       label := "Battery Bravo"
       color := "#ff7c66"
       position := position 4 0 2.5
       geometry := "battery"
       modes :=
         [{ mode := "battery-tracking", activity := some "tracking" },
          { mode := "battery-engaged", activity := some "engaged" },
          { mode := "battery-damaged", activity := some "damaged" }] },
     { id := convoyProjection.machineId
       label := "Evacuation convoy"
       color := "#e9eef5"
       position := position (-8) 0 7
       geometry := "convoy"
       modes :=
         [{ mode := "convoy-staging", position := some (position (-8) 0 7) },
          { mode := "convoy-route-one"
            position := some (position (-2) 0 7)
            activity := some "moving" },
          { mode := "convoy-route-two"
            position := some (position 4 0 7)
            activity := some "moving" },
          { mode := "convoy-damaged"
            position := some (position (-2) 0 7)
            activity := some "damaged" },
          { mode := "convoy-extracted"
            position := some (position 9 0 7)
            activity := some "extracted" }] }]
  camera :=
    { position := position 19 22 29
      target := position 0 0 1.5 }

def projectMissionState
    (timeline : TimelineState Simulation.State Intent) : StateView :=
  let state := timeline.application
  let radar := projectState radarProjection
    (state.radar.toState state.accounts state.radarBacked)
  let alpha := projectState alphaProjection
    (state.alpha.toState state.accounts state.alphaBacked)
  let bravo := projectState bravoProjection
    (state.bravo.toState state.accounts state.bravoBacked)
  let convoy := projectState convoyProjection
    (state.convoy.toState state.accounts state.convoyBacked)
  { holdings := radar.holdings
    machines := radar.machines ++ alpha.machines ++ bravo.machines ++ convoy.machines
    custody := radar.custody ++ alpha.custody ++ bravo.custody ++ convoy.custody
    nextProcessId := exactNat (max (max state.radar.nextProcessId state.alpha.nextProcessId)
      (max state.bravo.nextProcessId state.convoy.nextProcessId))
    logicalTick := some (exactNat timeline.tick.value)
    pendingIntents := some (exactNat timeline.pending.length) }

def componentMachineId : Component → String
  | .radar => radarProjection.machineId
  | .alphaBattery => alphaProjection.machineId
  | .bravoBattery => bravoProjection.machineId
  | .convoy => convoyProjection.machineId

def componentName : Component → String
  | .radar => "radar"
  | .alphaBattery => "Battery Alpha"
  | .bravoBattery => "Battery Bravo"
  | .convoy => "convoy"

def intentName : Intent → String
  | .radar proposal => radarOperationName proposal.operation
  | .alphaBattery proposal _ _ =>
      s!"Battery Alpha: {batteryOperationName proposal.operation}"
  | .bravoBattery proposal _ _ =>
      s!"Battery Bravo: {batteryOperationName proposal.operation}"
  | .convoy proposal _ => convoyOperationName proposal.operation

private def accountIssueView : AccountTransactionIssue → IssueView
  | issue@(.debitRejected _ _ _ _) =>
      { code := "account-debit-rejected", detail := reprStr issue }
  | issue@(.creditRejected _ _ _ _) =>
      { code := "account-credit-rejected", detail := reprStr issue }

private def policyIssueView : PolicyIssue → IssueView
  | issue@(.contactNotTracked _) =>
      { code := "contact-not-tracked", detail := reprStr issue }

def issueViews : Issue → List IssueView
  | .operationRejected component issues => issues.map fun issue =>
      let view := issueView issue
      { view with detail := s!"{componentName component}: {view.detail}" }
  | .policyRejected component issues => issues.map fun issue =>
      let view := policyIssueView issue
      { view with detail := s!"{componentName component}: {view.detail}" }
  | .accountRejected issues => issues.map accountIssueView
  | .protectedInventoryTouched component account =>
      [{ code := "protected-inventory-touched"
         detail := s!"{reprStr component} touched protected account {account.value}" }]

def rejectedIssueChecks : Issue → List CheckView
  | .operationRejected _ issues => issues.flatMap rejectedCheckViews
  | .policyRejected _ issues =>
      [{ kind := "game-policy"
         condition := "contact-tracked"
         status := "rejected"
         detail := "the game-owned radar component is not tracking a contact"
         issues := issues.map policyIssueView }]
  | .accountRejected issues =>
      issues.map fun issue =>
        { kind := "account-transaction"
          condition := "atomic-account-transaction"
          status := "rejected"
          detail := "an account transaction leg was rejected; no successor was exposed"
          issues := [accountIssueView issue] }
  | .protectedInventoryTouched _ _ => []

private def worldEffectView
    (machineId : String) : WorldEffectReceipt → EffectView
  | .transfer receipt => effectView machineId (.transfer receipt)
  | .transformation receipt => effectView machineId (.transformation receipt)

private def rejectionName : IntentRejectionKind → String
  | .invalidAtSnapshot => "snapshot eligibility"
  | .lostConflict => "canonical conflict arbitration"

def scheduledIntentName
    (processed : List (ScheduledIntent Intent))
    (event : TimelineEvent Issue Receipt) : String :=
  match processed.find? fun intent => intent.id.value == event.intentId.value with
  | some intent => intentName intent.payload
  | none => s!"intent {event.intentId.value}"

def eventChecks
    (processed : List (ScheduledIntent Intent))
    (event : TimelineEvent Issue Receipt) : List CheckView :=
  let label := scheduledIntentName processed event
  match event.outcome with
  | .accepted receipt =>
      { kind := "scheduler"
        condition := label
        status := "accepted"
        detail := s!"{label} committed at event sequence {event.sequence}" } ::
        receipt.policyEvidence.map (fun evidence =>
          { kind := "game-policy"
            condition := evidence.condition
            status := "accepted"
            detail := evidence.detail }) ++
        receipt.operationChecks.map acceptedCheckView
  | .rejected kind issues =>
      { kind := "scheduler"
        condition := label
        status := "rejected"
        detail := s!"{label} rejected by {rejectionName kind}" } ::
        issues.flatMap rejectedIssueChecks

def eventEffects (event : TimelineEvent Issue Receipt) : List EffectView :=
  match event.outcome with
  | .accepted receipt =>
      let machineId := componentMachineId receipt.component
      receipt.operationEffects.map (effectView machineId) ++
        receipt.transactionEffects.map (worldEffectView machineId)
  | .rejected _ _ => []

def eventIssues (event : TimelineEvent Issue Receipt) : List IssueView :=
  match event.outcome with
  | .accepted _ => []
  | .rejected _ issues => issues.flatMap issueViews

def eventAccepted (event : TimelineEvent Issue Receipt) : Bool :=
  match event.outcome with
  | .accepted _ => true
  | .rejected _ _ => false

def eventRejected (event : TimelineEvent Issue Receipt) : Bool :=
  !eventAccepted event

def tickStatus (events : List (TimelineEvent Issue Receipt)) : String :=
  if events.any eventAccepted && events.any eventRejected then "mixed"
  else if events.any eventRejected then "rejected"
  else "accepted"

def applyMissionTick
    (before : TimelineState Simulation.State Intent)
    (_ : Unit) : ApplicationStepResult (TimelineState Simulation.State Intent) :=
  let applied := applyTick executor before
  let operation :=
    match applied.processed.map fun intent => intentName intent.payload with
    | [name] => name
    | names => s!"resolve {names.length} scheduled intents"
  { after := applied.after
    operation
    trigger := "scheduled"
    status := tickStatus applied.events
    semanticStatus := "lean-proved-tick-replay"
    logicalTick := some (exactNat before.tick.value)
    eventSequences := applied.events.map fun event => exactNat event.sequence
    intentIds := applied.events.map fun event => exactNat event.intentId.value
    checks := applied.events.flatMap (eventChecks applied.processed)
    effects := applied.events.flatMap eventEffects
    issues := applied.events.flatMap eventIssues }

def provenance : ProvenanceView where
  engine := leanProvenance.engine
  toolchain := leanProvenance.toolchain
  guarantees := leanProvenance.guarantees ++
    ["logical ticks are independent of wall-clock time",
     "same-tick intents resolve in one canonical total order",
     "snapshot-invalid and conflict-losing intents do not mutate state",
     "immutable accepted events replay the complete heterogeneous game state",
     "mission vocabulary and component composition remain game-owned"]

def mission :
    Visualization.ApplicationScenario
      (TimelineState Simulation.State Intent) Unit where
  id := "nightglass-extraction"
  gameId := "nightglass"
  title := "Operation Nightglass"
  summary :=
    "Two interceptor batteries contend for one targeting channel while an evacuation convoy survives a deterministic strike and repair."
  initial := initialTimeline
  program := [(), (), (), (), (), (), (), (), ()]
  presentation := presentation
  provenance := provenance
  projectState := projectMissionState
  applyIntent := applyMissionTick

def artifact : ScenarioArtifact := projectApplicationScenario mission

end Maquina.Games.Nightglass.Showcase
