import NightglassSim.Domain

/-!
# Operation Nightglass Simulation

A game-owned heterogeneous mission state scheduled by Maquina's generic
timeline. The mission demonstrates snapshot eligibility, deterministic
same-tick conflicts, complete-state event replay, damage, repair, and extraction.
-/

namespace Maquina.Games.Nightglass.Simulation

open Maquina.Games.Nightglass

def commandAccount : AccountId := ⟨10000⟩
def arsenalAccount : AccountId := ⟨10001⟩
def repairAccount : AccountId := ⟨10002⟩
def radarAccount : AccountId := ⟨11000⟩
def alphaBatteryAccount : AccountId := ⟨11001⟩
def bravoBatteryAccount : AccountId := ⟨11002⟩
def convoyAccount : AccountId := ⟨11003⟩

def initialTransaction : AccountTransaction where
  debits := []
  credits :=
    [{ account := commandAccount,
       entry := { resourceId := targetingChannelId, quantity := .one, positive := by decide } },
     { account := arsenalAccount,
       entry := { resourceId := interceptorAmmoId, quantity := ⟨4⟩, positive := by decide } },
     { account := repairAccount,
       entry := { resourceId := sparePartsId, quantity := ⟨2⟩, positive := by decide } },
     { account := convoyAccount,
       entry := { resourceId := evacueeId, quantity := ⟨24⟩, positive := by decide } }]
  debitKeysUnique := by decide
  creditKeysUnique := by decide
  directionsDisjoint := by simp

def initialAccounts : WorldState resourceCatalog :=
  match applyAccountTransaction (WorldState.empty resourceCatalog)
      initialTransaction with
  | .ok applied => applied.after
  | .error _ => WorldState.empty resourceCatalog

def emptyRuntime
    (language : OperationLanguage schema)
    (inventory : AccountId)
    (mode : language.Mode) : MachineRuntime schema language where
  mode := mode
  machine := Machine.empty inventory 0
  custody := MachineCustody.empty inventory
  activeCustodyHeld := Machine.activeDependenciesSatisfy_empty inventory 0 _
  nextProcessId := 0

structure State where
  accounts : WorldState resourceCatalog
  radar : MachineRuntime schema Radar.language
  alpha : MachineRuntime schema Battery.language
  bravo : MachineRuntime schema Battery.language
  convoy : MachineRuntime schema Convoy.language
  radarBacked : MachineCustody.Backed accounts radar.custody
  alphaBacked : MachineCustody.Backed accounts alpha.custody
  bravoBacked : MachineCustody.Backed accounts bravo.custody
  convoyBacked : MachineCustody.Backed accounts convoy.custody

def initialState : State where
  accounts := initialAccounts
  radar := emptyRuntime Radar.language radarAccount .ready
  alpha := emptyRuntime Battery.language alphaBatteryAccount .ready
  bravo := emptyRuntime Battery.language bravoBatteryAccount .ready
  convoy := emptyRuntime Convoy.language convoyAccount .staging
  radarBacked := MachineCustody.backed_empty initialAccounts radarAccount
  alphaBacked := MachineCustody.backed_empty initialAccounts alphaBatteryAccount
  bravoBacked := MachineCustody.backed_empty initialAccounts bravoBatteryAccount
  convoyBacked := MachineCustody.backed_empty initialAccounts convoyAccount

def guardCondition
    (_ : Guard)
    (_ : SimulatorState resourceCatalog schema language) : Prop := True

def guardIssues
    (_ : Guard)
    (_ : SimulatorState resourceCatalog schema language) : List GuardIssue := []

def guardEvidence
    (guard : Guard)
    (_ : SimulatorState resourceCatalog schema language) : GuardEvidence :=
  match guard with
  | .missionAuthorized =>
      { condition := "mission-authorized"
        detail := "mission command authorizes the operation" }
  | .routeClear =>
      { condition := "route-clear"
        detail := "the selected route is clear at assessment time" }

theorem guardIssues_empty_iff
    (guard : Guard)
    (state : SimulatorState resourceCatalog schema language) :
    guardIssues guard state = [] ↔ guardCondition guard state := by
  simp [guardIssues, guardCondition]

def radarGuardEvaluator :
    GuardEvaluator resourceCatalog schema Radar.language where
  condition := guardCondition
  issues := guardIssues
  evidence := guardEvidence
  issuesEmptyIff := guardIssues_empty_iff

def batteryGuardEvaluator :
    GuardEvaluator resourceCatalog schema Battery.language where
  condition := guardCondition
  issues := guardIssues
  evidence := guardEvidence
  issuesEmptyIff := guardIssues_empty_iff

def convoyGuardEvaluator :
    GuardEvaluator resourceCatalog schema Convoy.language where
  condition := guardCondition
  issues := guardIssues
  evidence := guardEvidence
  issuesEmptyIff := guardIssues_empty_iff

def queueBindings : QueueBindings QueuePort where
  resolve := fun {_} port => nomatch port

def recipientBindings : RecipientBindings Label where
  resolve := fun _ => none

def noCustodyBindings : CustodyBindings Label where
  resolve := fun _ => none

def channelCustodyBindings : CustodyBindings Label where
  resolve
    | .equipment => some 0
    | _ => none

def possessionBindingsFor (equipment : AccountId) : PossessionBindings Label where
  resolve
    | .command => commandAccount
    | .equipment => equipment
    | .arsenal => arsenalAccount
    | .repairDepot => repairAccount
    | .evacuees => convoyAccount

def radarProposal
    {before after : Radar.Mode}
    (operation : Radar.Operation before after) :
    OperationProposal schema Radar.language where
  before := before
  after := after
  operation := operation
  possessionBindings := possessionBindingsFor radarAccount
  custodyBindings := noCustodyBindings
  processBindings := none
  queueBindings := queueBindings
  recipientBindings := recipientBindings

def batteryProposal
    (account : AccountId)
    {before after : Battery.Mode}
    (operation : Battery.Operation before after)
    (custodyBindings : CustodyBindings Label := noCustodyBindings) :
    OperationProposal schema Battery.language where
  before := before
  after := after
  operation := operation
  possessionBindings := possessionBindingsFor account
  custodyBindings := custodyBindings
  processBindings := none
  queueBindings := queueBindings
  recipientBindings := recipientBindings

def convoyProposal
    {before after : Convoy.Mode}
    (operation : Convoy.Operation before after) :
    OperationProposal schema Convoy.language where
  before := before
  after := after
  operation := operation
  possessionBindings := possessionBindingsFor convoyAccount
  custodyBindings := noCustodyBindings
  processBindings := none
  queueBindings := queueBindings
  recipientBindings := recipientBindings

inductive Component where
  | radar
  | alphaBattery
  | bravoBattery
  | convoy
  deriving DecidableEq, Repr

inductive PolicyRequirement where
  | radarTracking
  deriving DecidableEq, Repr

inductive Intent where
  | radar (proposal : OperationProposal schema Radar.language)
  | alphaBattery
      (proposal : OperationProposal schema Battery.language)
      (cost : Option AccountTransaction := none)
      (policies : List PolicyRequirement := [])
  | bravoBattery
      (proposal : OperationProposal schema Battery.language)
      (cost : Option AccountTransaction := none)
      (policies : List PolicyRequirement := [])
  | convoy
      (proposal : OperationProposal schema Convoy.language)
      (cost : Option AccountTransaction := none)

inductive PolicyIssue where
  | contactNotTracked (actual : Radar.Mode)
  deriving DecidableEq, Repr

structure PolicyEvidence where
  condition : String
  detail : String
  deriving DecidableEq, Repr

inductive Issue where
  | operationRejected (component : Component) (issues : List SimulatorIssue)
  | policyRejected (component : Component) (issues : List PolicyIssue)
  | accountRejected (issues : List AccountTransactionIssue)
  | protectedInventoryTouched (component : Component) (account : AccountId)
  deriving DecidableEq, Repr

structure Transition where
  after : State
  component : Component
  policyEvidence : List PolicyEvidence
  operationChecks : List OperationCheckReceipt
  operationEffects : List SimulatorEffectReceipt
  transactionEffects : List WorldEffectReceipt

structure Receipt where
  after : State
  component : Component
  policyEvidence : List PolicyEvidence
  operationChecks : List OperationCheckReceipt
  operationEffects : List SimulatorEffectReceipt
  transactionEffects : List WorldEffectReceipt

def replayReceipt (receipt : Receipt) (_ : State) : State := receipt.after

def assessPolicies
    (before : State)
    (policies : List PolicyRequirement) :
    Except (List PolicyIssue) (List PolicyEvidence) :=
  match policies with
  | [] => .ok []
  | .radarTracking :: rest =>
      match Radar.language.modeDecidableEq before.radar.mode .tracking with
      | .isTrue _ =>
        match assessPolicies before rest with
        | .error issues => .error issues
        | .ok evidence =>
            .ok
              ({ condition := "contact-tracked"
                 detail := "the game-owned radar component is tracking a contact" } ::
                evidence)
      | .isFalse _ =>
        .error [.contactNotTracked before.radar.mode]

private structure RebasedBacking
    {language : OperationLanguage schema}
    (after : WorldState resourceCatalog)
    (runtime : MachineRuntime schema language) : Type where
  proof : MachineCustody.Backed after runtime.custody

private def rebaseBacking?
    {language : OperationLanguage schema}
    {before after : WorldState resourceCatalog}
    (runtime : MachineRuntime schema language)
    (backed : MachineCustody.Backed before runtime.custody)
    (receipts : List WorldEffectReceipt)
    (replayExact :
      replayWorldEffectReceipts receipts before.holdings = after.holdings) :
    Option (RebasedBacking after runtime) :=
  if untouched : worldEffectsLeaveAccountUntouched receipts
      runtime.machine.inventory = true then
    some ⟨backed.replayWorldEffects_untouched receipts replayExact
      (worldEffectsLeaveAccountUntouched_each receipts
        runtime.machine.inventory untouched)⟩
  else none

private def updateRadar
    (before : State)
    (applied : AppliedRuntimeOperation before.accounts before.radar proposal) :
    Except (List Issue) State :=
  match rebaseBacking? before.alpha before.alphaBacked applied.worldEffects
      applied.worldReplayExact,
    rebaseBacking? before.bravo before.bravoBacked applied.worldEffects
      applied.worldReplayExact,
    rebaseBacking? before.convoy before.convoyBacked applied.worldEffects
      applied.worldReplayExact with
  | some alphaWitness, some bravoWitness, some convoyWitness =>
      .ok
        { accounts := applied.afterWorld
          radar := applied.afterRuntime
          alpha := before.alpha
          bravo := before.bravo
          convoy := before.convoy
          radarBacked := applied.afterCustodyBacked
          alphaBacked := alphaWitness.proof
          bravoBacked := bravoWitness.proof
          convoyBacked := convoyWitness.proof }
  | none, _, _ =>
      .error [.protectedInventoryTouched .alphaBattery
        before.alpha.machine.inventory]
  | _, none, _ =>
      .error [.protectedInventoryTouched .bravoBattery
        before.bravo.machine.inventory]
  | _, _, none =>
      .error [.protectedInventoryTouched .convoy before.convoy.machine.inventory]

private def updateAlpha
    (before : State)
    (applied : AppliedRuntimeOperation before.accounts before.alpha proposal) :
    Except (List Issue) State :=
  match rebaseBacking? before.radar before.radarBacked applied.worldEffects
      applied.worldReplayExact,
    rebaseBacking? before.bravo before.bravoBacked applied.worldEffects
      applied.worldReplayExact,
    rebaseBacking? before.convoy before.convoyBacked applied.worldEffects
      applied.worldReplayExact with
  | some radarWitness, some bravoWitness, some convoyWitness =>
      .ok
        { accounts := applied.afterWorld
          radar := before.radar
          alpha := applied.afterRuntime
          bravo := before.bravo
          convoy := before.convoy
          radarBacked := radarWitness.proof
          alphaBacked := applied.afterCustodyBacked
          bravoBacked := bravoWitness.proof
          convoyBacked := convoyWitness.proof }
  | none, _, _ =>
      .error [.protectedInventoryTouched .radar before.radar.machine.inventory]
  | _, none, _ =>
      .error [.protectedInventoryTouched .bravoBattery
        before.bravo.machine.inventory]
  | _, _, none =>
      .error [.protectedInventoryTouched .convoy before.convoy.machine.inventory]

private def updateBravo
    (before : State)
    (applied : AppliedRuntimeOperation before.accounts before.bravo proposal) :
    Except (List Issue) State :=
  match rebaseBacking? before.radar before.radarBacked applied.worldEffects
      applied.worldReplayExact,
    rebaseBacking? before.alpha before.alphaBacked applied.worldEffects
      applied.worldReplayExact,
    rebaseBacking? before.convoy before.convoyBacked applied.worldEffects
      applied.worldReplayExact with
  | some radarWitness, some alphaWitness, some convoyWitness =>
      .ok
        { accounts := applied.afterWorld
          radar := before.radar
          alpha := before.alpha
          bravo := applied.afterRuntime
          convoy := before.convoy
          radarBacked := radarWitness.proof
          alphaBacked := alphaWitness.proof
          bravoBacked := applied.afterCustodyBacked
          convoyBacked := convoyWitness.proof }
  | none, _, _ =>
      .error [.protectedInventoryTouched .radar before.radar.machine.inventory]
  | _, none, _ =>
      .error [.protectedInventoryTouched .alphaBattery
        before.alpha.machine.inventory]
  | _, _, none =>
      .error [.protectedInventoryTouched .convoy before.convoy.machine.inventory]

private def updateConvoy
    (before : State)
    (applied : AppliedRuntimeOperation before.accounts before.convoy proposal) :
    Except (List Issue) State :=
  match rebaseBacking? before.radar before.radarBacked applied.worldEffects
      applied.worldReplayExact,
    rebaseBacking? before.alpha before.alphaBacked applied.worldEffects
      applied.worldReplayExact,
    rebaseBacking? before.bravo before.bravoBacked applied.worldEffects
      applied.worldReplayExact with
  | some radarWitness, some alphaWitness, some bravoWitness =>
      .ok
        { accounts := applied.afterWorld
          radar := before.radar
          alpha := before.alpha
          bravo := before.bravo
          convoy := applied.afterRuntime
          radarBacked := radarWitness.proof
          alphaBacked := alphaWitness.proof
          bravoBacked := bravoWitness.proof
          convoyBacked := applied.afterCustodyBacked }
  | none, _, _ =>
      .error [.protectedInventoryTouched .radar before.radar.machine.inventory]
  | _, none, _ =>
      .error [.protectedInventoryTouched .alphaBattery
        before.alpha.machine.inventory]
  | _, _, none =>
      .error [.protectedInventoryTouched .bravoBattery
        before.bravo.machine.inventory]

private def applyCost
    (before : State)
    (transaction : AccountTransaction) :
    Except (List Issue) (State × List WorldEffectReceipt) :=
  match applyAccountTransaction before.accounts transaction with
  | .error issues => .error [.accountRejected issues]
  | .ok applied =>
      let effects := applied.receipts.map WorldEffectReceipt.transformation
      have replayExact :
          replayWorldEffectReceipts effects before.accounts.holdings =
            applied.after.holdings := by
        rw [replayWorldEffectReceipts_transformations]
        exact applied.replayExact
      match rebaseBacking? before.radar before.radarBacked effects replayExact,
        rebaseBacking? before.alpha before.alphaBacked effects replayExact,
        rebaseBacking? before.bravo before.bravoBacked effects replayExact,
        rebaseBacking? before.convoy before.convoyBacked effects replayExact with
      | some radarWitness, some alphaWitness, some bravoWitness, some convoyWitness =>
          .ok
            ({ before with
                accounts := applied.after
                radarBacked := radarWitness.proof
                alphaBacked := alphaWitness.proof
                bravoBacked := bravoWitness.proof
                convoyBacked := convoyWitness.proof }, effects)
      | none, _, _, _ =>
          .error [.protectedInventoryTouched .radar before.radar.machine.inventory]
      | _, none, _, _ =>
          .error [.protectedInventoryTouched .alphaBattery
            before.alpha.machine.inventory]
      | _, _, none, _ =>
          .error [.protectedInventoryTouched .bravoBattery
            before.bravo.machine.inventory]
      | _, _, _, none =>
          .error [.protectedInventoryTouched .convoy before.convoy.machine.inventory]

def ammoCost : AccountTransaction :=
  AccountTransaction.debit arsenalAccount
    { resourceId := interceptorAmmoId, quantity := .one, positive := by decide }

def repairCost : AccountTransaction :=
  AccountTransaction.debit repairAccount
    { resourceId := sparePartsId, quantity := .one, positive := by decide }

private def applyRadarIntent
    (before : State)
    (proposal : OperationProposal schema Radar.language) :
    Except (List Issue) Transition :=
  match applyRuntimeOperation radarGuardEvaluator before.accounts
      before.radar before.radarBacked proposal with
  | .error issues => .error [.operationRejected .radar issues]
  | .ok applied =>
      match updateRadar before applied with
      | .error issues => .error issues
      | .ok after =>
          .ok
            { after
              component := .radar
              policyEvidence := []
              operationChecks := applied.receipt.checks
              operationEffects := applied.receipt.effects
              transactionEffects := [] }

private def applyAlphaIntent
    (before : State)
    (proposal : OperationProposal schema Battery.language)
    (cost : Option AccountTransaction)
    (policies : List PolicyRequirement) :
    Except (List Issue) Transition :=
  match assessPolicies before policies with
  | .error issues => .error [.policyRejected .alphaBattery issues]
  | .ok policyEvidence =>
    match applyRuntimeOperation batteryGuardEvaluator before.accounts
        before.alpha before.alphaBacked proposal with
    | .error issues => .error [.operationRejected .alphaBattery issues]
    | .ok applied =>
      match updateAlpha before applied with
      | .error issues => .error issues
      | .ok intermediate =>
          match cost with
          | none =>
              .ok
                { after := intermediate
                  component := .alphaBattery
                  policyEvidence
                  operationChecks := applied.receipt.checks
                  operationEffects := applied.receipt.effects
                  transactionEffects := [] }
          | some transaction =>
              match applyCost intermediate transaction with
              | .error issues => .error issues
              | .ok (after, costs) =>
                  .ok
                    { after
                      component := .alphaBattery
                      policyEvidence
                      operationChecks := applied.receipt.checks
                      operationEffects := applied.receipt.effects
                      transactionEffects := costs }

private def applyBravoIntent
    (before : State)
    (proposal : OperationProposal schema Battery.language)
    (cost : Option AccountTransaction)
    (policies : List PolicyRequirement) :
    Except (List Issue) Transition :=
  match assessPolicies before policies with
  | .error issues => .error [.policyRejected .bravoBattery issues]
  | .ok policyEvidence =>
    match applyRuntimeOperation batteryGuardEvaluator before.accounts
        before.bravo before.bravoBacked proposal with
    | .error issues => .error [.operationRejected .bravoBattery issues]
    | .ok applied =>
      match updateBravo before applied with
      | .error issues => .error issues
      | .ok intermediate =>
          match cost with
          | none =>
              .ok
                { after := intermediate
                  component := .bravoBattery
                  policyEvidence
                  operationChecks := applied.receipt.checks
                  operationEffects := applied.receipt.effects
                  transactionEffects := [] }
          | some transaction =>
              match applyCost intermediate transaction with
              | .error issues => .error issues
              | .ok (after, costs) =>
                  .ok
                    { after
                      component := .bravoBattery
                      policyEvidence
                      operationChecks := applied.receipt.checks
                      operationEffects := applied.receipt.effects
                      transactionEffects := costs }

private def applyConvoyIntent
    (before : State)
    (proposal : OperationProposal schema Convoy.language)
    (cost : Option AccountTransaction) :
    Except (List Issue) Transition :=
  match applyRuntimeOperation convoyGuardEvaluator before.accounts
      before.convoy before.convoyBacked proposal with
  | .error issues => .error [.operationRejected .convoy issues]
  | .ok applied =>
      match updateConvoy before applied with
      | .error issues => .error issues
      | .ok intermediate =>
          match cost with
          | some transaction =>
            match applyCost intermediate transaction with
            | .error issues => .error issues
            | .ok (after, costs) =>
                .ok
                  { after
                    component := .convoy
                    policyEvidence := []
                    operationChecks := applied.receipt.checks
                    operationEffects := applied.receipt.effects
                    transactionEffects := costs }
          | none =>
            .ok
              { after := intermediate
                component := .convoy
                policyEvidence := []
                operationChecks := applied.receipt.checks
                operationEffects := applied.receipt.effects
                transactionEffects := [] }

def applyIntent
    (before : State)
    (intent : Intent) :
    Except (List Issue) (AppliedIntent State Receipt replayReceipt before) :=
  let result :=
    match intent with
    | .radar proposal => applyRadarIntent before proposal
    | .alphaBattery proposal cost policies =>
        applyAlphaIntent before proposal cost policies
    | .bravoBattery proposal cost policies =>
        applyBravoIntent before proposal cost policies
    | .convoy proposal cost => applyConvoyIntent before proposal cost
  match result with
  | .error issues => .error issues
  | .ok transition =>
      let receipt : Receipt :=
          { after := transition.after
            component := transition.component
            policyEvidence := transition.policyEvidence
            operationChecks := transition.operationChecks
            operationEffects := transition.operationEffects
            transactionEffects := transition.transactionEffects }
      .ok
        { after := transition.after
          receipt
          replayExact := rfl }

def executor : IntentExecutor State Intent Issue Receipt where
  replay := replayReceipt
  apply := applyIntent

def beginScan : Intent := .radar (radarProposal Radar.Operation.beginScan)
def detectContact : Intent := .radar (radarProposal Radar.Operation.detectContact)
def clearTrack : Intent := .radar (radarProposal Radar.Operation.clearTrack)

def acquireAlpha : Intent :=
  .alphaBattery (batteryProposal alphaBatteryAccount Battery.Operation.acquireChannel)
    none [.radarTracking]
def acquireBravo : Intent :=
  .bravoBattery (batteryProposal bravoBatteryAccount Battery.Operation.acquireChannel)
    none [.radarTracking]
def launchAlpha : Intent :=
  .alphaBattery (batteryProposal alphaBatteryAccount Battery.Operation.launch)
    (some ammoCost)
def launchBravo : Intent :=
  .bravoBattery (batteryProposal bravoBatteryAccount Battery.Operation.launch)
    (some ammoCost)
def completeAlpha : Intent :=
  .alphaBattery (batteryProposal alphaBatteryAccount
    Battery.Operation.completeIntercept channelCustodyBindings) none
def completeBravo : Intent :=
  .bravoBattery (batteryProposal bravoBatteryAccount
    Battery.Operation.completeIntercept channelCustodyBindings) none

def enterRouteOne : Intent :=
  .convoy (convoyProposal Convoy.Operation.enterRouteOne) none
def enterRouteTwo : Intent :=
  .convoy (convoyProposal Convoy.Operation.enterRouteTwo) none
def strikeConvoy : Intent := .convoy (convoyProposal Convoy.Operation.strike) none
def repairConvoy : Intent :=
  .convoy (convoyProposal Convoy.Operation.repair) (some repairCost)
def extractConvoy : Intent := .convoy (convoyProposal Convoy.Operation.extract) none
def abortStaging : Intent :=
  .convoy (convoyProposal Convoy.Operation.abortStaging) none
def abortRouteOne : Intent :=
  .convoy (convoyProposal Convoy.Operation.abortRouteOne) none
def abortDamaged : Intent :=
  .convoy (convoyProposal Convoy.Operation.abortDamaged) none

def scheduled
    (id executeAt major minor : Nat)
    (payload : Intent) : ScheduledIntent Intent where
  id := ⟨id⟩
  submittedAt := ⟨0⟩
  executeAt := ⟨executeAt⟩
  notBeforeSubmission := Nat.zero_le executeAt
  arbitration := ⟨major, minor⟩
  payload := payload

def missionIntents : List (ScheduledIntent Intent) :=
  [scheduled 0 0 10 0 beginScan,
   scheduled 1 1 10 0 detectContact,
   scheduled 2 2 20 0 acquireAlpha,
   scheduled 3 2 20 1 acquireBravo,
   scheduled 4 3 10 0 launchAlpha,
   scheduled 5 3 20 0 enterRouteOne,
   scheduled 6 4 10 0 strikeConvoy,
   scheduled 7 4 20 0 enterRouteTwo,
   scheduled 8 4 30 0 completeAlpha,
   scheduled 9 5 10 0 repairConvoy,
   scheduled 10 6 10 0 enterRouteTwo,
   scheduled 11 6 20 0 acquireBravo,
   scheduled 12 7 10 0 launchBravo,
   scheduled 13 7 20 0 extractConvoy,
   scheduled 14 7 30 0 clearTrack,
   scheduled 15 8 10 0 completeBravo]

def initialTimeline : TimelineState State Intent where
  tick := ⟨0⟩
  application := initialState
  pending := missionIntents
  pendingIdsUnique := by native_decide
  nextEventSequence := 0

def tickZero := applyTick executor initialTimeline
def tickOne := applyTick executor tickZero.after
def tickTwo := applyTick executor tickOne.after
def tickThree := applyTick executor tickTwo.after
def tickFour := applyTick executor tickThree.after
def tickFive := applyTick executor tickFour.after
def tickSix := applyTick executor tickFive.after
def tickSeven := applyTick executor tickSix.after
def tickEight := applyTick executor tickSeven.after

def finalTimeline : TimelineState State Intent := tickEight.after

inductive MissionStatus where
  | active
  | victory
  | defeat
  deriving DecidableEq, Repr

def convoyMode (state : State) : Convoy.Mode := state.convoy.mode

def missionStatus (state : TimelineState State Intent) : MissionStatus :=
  if convoyMode state.application = .extracted then .victory
  else if convoyMode state.application = .aborted then .defeat
  else if state.tick.value ≥ 90 then .defeat
  else .active

def acceptedEventCount (events : List (TimelineEvent Issue Receipt)) : Nat :=
  events.countP fun event =>
    match event.outcome with
    | .accepted _ => true
    | .rejected _ _ => false

def conflictEventCount (events : List (TimelineEvent Issue Receipt)) : Nat :=
  events.countP fun event =>
    match event.outcome with
    | .rejected .lostConflict _ => true
    | _ => false

def allEvents : List (TimelineEvent Issue Receipt) :=
  tickZero.events ++ tickOne.events ++ tickTwo.events ++ tickThree.events ++
    tickFour.events ++ tickFive.events ++ tickSix.events ++ tickSeven.events ++
    tickEight.events

def damageRun := applyIntent tickThree.after.application strikeConvoy

def prematureAcquireIssues : Option (List Issue) :=
  match applyIntent tickZero.after.application acquireAlpha with
  | .error issues => some issues
  | .ok _ => none

def damagedState? : Option State :=
  match damageRun with
  | .ok applied => some applied.after
  | .error _ => none

def repairedState? : Option State :=
  match damagedState? with
  | some state =>
      match applyIntent state repairConvoy with
      | .ok applied => some applied.after
      | .error _ => none
  | none => none

def repairedSpareBalance? : Option Nat :=
  repairedState?.map fun state =>
    (state.accounts.balance repairAccount sparePartsId).atoms

def defeatTimeline : TimelineState State Intent :=
  { initialTimeline with tick := ⟨90⟩ }

example : tickTwo.events.length = 2 := by native_decide
example : conflictEventCount tickTwo.events = 1 := by native_decide
example : conflictEventCount tickFour.events = 1 := by native_decide
example : convoyMode tickFour.after.application = .damaged := by native_decide
example : convoyMode tickFive.after.application = .routeOne := by native_decide
example : missionStatus finalTimeline = .victory := by native_decide
example : missionStatus initialTimeline = .active := by native_decide
example : missionStatus defeatTimeline = .defeat := by native_decide
example : finalTimeline.tick.value = 9 := by native_decide
example : finalTimeline.pending = [] := by native_decide
example :
    (finalTimeline.application.accounts.balance arsenalAccount
      interceptorAmmoId).atoms = 2 := by native_decide
example :
    (finalTimeline.application.accounts.balance commandAccount
      targetingChannelId).atoms = 1 := by native_decide
example :
    (finalTimeline.application.accounts.balance repairAccount
      sparePartsId).atoms = 1 := by native_decide

def alphaContender := scheduled 2 2 20 0 acquireAlpha
def bravoContender := scheduled 3 2 20 1 acquireBravo

example :
    (orderScheduledIntents [bravoContender, alphaContender]).map
        (fun intent => intent.id.value) = [2, 3] := by
  native_decide

example : damagedState?.map convoyMode = some .damaged := by native_decide
example : repairedState?.map convoyMode = some .routeOne := by native_decide
example : repairedSpareBalance? = some 1 := by native_decide
example : prematureAcquireIssues =
    some [.policyRejected .alphaBattery [.contactNotTracked .scanning]] := by
  native_decide

example :
    replayTimelineEvents executor allEvents initialState =
      finalTimeline.application := by
  unfold allEvents
  rw [replayTimelineEvents_append, replayTimelineEvents_append,
    replayTimelineEvents_append, replayTimelineEvents_append,
    replayTimelineEvents_append, replayTimelineEvents_append,
    replayTimelineEvents_append, replayTimelineEvents_append]
  change replayTimelineEvents executor tickEight.events
      (replayTimelineEvents executor tickSeven.events
        (replayTimelineEvents executor tickSix.events
          (replayTimelineEvents executor tickFive.events
            (replayTimelineEvents executor tickFour.events
              (replayTimelineEvents executor tickThree.events
                (replayTimelineEvents executor tickTwo.events
                  (replayTimelineEvents executor tickOne.events
                    (replayTimelineEvents executor tickZero.events
                      initialTimeline.application)))))))) =
    tickEight.after.application
  rw [tickZero.replayExact, tickOne.replayExact, tickTwo.replayExact,
    tickThree.replayExact, tickFour.replayExact, tickFive.replayExact,
    tickSix.replayExact, tickSeven.replayExact, tickEight.replayExact]

end Maquina.Games.Nightglass.Simulation
