import VeiledAccordSim.Domain

/-!
# Operation Veiled Accord Simulation

A game-owned strategic state executed through Maquina's ordinary deterministic
intent boundary. Cooperation is funded through declared Machine Processes; the
partner's sealed order remains hidden from the commander observation until the
joint round resolves.
-/

namespace Maquina.Games.VeiledAccord.Simulation

open Maquina.Games.VeiledAccord

def commanderActor : ActorId := ⟨10⟩
def partnerActor : ActorId := ⟨11⟩
def authorityActor : ActorId := ⟨12⟩
def outsiderActor : ActorId := ⟨13⟩

def commanderAccount : AccountId := ⟨20000⟩
def partnerAccount : AccountId := ⟨20001⟩
def escrowAccount : AccountId := ⟨20002⟩
def partnerIntelAccount : AccountId := ⟨20003⟩
def convoyAccount : AccountId := ⟨20004⟩
def sanctuaryAccount : AccountId := ⟨20005⟩
def lossAccount : AccountId := ⟨20006⟩
def authorityAccount : AccountId := ⟨20007⟩
def contestedAccount : AccountId := ⟨20008⟩
def accordMachineAccount : AccountId := ⟨20009⟩

private def entry (resourceId : ResourceId) (atoms : Nat)
    (positive : 0 < atoms) : BasketEntry where
  resourceId
  quantity := ⟨atoms⟩
  positive

def initialGenesis : GenesisPlan where
  grants :=
    [{ account := commanderAccount,
       entry := entry defenseTokenId 2 (by decide) },
     { account := commanderAccount,
       entry := entry intelligenceSealId 1 (by decide) },
     { account := convoyAccount,
       entry := entry evacueeId 24 (by decide) },
     { account := convoyAccount,
       entry := entry strategicAssetId 1 (by decide) },
     { account := accordMachineAccount,
       entry := entry accordBodyId 1 (by decide) }]
  keysUnique := by decide

def initialAccounts : WorldState resourceCatalog :=
  match applyGenesis resourceCatalog initialGenesis with
  | .ok applied => applied.after
  | .error _ => WorldState.empty resourceCatalog

def openingPromise : ScopedMessage Communication where
  id := 0
  sender := partnerActor
  audience := .broadcast
  payload := { statement := .promiseDefense, verified := false }

def accordMachine : Machine schema := Machine.empty accordMachineAccount 0 accordBodyId

def initialRuntime : MachineRuntime schema language where
  mode := .negotiation
  machine := accordMachine
  custody := MachineCustody.empty accordMachineAccount
  activeCustodyHeld := Machine.activeDependenciesSatisfy_empty
    accordMachineAccount 0 accordBodyId _
  nextProcessId := 0

def guardEvaluator : GuardEvaluator resourceCatalog schema language where
  condition := fun guard _ => nomatch guard
  issues := fun guard _ => nomatch guard
  evidence := fun guard _ => nomatch guard
  issuesEmptyIff := by
    intro guard
    nomatch guard

structure State where
  accounts : WorldState resourceCatalog
  runtime : MachineRuntime schema language
  runtimeBacked : MachineCustody.Backed accounts runtime.custody
  partnerNature : PartnerNature
  partnerOrder : TacticalOrder
  claimBroadcast : Bool
  evidenceShared : Bool
  pactFunded : Bool
  messages : List (ScopedMessage Communication)
  outcome : MissionOutcome
  civiliansSaved : Nat
  credibility : Nat
  commanderUtility : Nat
  partnerUtility : Nat

def State.phase (state : State) : Phase := state.runtime.mode

def initialStateFor (nature : PartnerNature) : State where
  accounts := initialAccounts
  runtime := initialRuntime
  runtimeBacked := MachineCustody.backed_empty initialAccounts accordMachineAccount
  partnerNature := nature
  partnerOrder := .seizeAsset
  claimBroadcast := false
  evidenceShared := false
  pactFunded := false
  messages := [openingPromise]
  outcome := .active
  civiliansSaved := 0
  credibility := 50
  commanderUtility := 0
  partnerUtility := 0

def initialState : State := initialStateFor .opportunist

def accord : ResourceBackedAgreement AccordTerms
    (Operation .negotiation .negotiation) where
  agreement :=
    { id := 1
      parties := [commanderActor, partnerActor]
      partiesNonempty := by decide
      partiesUnique := by decide
      terms := { route := .harbor, defenseTokens := 2, mutualEscort := true } }
  ratified :=
    { approvals := [commanderActor, partnerActor]
      approvalsUnique := by decide
      approvedExactly := by intro actor; rfl }
  backing := .fundPact

def possessionBindings : PossessionBindings Label where
  resolve
    | .evidence | .defense => commanderAccount
    | .evacuees | .asset => convoyAccount
    | .saved => sanctuaryAccount
    | .lost => lossAccount
    | .assetRecipient => authorityAccount

def processBindings (assetRecipient : AccountId) : ProcessBindings Label where
  source
    | .evidence | .defense => commanderAccount
    | .evacuees | .asset => convoyAccount
    | .saved => sanctuaryAccount
    | .lost => lossAccount
    | .assetRecipient => assetRecipient
  custody := fun _ => accordMachineAccount
  output
    | .evidence => some partnerIntelAccount
    | .defense => some escrowAccount
    | .saved => some sanctuaryAccount
    | .lost => some lossAccount
    | .assetRecipient => some assetRecipient
    | .evacuees | .asset => none

def queueBindings : QueueBindings QueuePort where
  resolve := fun {_} port => nomatch port

def custodyBindings : CustodyBindings Label where
  resolve := fun _ => none

def recipientBindings : RecipientBindings Label where
  resolve := fun _ => none

def proposal
    {before after : Phase}
    (operation : Operation before after)
    (assetRecipient : AccountId := authorityAccount) :
    OperationProposal schema language where
  before := before
  after := after
  operation := operation
  possessionBindings := possessionBindings
  custodyBindings := custodyBindings
  processBindings := some (processBindings assetRecipient)
  queueBindings := queueBindings
  recipientBindings := recipientBindings

inductive Intent where
  | broadcastClaim
  | shareEvidence
  | fundPact
  | inspectPartnerOrder
  | closeNegotiation
  | reveal (order : TacticalOrder)
  deriving DecidableEq, Repr

inductive Issue where
  | wrongPhase (expected actual : Phase)
  | duplicateClaim
  | evidenceAlreadyShared
  | pactAlreadyFunded
  | sealedOrderHidden
  | noNegotiatedTerms
  | operationRejected (issues : List SimulatorIssue)
  deriving DecidableEq, Repr

structure Movement where
  source : AccountId
  destination : AccountId
  resource : ResourceId
  quantity : Nat
  deriving DecidableEq, Repr

structure Receipt where
  after : State
  label : String
  movements : List Movement
  revealedOrders : List TacticalOrder := []
  operationChecks : List OperationCheckReceipt := []
  operationEffects : List SimulatorEffectReceipt := []

def replayReceipt (receipt : Receipt) (_ : State) : State := receipt.after

private def accepted
    (before after : State)
    (label : String)
    (movements : List Movement := [])
    (revealedOrders : List TacticalOrder := [])
    (operationChecks : List OperationCheckReceipt := [])
    (operationEffects : List SimulatorEffectReceipt := []) :
    Except (List Issue)
      (AppliedIntent State Receipt replayReceipt before) :=
  .ok
    { after
      receipt :=
        { after, label, movements, revealedOrders, operationChecks,
          operationEffects }
      replayExact := rfl }

private def applyMachineOperation
    (before : State)
    (operationProposal : OperationProposal schema language)
    (update : ∀ (accounts : WorldState resourceCatalog)
        (runtime : MachineRuntime schema language),
      MachineCustody.Backed accounts runtime.custody → State)
    (label : String)
    (movements : List Movement)
    (revealedOrders : List TacticalOrder := []) :
    Except (List Issue)
      (AppliedIntent State Receipt replayReceipt before) :=
  match applyRuntimeOperation guardEvaluator before.accounts before.runtime
      before.runtimeBacked operationProposal with
  | .error issues => .error [.operationRejected issues]
  | .ok applied =>
      accepted before
        (update applied.afterWorld applied.afterRuntime applied.afterCustodyBacked)
        label movements revealedOrders applied.receipt.checks applied.receipt.effects

def tacticalCommit : TacticalOrder → CommitmentToken
  | .escort => ⟨9100⟩
  | .seizeAsset => ⟨9200⟩

def closedRound
    (partnerOrder commanderOrder : TacticalOrder) :
    ClosedSealedRound TacticalOrder tacticalCommit where
  reveals :=
    [{ sealed :=
         { id := ⟨500⟩
           actor := commanderActor
           arbitration := ⟨10, 0⟩
           token := tacticalCommit commanderOrder }
       payload := commanderOrder
       binding := rfl },
     { sealed :=
         { id := ⟨501⟩
           actor := partnerActor
           arbitration := ⟨10, 1⟩
           token := tacticalCommit partnerOrder }
       payload := partnerOrder
       binding := rfl }]
  idsUnique := by simp
  actorsUnique := by simp [commanderActor, partnerActor]

private def partnerOrderAfterNegotiation (state : State) : TacticalOrder :=
  if state.pactFunded || state.evidenceShared then .escort else .seizeAsset

private structure SettlementPlan where
  operation : Operation .sealed .resolved
  outcome : MissionOutcome
  saved : Nat
  credibility : Nat
  commanderUtility : Nat
  partnerUtility : Nat
  assetRecipient : AccountId

private def resolveSettlement
    (before : State)
    (commanderOrder : TacticalOrder) : SettlementPlan :=
  match commanderOrder, before.partnerOrder with
  | .escort, .escort =>
      if before.pactFunded then
        { operation := .settlePareto
          outcome := .paretoAccord
          saved := 24
          credibility := 100
          commanderUtility := 88
          partnerUtility := 82
          assetRecipient := authorityAccount }
      else
        { operation := .settleVerified
          outcome := .verifiedCooperation
          saved := 20
          credibility := 72
          commanderUtility := 70
          partnerUtility := 68
          assetRecipient := authorityAccount }
  | .escort, .seizeAsset =>
      { operation := .settleExploited
        outcome := .exploitedCooperation
        saved := 8
        credibility := 18
        commanderUtility := 22
        partnerUtility := 86
        assetRecipient := partnerAccount }
  | .seizeAsset, .escort =>
      let outcome := if before.pactFunded then
        MissionOutcome.trustedBetrayal else MissionOutcome.preemptiveBetrayal
      { operation := .settleBetrayal
        outcome
        saved := 12
        credibility := 0
        commanderUtility := 92
        partnerUtility := 18
        assetRecipient := commanderAccount }
  | .seizeAsset, .seizeAsset =>
      { operation := .settleMutualDefection
        outcome := .mutualDefection
        saved := 4
        credibility := 0
        commanderUtility := 34
        partnerUtility := 34
        assetRecipient := contestedAccount }

def applyIntent
    (before : State)
    (intent : Intent) :
    Except (List Issue) (AppliedIntent State Receipt replayReceipt before) :=
  match intent with
  | .broadcastClaim =>
      if _phase : before.phase = .negotiation then
        if _duplicate : before.claimBroadcast then
          .error [.duplicateClaim]
        else
          let message : ScopedMessage Communication :=
            { id := 1
              sender := commanderActor
              audience := .broadcast
              payload := { statement := .claimHarborSafe, verified := false } }
          applyMachineOperation before (proposal .broadcastClaim)
            (fun accounts runtime backed =>
              { before with
                accounts := accounts
                runtime := runtime
                runtimeBacked := backed
                claimBroadcast := true
                messages := before.messages ++ [message] })
            "broadcast unverified harbor claim" []
      else
        .error [.wrongPhase .negotiation before.phase]
  | .shareEvidence =>
      if _phase : before.phase = .negotiation then
        if _duplicate : before.evidenceShared then
          .error [.evidenceAlreadyShared]
        else
          let message : ScopedMessage Communication :=
            { id := 2
              sender := commanderActor
              audience := .coalition [commanderActor, partnerActor]
              payload := { statement := .verifiedRidgeThreat, verified := true } }
          applyMachineOperation before (proposal .shareEvidence)
            (fun accounts runtime backed =>
              { before with
                accounts := accounts
                runtime := runtime
                runtimeBacked := backed
                evidenceShared := true
                messages := before.messages ++ [message] })
            "share verified ridge-threat evidence"
            [{ source := commanderAccount
               destination := partnerIntelAccount
               resource := intelligenceSealId
               quantity := 1 }]
      else
        .error [.wrongPhase .negotiation before.phase]
  | .fundPact =>
      if _phase : before.phase = .negotiation then
        if _duplicate : before.pactFunded then
          .error [.pactAlreadyFunded]
        else
          let message : ScopedMessage Communication :=
            { id := 3
              sender := authorityActor
              audience := .broadcast
              payload := { statement := .accordRatified, verified := true } }
          applyMachineOperation before (proposal accord.backing)
            (fun accounts runtime backed =>
              { before with
                accounts := accounts
                runtime := runtime
                runtimeBacked := backed
                pactFunded := true
                messages := before.messages ++ [message] })
            "fund mutual-defense escrow"
            [{ source := commanderAccount
               destination := escrowAccount
               resource := defenseTokenId
               quantity := 2 }]
      else
        .error [.wrongPhase .negotiation before.phase]
  | .inspectPartnerOrder =>
      .error [.sealedOrderHidden]
  | .closeNegotiation =>
      if _phase : before.phase = .negotiation then
        if _noTerms : !before.claimBroadcast && !before.evidenceShared && !before.pactFunded then
          .error [.noNegotiatedTerms]
        else
          applyMachineOperation before (proposal .closeNegotiation)
            (fun accounts runtime backed =>
              { before with
                accounts := accounts
                runtime := runtime
                runtimeBacked := backed
                partnerOrder := partnerOrderAfterNegotiation before })
            "seal simultaneous corridor orders" []
      else
        .error [.wrongPhase .negotiation before.phase]
  | .reveal commanderOrder =>
      if _phase : before.phase = .sealed then
        let resolution := resolveSettlement before commanderOrder
        let round := closedRound before.partnerOrder commanderOrder
        let lost := 24 - resolution.saved
        applyMachineOperation before
          (proposal resolution.operation resolution.assetRecipient)
          (fun accounts runtime backed =>
            { before with
              accounts := accounts
              runtime := runtime
              runtimeBacked := backed
              outcome := resolution.outcome
              civiliansSaved := resolution.saved
              credibility := resolution.credibility
              commanderUtility := resolution.commanderUtility
              partnerUtility := resolution.partnerUtility })
          "reveal and resolve sealed orders"
          ([{ source := convoyAccount
              destination := sanctuaryAccount
              resource := evacueeId
              quantity := resolution.saved },
            { source := convoyAccount
              destination := resolution.assetRecipient
              resource := strategicAssetId
              quantity := 1 }] ++
            if lost = 0 then [] else
              [{ source := convoyAccount
                 destination := lossAccount
                 resource := evacueeId
                 quantity := lost }])
          (round.reveals.map fun reveal => reveal.payload)
      else
        .error [.wrongPhase .sealed before.phase]

def executor : IntentExecutor State Intent Issue Receipt where
  replay := replayReceipt
  apply := applyIntent

def initialTimeline : TimelineState State Intent where
  tick := ⟨0⟩
  application := initialState
  pending := []
  pendingIdsUnique := by simp
  nextEventSequence := 0

end Maquina.Games.VeiledAccord.Simulation
