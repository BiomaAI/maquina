import VeiledAccordSim.Domain

/-!
# Operation Veiled Accord Simulation

A game-owned strategic state executed through Maquina's ordinary deterministic
intent boundary. Cooperation is funded through account transactions; the
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

private def entry (resourceId : ResourceId) (atoms : Nat)
    (positive : 0 < atoms) : BasketEntry where
  resourceId
  quantity := ⟨atoms⟩
  positive

def initialTransaction : AccountTransaction where
  debits := []
  credits :=
    [{ account := commanderAccount,
       entry := entry defenseTokenId 2 (by decide) },
     { account := commanderAccount,
       entry := entry intelligenceSealId 1 (by decide) },
     { account := convoyAccount,
       entry := entry evacueeId 24 (by decide) },
     { account := convoyAccount,
       entry := entry strategicAssetId 1 (by decide) }]
  debitKeysUnique := by decide
  creditKeysUnique := by decide
  directionsDisjoint := by simp

def initialAccounts : WorldState resourceCatalog :=
  match applyAccountTransaction (WorldState.empty resourceCatalog)
      initialTransaction with
  | .ok applied => applied.after
  | .error _ => WorldState.empty resourceCatalog

def openingPromise : ScopedMessage Communication where
  id := 0
  sender := partnerActor
  audience := .broadcast
  payload := { statement := .promiseDefense, verified := false }

structure State where
  accounts : WorldState resourceCatalog
  phase : Phase
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

def initialStateFor (nature : PartnerNature) : State where
  accounts := initialAccounts
  phase := .negotiation
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

def shareEvidenceTransaction : AccountTransaction :=
  AccountTransaction.transfer commanderAccount partnerIntelAccount
    (entry intelligenceSealId 1 (by decide)) (by decide)

def pactEscrowTransaction : AccountTransaction :=
  AccountTransaction.transfer commanderAccount escrowAccount
    (entry defenseTokenId 2 (by decide)) (by decide)

def accord : ResourceBackedAgreement AccordTerms where
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
  escrow := pactEscrowTransaction

private def settlementTransaction
    (saved lost : Nat)
    (savedPositive : 0 < saved)
    (lostPositive : 0 < lost)
    (assetRecipient : AccountId)
    (recipientDifferent : assetRecipient ≠ convoyAccount) : AccountTransaction where
  debits :=
    [{ account := convoyAccount,
       entry := entry evacueeId 24 (by decide) },
     { account := convoyAccount,
       entry := entry strategicAssetId 1 (by decide) }]
  credits :=
    [{ account := sanctuaryAccount,
       entry := entry evacueeId saved savedPositive },
     { account := lossAccount,
       entry := entry evacueeId lost lostPositive },
     { account := assetRecipient,
       entry := entry strategicAssetId 1 (by decide) }]
  debitKeysUnique := by decide
  creditKeysUnique := by
    simp [AccountCredit.key, entry, sanctuaryAccount, lossAccount, evacueeId,
      strategicAssetId]
  directionsDisjoint := by
    have convoyDifferent : convoyAccount ≠ assetRecipient :=
      Ne.symm recipientDifferent
    intro debit debitMem credit creditMem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at debitMem creditMem
    rcases debitMem with rfl | rfl <;>
      rcases creditMem with rfl | rfl | rfl <;>
      simp [AccountDebit.key, AccountCredit.key, entry, convoyAccount,
        sanctuaryAccount, lossAccount, evacueeId, strategicAssetId]
    all_goals exact convoyDifferent

private def fullSettlementTransaction
    (assetRecipient : AccountId)
    (recipientDifferent : assetRecipient ≠ convoyAccount) : AccountTransaction where
  debits :=
    [{ account := convoyAccount,
       entry := entry evacueeId 24 (by decide) },
     { account := convoyAccount,
       entry := entry strategicAssetId 1 (by decide) }]
  credits :=
    [{ account := sanctuaryAccount,
       entry := entry evacueeId 24 (by decide) },
     { account := assetRecipient,
       entry := entry strategicAssetId 1 (by decide) }]
  debitKeysUnique := by decide
  creditKeysUnique := by
    simp [AccountCredit.key, entry, sanctuaryAccount, evacueeId,
      strategicAssetId]
  directionsDisjoint := by
    have convoyDifferent : convoyAccount ≠ assetRecipient :=
      Ne.symm recipientDifferent
    intro debit debitMem credit creditMem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at debitMem creditMem
    rcases debitMem with rfl | rfl <;>
      rcases creditMem with rfl | rfl <;>
      simp [AccountDebit.key, AccountCredit.key, entry, convoyAccount,
        sanctuaryAccount, evacueeId, strategicAssetId]
    all_goals exact convoyDifferent

def verifiedSettlement : AccountTransaction :=
  settlementTransaction 20 4 (by decide) (by decide) authorityAccount (by decide)

def exploitedSettlement : AccountTransaction :=
  settlementTransaction 8 16 (by decide) (by decide) partnerAccount (by decide)

def betrayalSettlement : AccountTransaction :=
  settlementTransaction 12 12 (by decide) (by decide) commanderAccount (by decide)

def mutualDefectionSettlement : AccountTransaction :=
  settlementTransaction 4 20 (by decide) (by decide) contestedAccount (by decide)

def paretoSettlement : AccountTransaction :=
  fullSettlementTransaction authorityAccount (by decide)

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
  | accountRejected (issues : List AccountTransactionIssue)
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

def replayReceipt (receipt : Receipt) (_ : State) : State := receipt.after

private def accepted
    (before after : State)
    (label : String)
    (movements : List Movement := [])
    (revealedOrders : List TacticalOrder := []) :
    Except (List Issue)
      (AppliedIntent State Receipt replayReceipt before) :=
  .ok
    { after
      receipt := { after, label, movements, revealedOrders }
      replayExact := rfl }

private def applyTransaction
    (before : State)
    (transaction : AccountTransaction)
    (update : WorldState resourceCatalog → State)
    (label : String)
    (movements : List Movement)
    (revealedOrders : List TacticalOrder := []) :
    Except (List Issue)
      (AppliedIntent State Receipt replayReceipt before) :=
  match applyAccountTransaction before.accounts transaction with
  | .error issues => .error [.accountRejected issues]
  | .ok applied =>
      accepted before (update applied.after) label movements revealedOrders

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
  transaction : AccountTransaction
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
        { transaction := paretoSettlement
          outcome := .paretoAccord
          saved := 24
          credibility := 100
          commanderUtility := 88
          partnerUtility := 82
          assetRecipient := authorityAccount }
      else
        { transaction := verifiedSettlement
          outcome := .verifiedCooperation
          saved := 20
          credibility := 72
          commanderUtility := 70
          partnerUtility := 68
          assetRecipient := authorityAccount }
  | .escort, .seizeAsset =>
      { transaction := exploitedSettlement
        outcome := .exploitedCooperation
        saved := 8
        credibility := 18
        commanderUtility := 22
        partnerUtility := 86
        assetRecipient := partnerAccount }
  | .seizeAsset, .escort =>
      let outcome := if before.pactFunded then
        MissionOutcome.trustedBetrayal else MissionOutcome.preemptiveBetrayal
      { transaction := betrayalSettlement
        outcome
        saved := 12
        credibility := 0
        commanderUtility := 92
        partnerUtility := 18
        assetRecipient := commanderAccount }
  | .seizeAsset, .seizeAsset =>
      { transaction := mutualDefectionSettlement
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
          accepted before
            { before with
              claimBroadcast := true
              messages := before.messages ++ [message] }
            "broadcast unverified harbor claim"
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
          applyTransaction before shareEvidenceTransaction
            (fun accounts =>
              { before with
                accounts := accounts
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
          applyTransaction before accord.escrow
            (fun accounts =>
              { before with
                accounts := accounts
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
          accepted before
            { before with
                phase := .sealed
                partnerOrder := partnerOrderAfterNegotiation before }
            "seal simultaneous corridor orders"
      else
        .error [.wrongPhase .negotiation before.phase]
  | .reveal commanderOrder =>
      if _phase : before.phase = .sealed then
        let resolution := resolveSettlement before commanderOrder
        let round := closedRound before.partnerOrder commanderOrder
        let lost := 24 - resolution.saved
        applyTransaction before resolution.transaction
          (fun accounts =>
            { before with
              accounts := accounts
              phase := .resolved
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
