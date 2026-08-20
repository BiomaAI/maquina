import VeiledAccordSim.Simulation

/-!
# Operation Veiled Accord Command Graph

A bounded extensive-form game with an imperfect-information decision point.
The browser receives actor-safe candidate surfaces and proof-backed immutable
resolutions; it never evaluates Veiled Accord rules.
-/

namespace Maquina.Games.VeiledAccord.Command

open Maquina.Games.VeiledAccord Simulation

abbrev Snapshot := TimelineSnapshot executor initialState

def root : Snapshot where
  id := ⟨0⟩
  timeline := initialTimeline
  history := []
  replayExact := rfl

def candidate (id : Nat) (payload : Intent) : CommandCandidate Intent where
  id := ⟨id⟩
  actor := commanderActor
  payload

def order
    (id major minor : Nat)
    (actor : ActorId)
    (payload : Intent) : CommandOrder Intent where
  id := ⟨id⟩
  actor
  arbitration := ⟨major, minor⟩
  payload

def claimCandidate := candidate 100 .broadcastClaim
def evidenceCandidate := candidate 101 .shareEvidence
def pactCandidate := candidate 102 .fundPact
def inspectPartnerCandidate := candidate 103 .inspectPartnerOrder
def escortCandidate := candidate 200 (.reveal .escort)
def seizeCandidate := candidate 201 (.reveal .seizeAsset)

def claimSet : OrderSet Intent where
  orders := [order 100 10 0 commanderActor .broadcastClaim]
  idsUnique := by decide

def evidenceSet : OrderSet Intent where
  orders := [order 101 10 0 commanderActor .shareEvidence]
  idsUnique := by decide

def accordSet : OrderSet Intent where
  orders :=
    [order 101 10 0 commanderActor .shareEvidence,
     order 102 20 0 commanderActor .fundPact]
  idsUnique := by decide

def closeSet (id : Nat) : OrderSet Intent where
  orders := [order id 10 0 authorityActor .closeNegotiation]
  idsUnique := by simp

def escortSet : OrderSet Intent where
  orders := [order 200 10 0 commanderActor (.reveal .escort)]
  idsUnique := by decide

def seizeSet : OrderSet Intent where
  orders := [order 201 10 0 commanderActor (.reveal .seizeAsset)]
  idsUnique := by decide

def claimApplied :=
  resolveSnapshotOrderSet executor initialState root ⟨100⟩ rfl claimSet
def claimClosed :=
  resolveSnapshotOrderSet executor initialState claimApplied.child ⟨1⟩ rfl
    (closeSet 900)
def claimNodeSnapshot : Snapshot := claimClosed.child

def evidenceApplied :=
  resolveSnapshotOrderSet executor initialState root ⟨101⟩ rfl evidenceSet
def evidenceClosed :=
  resolveSnapshotOrderSet executor initialState evidenceApplied.child ⟨2⟩ rfl
    (closeSet 901)
def evidenceNodeSnapshot : Snapshot := evidenceClosed.child

def accordApplied :=
  resolveSnapshotOrderSet executor initialState root ⟨102⟩ rfl accordSet
def accordClosed :=
  resolveSnapshotOrderSet executor initialState accordApplied.child ⟨3⟩ rfl
    (closeSet 902)
def accordNodeSnapshot : Snapshot := accordClosed.child

def claimEscort :=
  resolveSnapshotOrderSet executor initialState claimNodeSnapshot ⟨10⟩ rfl escortSet
def claimSeize :=
  resolveSnapshotOrderSet executor initialState claimNodeSnapshot ⟨11⟩ rfl seizeSet
def evidenceEscort :=
  resolveSnapshotOrderSet executor initialState evidenceNodeSnapshot ⟨12⟩ rfl escortSet
def evidenceSeize :=
  resolveSnapshotOrderSet executor initialState evidenceNodeSnapshot ⟨13⟩ rfl seizeSet
def accordEscort :=
  resolveSnapshotOrderSet executor initialState accordNodeSnapshot ⟨14⟩ rfl escortSet
def accordSeize :=
  resolveSnapshotOrderSet executor initialState accordNodeSnapshot ⟨15⟩ rfl seizeSet

/-! ## Actor observation, no-leak surface, and information sets -/

structure CommanderObservation where
  phase : Phase
  claimBroadcast : Bool
  evidenceShared : Bool
  pactFunded : Bool
  visibleMessages : List (ScopedMessage Communication)
  defenseTokens : Nat
  evidenceSeals : Nat
  evacueesInTransit : Nat
  outcome : MissionOutcome
  civiliansSaved : Nat
  credibility : Nat
  commanderUtility : Nat
  partnerUtility : Nat
  deriving DecidableEq, Repr

def commanderView (state : State) : CommanderObservation where
  phase := state.phase
  claimBroadcast := state.claimBroadcast
  evidenceShared := state.evidenceShared
  pactFunded := state.pactFunded
  visibleMessages := messagesFor commanderActor state.messages
  defenseTokens := (state.accounts.balance commanderAccount defenseTokenId).atoms
  evidenceSeals := (state.accounts.balance commanderAccount intelligenceSealId).atoms
  evacueesInTransit := (state.accounts.balance convoyAccount evacueeId).atoms
  outcome := state.outcome
  civiliansSaved := state.civiliansSaved
  credibility := state.credibility
  commanderUtility := state.commanderUtility
  partnerUtility := state.partnerUtility

def observationPolicy : ObservationPolicy State CommanderObservation where
  permitted := fun _ state view => view = commanderView state
  observe := fun _ state => commanderView state
  sound := by intro actor state; rfl

structure VisibleCandidate where
  id : CandidateId
  label : String
  detail : String
  selectable : Bool
  explanation : String
  sealed : Bool
  deriving DecidableEq, Repr

def candidateSurface
    (_ : ActorId)
    (observation : CommanderObservation) : List VisibleCandidate :=
  match observation.phase with
  | .negotiation =>
      [{ id := claimCandidate.id
         label := "Broadcast harbor-safe claim"
         detail := "Cheap talk: make an attributable claim without evidence."
         selectable := true
         explanation := "The broadcast channel is available."
         sealed := false },
       { id := evidenceCandidate.id
         label := "Share verified threat evidence"
         detail := "Expose the unique intelligence seal to make the signal credible."
         selectable := true
         explanation := "Command visibly holds the unique evidence seal."
         sealed := false },
       { id := pactCandidate.id
         label := "Fund mutual-defense escrow"
         detail := "Lock two defense tokens behind the joint accord."
         selectable := true
         explanation := "Command visibly holds two defense tokens."
         sealed := false },
       { id := inspectPartnerCandidate.id
         label := "Inspect partner order early"
         detail := "Test the sealed information boundary without learning the order."
         selectable := false
         explanation := "The order remains unavailable until simultaneous reveal."
         sealed := true }]
  | .sealed =>
      [{ id := escortCandidate.id
         label := "Reveal escort order"
         detail := "Cooperate without seeing the partner's sealed order."
         selectable := true
         explanation := "The commander's commitment is ready to reveal."
         sealed := true },
       { id := seizeCandidate.id
         label := "Reveal asset-seizure order"
         detail := "Defect and attempt to take the strategic asset."
         selectable := true
         explanation := "The commander's commitment is ready to reveal."
         sealed := true }]
  | .resolved => []

def safeCommandPolicy :
    ActorSafeCommandPolicy State CommanderObservation VisibleCandidate
      observationPolicy where
  present := candidateSurface

def hiddenPartnerAlternative : State :=
  { claimNodeSnapshot.timeline.application with
      partnerNature := .cooperative
      partnerOrder := .escort }

def sealedInformationSet : InformationSet State CommanderObservation observationPolicy where
  id := 1
  actor := commanderActor
  representative := claimNodeSnapshot.timeline.application
  alternatives :=
    [claimNodeSnapshot.timeline.application, hiddenPartnerAlternative]
  representativeMember := by simp
  indistinguishable := by
    intro state member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · rfl
    · rfl

theorem sealed_surface_no_leak :
    safeCommandPolicy.surface commanderActor hiddenPartnerAlternative =
      safeCommandPolicy.surface commanderActor
        claimNodeSnapshot.timeline.application :=
  sealedInformationSet.same_command_surface safeCommandPolicy
    hiddenPartnerAlternative
      (List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr rfl)))

theorem outsider_cannot_see_verified_evidence :
    (messagesFor outsiderActor evidenceNodeSnapshot.timeline.application.messages).all
      (fun message => message.payload.statement != .verifiedRidgeThreat) = true := by
  native_decide

theorem commander_strategy_cannot_condition_on_hidden_partner
    (strategy : ObservationStrategy CommanderObservation)
    (owned : strategy.actor = commanderActor) :
    strategy.chooseAt observationPolicy hiddenPartnerAlternative =
      strategy.chooseAt observationPolicy claimNodeSnapshot.timeline.application := by
  apply strategy.information_set_consistent observationPolicy
  rw [owned]
  rfl

/-! ## Proof-backed command graph -/

structure CandidateSpec where
  candidate : CommandCandidate Intent
  component : String
  label : String
  detail : String
  sealed : Bool := false

structure CommandNode where
  snapshot : Snapshot
  title : String
  summary : String
  outcome : MissionOutcome
  candidates : List CandidateSpec
  candidateIdsUnique :
    (candidates.map fun spec => spec.candidate.id).Nodup

structure CommandResolution where
  id : Nat
  label : String
  summary : String
  automaticOrders : List String
  reveal : String := ""

def rootNode : CommandNode where
  snapshot := root
  title := "A promise without proof"
  summary :=
    "The partner publicly promises defense. Choose cheap talk, costly evidence, or an evidence-backed escrow accord."
  outcome := .active
  candidates :=
    [{ candidate := claimCandidate
       component := "machine:veiled:relay"
       label := "Broadcast harbor-safe claim"
       detail := "Make an attributable but unverified claim." },
     { candidate := evidenceCandidate
       component := "machine:veiled:relay"
       label := "Share verified threat evidence"
       detail := "Transfer the unique evidence seal into the coalition channel." },
     { candidate := pactCandidate
       component := "account:20002"
       label := "Fund mutual-defense escrow"
       detail := "Lock two defense tokens in the account-level accord." },
     { candidate := inspectPartnerCandidate
       component := "machine:veiled:partner"
       label := "Inspect partner order early"
       detail := "The actor-safe rejection reveals no sealed payload."
       sealed := true }]
  candidateIdsUnique := by decide

def planningNode
    (snapshot : Snapshot)
    (title summary : String) : CommandNode where
  snapshot
  title
  summary
  outcome := .active
  candidates :=
    [{ candidate := escortCandidate
       component := "machine:veiled:convoy"
       label := "Reveal escort order"
       detail := "Cooperate without observing the partner's sealed command."
       sealed := true },
     { candidate := seizeCandidate
       component := "machine:veiled:checkpoint"
       label := "Reveal asset-seizure order"
       detail := "Defect and attempt to capture the strategic asset."
       sealed := true }]
  candidateIdsUnique := by decide

def claimNode := planningNode claimNodeSnapshot "Cheap talk committed"
  "The claim carried no evidence or escrow. Both orders are sealed; the partner's intent is hidden."

def evidenceNode := planningNode evidenceNodeSnapshot "Costly signal delivered"
  "The unique evidence seal makes the threat report credible, but no resources guarantee cooperation."

def accordNode := planningNode accordNodeSnapshot "Accord funded"
  "Verified evidence and two escrowed defense tokens support a resource-backed mutual escort."

def terminalNode
    (snapshot : Snapshot)
    (title summary : String)
    (outcome : MissionOutcome) : CommandNode where
  snapshot
  title
  summary
  outcome
  candidates := []
  candidateIdsUnique := by simp

def exploitedNode := terminalNode claimEscort.child "Promise exploited"
  "Command escorted while the opportunistic partner seized the asset; only eight evacuees survived."
  .exploitedCooperation

def mutualDefectionNode := terminalNode claimSeize.child "Mutual defection"
  "Both factions pursued the asset. The corridor collapsed and only four evacuees survived."
  .mutualDefection

def verifiedNode := terminalNode evidenceEscort.child "Verified cooperation"
  "Costly evidence aligned both escorts. Twenty evacuees survived without a binding escrow."
  .verifiedCooperation

def preemptiveNode := terminalNode evidenceSeize.child "Preemptive betrayal"
  "Command used credible intelligence to win the asset, sacrificing the cooperative response."
  .preemptiveBetrayal

def paretoNode := terminalNode accordEscort.child "Veiled Accord holds"
  "Both sealed escorts matched: all twenty-four evacuees survived and the asset reached neutral custody."
  .paretoAccord

def trustedBetrayalNode := terminalNode accordSeize.child "Trusted betrayal"
  "Command defected after escrow induced cooperation, winning the asset and destroying credibility."
  .trustedBetrayal

def nodes : List CommandNode :=
  [rootNode, claimNode, evidenceNode, accordNode, exploitedNode,
   mutualDefectionNode, verifiedNode, preemptiveNode, paretoNode,
   trustedBetrayalNode]

abbrev ProvedNode := Maquina.CommandGraphNode executor initialState

def provedNode (node : CommandNode) : ProvedNode :=
  assessCommandGraphNode executor initialState node.snapshot
    (node.candidates.map fun spec => spec.candidate) (by
      simpa [List.map_map, Function.comp_def] using node.candidateIdsUnique)

def provedRootNode := provedNode rootNode
def provedClaimNode := provedNode claimNode
def provedEvidenceNode := provedNode evidenceNode
def provedAccordNode := provedNode accordNode
def provedExploitedNode := provedNode exploitedNode
def provedMutualDefectionNode := provedNode mutualDefectionNode
def provedVerifiedNode := provedNode verifiedNode
def provedPreemptiveNode := provedNode preemptiveNode
def provedParetoNode := provedNode paretoNode
def provedTrustedBetrayalNode := provedNode trustedBetrayalNode

def provedNodes : List ProvedNode :=
  [provedRootNode, provedClaimNode, provedEvidenceNode, provedAccordNode,
   provedExploitedNode, provedMutualDefectionNode, provedVerifiedNode,
   provedPreemptiveNode, provedParetoNode, provedTrustedBetrayalNode]

abbrev ProvedResolution :=
  Maquina.CommandGraphResolution executor initialState provedNodes

def provedTick
    (parent : Snapshot)
    (resolved : ResolvedSnapshotOrderSet executor initialState parent) :
    Maquina.CommandGraphStep executor initialState :=
  commandGraphStep executor initialState parent resolved

def resolutions : List CommandResolution :=
  [{ id := 0
     label := "Trust cheap talk"
     summary := "Broadcast an unverified route claim and proceed without a guarantee."
     automaticOrders := ["seal both factions' corridor orders"] },
   { id := 1
     label := "Send costly evidence"
     summary := "Expose the unique intelligence seal before orders close."
     automaticOrders := ["seal both factions' corridor orders"] },
   { id := 2
     label := "Ratify Veiled Accord"
     summary := "Share verified evidence and escrow two defense tokens atomically."
     automaticOrders := ["seal both factions' corridor orders"] },
   { id := 10
     label := "Cooperate"
     summary := "Reveal the escort order beside the partner's previously sealed order."
     automaticOrders := []
     reveal := "COMMAND: ESCORT · PARTNER: SEIZE ASSET" },
   { id := 11
     label := "Defect"
     summary := "Reveal asset seizure; the partner reveals the same opportunistic order."
     automaticOrders := []
     reveal := "COMMAND: SEIZE ASSET · PARTNER: SEIZE ASSET" },
   { id := 12
     label := "Cooperate"
     summary := "The costly signal coordinates two escort orders."
     automaticOrders := []
     reveal := "COMMAND: ESCORT · PARTNER: ESCORT" },
   { id := 13
     label := "Defect"
     summary := "Command defects after inducing a cooperative escort."
     automaticOrders := []
     reveal := "COMMAND: SEIZE ASSET · PARTNER: ESCORT" },
   { id := 14
     label := "Honor the accord"
     summary := "Both resource-backed escort commitments are revealed."
     automaticOrders := []
     reveal := "COMMAND: ESCORT · PARTNER: ESCORT" },
   { id := 15
     label := "Betray the accord"
     summary := "Command exploits the cooperation induced by escrow."
     automaticOrders := []
     reveal := "COMMAND: SEIZE ASSET · PARTNER: ESCORT" }]

def provedResolutions : List ProvedResolution :=
  [{ id := 0
     source := provedRootNode
     target := provedClaimNode
     sourceMember := by simp [provedNodes]
     targetMember := by simp [provedNodes]
     actionIds := [claimCandidate.id]
     actionIdsNonempty := by decide
     actionIdsUnique := by decide
     actionsAccepted := by native_decide
     steps := [provedTick root claimApplied, provedTick claimApplied.child claimClosed]
     stepsNonempty := by decide
     firstStepActionsExact := by native_decide
     stepsConnect := by
       simp only [CommandGraphStepsConnect]
       exact ⟨SameSnapshotData.refl root,
         ⟨SameSnapshotData.refl claimApplied.child,
           SameSnapshotData.refl claimNodeSnapshot⟩⟩ },
   { id := 1
     source := provedRootNode
     target := provedEvidenceNode
     sourceMember := by simp [provedNodes]
     targetMember := by simp [provedNodes]
     actionIds := [evidenceCandidate.id]
     actionIdsNonempty := by decide
     actionIdsUnique := by decide
     actionsAccepted := by native_decide
     steps := [provedTick root evidenceApplied,
       provedTick evidenceApplied.child evidenceClosed]
     stepsNonempty := by decide
     firstStepActionsExact := by native_decide
     stepsConnect := by
       simp only [CommandGraphStepsConnect]
       exact ⟨SameSnapshotData.refl root,
         ⟨SameSnapshotData.refl evidenceApplied.child,
           SameSnapshotData.refl evidenceNodeSnapshot⟩⟩ },
   { id := 2
     source := provedRootNode
     target := provedAccordNode
     sourceMember := by simp [provedNodes]
     targetMember := by simp [provedNodes]
     actionIds := [evidenceCandidate.id, pactCandidate.id]
     actionIdsNonempty := by decide
     actionIdsUnique := by decide
     actionsAccepted := by native_decide
     steps := [provedTick root accordApplied, provedTick accordApplied.child accordClosed]
     stepsNonempty := by decide
     firstStepActionsExact := by native_decide
     stepsConnect := by
       simp only [CommandGraphStepsConnect]
       exact ⟨SameSnapshotData.refl root,
         ⟨SameSnapshotData.refl accordApplied.child,
           SameSnapshotData.refl accordNodeSnapshot⟩⟩ },
   { id := 10
     source := provedClaimNode
     target := provedExploitedNode
     sourceMember := by simp [provedNodes]
     targetMember := by simp [provedNodes]
     actionIds := [escortCandidate.id]
     actionIdsNonempty := by decide
     actionIdsUnique := by decide
     actionsAccepted := by native_decide
     steps := [provedTick claimNodeSnapshot claimEscort]
     stepsNonempty := by decide
     firstStepActionsExact := by native_decide
     stepsConnect := by
       simp only [CommandGraphStepsConnect]
       exact ⟨SameSnapshotData.refl claimNodeSnapshot,
         SameSnapshotData.refl claimEscort.child⟩ },
   { id := 11
     source := provedClaimNode
     target := provedMutualDefectionNode
     sourceMember := by simp [provedNodes]
     targetMember := by simp [provedNodes]
     actionIds := [seizeCandidate.id]
     actionIdsNonempty := by decide
     actionIdsUnique := by decide
     actionsAccepted := by native_decide
     steps := [provedTick claimNodeSnapshot claimSeize]
     stepsNonempty := by decide
     firstStepActionsExact := by native_decide
     stepsConnect := by
       simp only [CommandGraphStepsConnect]
       exact ⟨SameSnapshotData.refl claimNodeSnapshot,
         SameSnapshotData.refl claimSeize.child⟩ },
   { id := 12
     source := provedEvidenceNode
     target := provedVerifiedNode
     sourceMember := by simp [provedNodes]
     targetMember := by simp [provedNodes]
     actionIds := [escortCandidate.id]
     actionIdsNonempty := by decide
     actionIdsUnique := by decide
     actionsAccepted := by native_decide
     steps := [provedTick evidenceNodeSnapshot evidenceEscort]
     stepsNonempty := by decide
     firstStepActionsExact := by native_decide
     stepsConnect := by
       simp only [CommandGraphStepsConnect]
       exact ⟨SameSnapshotData.refl evidenceNodeSnapshot,
         SameSnapshotData.refl evidenceEscort.child⟩ },
   { id := 13
     source := provedEvidenceNode
     target := provedPreemptiveNode
     sourceMember := by simp [provedNodes]
     targetMember := by simp [provedNodes]
     actionIds := [seizeCandidate.id]
     actionIdsNonempty := by decide
     actionIdsUnique := by decide
     actionsAccepted := by native_decide
     steps := [provedTick evidenceNodeSnapshot evidenceSeize]
     stepsNonempty := by decide
     firstStepActionsExact := by native_decide
     stepsConnect := by
       simp only [CommandGraphStepsConnect]
       exact ⟨SameSnapshotData.refl evidenceNodeSnapshot,
         SameSnapshotData.refl evidenceSeize.child⟩ },
   { id := 14
     source := provedAccordNode
     target := provedParetoNode
     sourceMember := by simp [provedNodes]
     targetMember := by simp [provedNodes]
     actionIds := [escortCandidate.id]
     actionIdsNonempty := by decide
     actionIdsUnique := by decide
     actionsAccepted := by native_decide
     steps := [provedTick accordNodeSnapshot accordEscort]
     stepsNonempty := by decide
     firstStepActionsExact := by native_decide
     stepsConnect := by
       simp only [CommandGraphStepsConnect]
       exact ⟨SameSnapshotData.refl accordNodeSnapshot,
         SameSnapshotData.refl accordEscort.child⟩ },
   { id := 15
     source := provedAccordNode
     target := provedTrustedBetrayalNode
     sourceMember := by simp [provedNodes]
     targetMember := by simp [provedNodes]
     actionIds := [seizeCandidate.id]
     actionIdsNonempty := by decide
     actionIdsUnique := by decide
     actionsAccepted := by native_decide
     steps := [provedTick accordNodeSnapshot accordSeize]
     stepsNonempty := by decide
     firstStepActionsExact := by native_decide
     stepsConnect := by
       simp only [CommandGraphStepsConnect]
       exact ⟨SameSnapshotData.refl accordNodeSnapshot,
         SameSnapshotData.refl accordSeize.child⟩ }]

def provedGraph : Maquina.CommandGraph executor initialState where
  actor := commanderActor
  nodes := provedNodes
  root := provedRootNode
  rootMember := by simp [provedNodes]
  nodeIdsUnique := by native_decide
  candidatesOwned := by native_decide
  resolutions := provedResolutions
  resolutionIdsUnique := by native_decide
  resolutionChoicesUnique := by native_decide
  acceptedCandidatesCovered := by native_decide
  terminalComplete := by native_decide

theorem sealed_round_has_two_unique_actors :
    ((closedRound .escort .seizeAsset).orderSet.orders.map fun item => item.actor).Nodup :=
  (closedRound .escort .seizeAsset).order_actors_unique

example :
    (accordNodeSnapshot.timeline.application.accounts.balance escrowAccount
      defenseTokenId).atoms = 2 := by native_decide

example : accordEscort.child.timeline.application.outcome = .paretoAccord := by
  native_decide

example : accordEscort.child.timeline.application.civiliansSaved = 24 := by
  native_decide

example : accordSeize.child.timeline.application.outcome = .trustedBetrayal := by
  native_decide

example : claimEscort.child.timeline.application.outcome = .exploitedCooperation := by
  native_decide

end Maquina.Games.VeiledAccord.Command
