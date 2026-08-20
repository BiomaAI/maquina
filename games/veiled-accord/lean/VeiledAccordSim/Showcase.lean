import VeiledAccordSim.Command
import MaquinaViz

/-!
# Operation Veiled Accord Showcase Adapter

The game exports actor-safe strategic metadata and ordinary Maquina state
views. The shared browser renders the result without executing mission rules.
-/

namespace Maquina.Games.VeiledAccord.Showcase

open Maquina.Games.VeiledAccord Simulation Visualization

private def position (x y z : Float) : Vec3 := { x, y, z }

def relayMachineId := "machine:veiled:relay"
def convoyMachineId := "machine:veiled:convoy"
def checkpointMachineId := "machine:veiled:checkpoint"
def partnerMachineId := "machine:veiled:partner"

def statementName : Statement → String
  | .promiseDefense => "I will defend the corridor"
  | .claimHarborSafe => "Harbor route is safe"
  | .verifiedRidgeThreat => "Verified threat on Ridge route"
  | .accordRatified => "Mutual-defense accord ratified"

def audienceName : MessageAudience → String
  | .broadcast => "public"
  | .privateTo actor => s!"private · actor {actor.value}"
  | .coalition actors =>
      s!"coalition · {String.intercalate ", " (actors.map fun actor => toString actor.value)}"

def outcomeName : MissionOutcome → String
  | .active => "active"
  | .paretoAccord => "pareto-accord"
  | .verifiedCooperation => "verified-cooperation"
  | .exploitedCooperation => "exploited-cooperation"
  | .trustedBetrayal => "trusted-betrayal"
  | .preemptiveBetrayal => "preemptive-betrayal"
  | .mutualDefection => "mutual-defection"

def presentation : PresentationView where
  theme :=
    { background := "#070b12"
      surface := "#111823"
      accent := "#b991ff" }
  resources :=
    [{ id := resourceKey defenseTokenId
       label := "Defense tokens"
       symbol := "D"
       color := "#66d9ff"
       geometry := "octahedron" },
     { id := resourceKey intelligenceSealId
       label := "Verified evidence"
       symbol := "V"
       color := "#b991ff"
       geometry := "octahedron" },
     { id := resourceKey evacueeId
       label := "Evacuees"
       symbol := "E"
       color := "#e9eef5"
       geometry := "sphere" },
     { id := resourceKey strategicAssetId
       label := "Strategic asset"
       symbol := "A"
       color := "#ffbf5d"
       geometry := "cube" }]
  accounts :=
    [{ id := accountKey commanderAccount
       label := "Coalition command"
       kind := "participant"
       color := "#66d9ff"
       position := position (-11) 0 (-5) },
     { id := accountKey partnerAccount
       label := "Partner command"
       kind := "machine-inventory"
       color := "#ff6f91"
       position := position 10 0 (-4) },
     { id := accountKey escrowAccount
       label := "Accord escrow"
       kind := "custody"
       color := "#65d59a"
       position := position 0 0 (-6.5) },
     { id := accountKey partnerIntelAccount
       label := "Coalition channel"
       kind := "machine-inventory"
       color := "#b991ff"
       position := position (-4.5) 0 (-1.5) },
     { id := accountKey convoyAccount
       label := "Convoy manifest"
       kind := "machine-inventory"
       color := "#e9eef5"
       position := position (-8) 0 6.5 },
     { id := accountKey sanctuaryAccount
       label := "Sanctuary"
       kind := "sanctuary"
       color := "#65d59a"
       position := position 10.5 0 7 },
     { id := accountKey lossAccount
       label := "Corridor losses"
       kind := "loss"
       color := "#ff5e67"
       position := position 5.5 0 9.5 },
     { id := accountKey authorityAccount
       label := "Neutral authority"
       kind := "machine-inventory"
       color := "#ffbf5d"
       position := position 5 0 1.5 },
     { id := accountKey contestedAccount
       label := "Contested ground"
       kind := "contested"
       color := "#ff7c66"
       position := position 0 0 10 }]
  machines :=
    [{ id := relayMachineId
       label := "Encrypted relay"
       color := "#b991ff"
       position := position (-4.5) 0 (-1.5)
       geometry := "relay"
       modes :=
         [{ mode := "relay-negotiation", activity := some "scanning" },
          { mode := "relay-sealed", activity := some "sealed" },
          { mode := "relay-revealed", activity := some "tracking" }] },
     { id := convoyMachineId
       label := "Accord convoy"
       color := "#e9eef5"
       position := position (-8) 0 6.5
       geometry := "convoy"
       modes :=
         [{ mode := "convoy-negotiation", position := some (position (-8) 0 6.5) },
          { mode := "convoy-sealed", position := some (position (-4) 0 6.5) },
          { mode := "convoy-extracted"
            position := some (position 9 0 7)
            activity := some "extracted" },
          { mode := "convoy-damaged"
            position := some (position 1.5 0 7.5)
            activity := some "damaged" }] },
     { id := checkpointMachineId
       label := "Neutral checkpoint"
       color := "#ffbf5d"
       position := position 5 0 1.5
       geometry := "checkpoint"
       modes :=
         [{ mode := "checkpoint-watching", activity := some "tracking" },
          { mode := "checkpoint-secured", activity := some "engaged" },
          { mode := "checkpoint-breached", activity := some "damaged" }] },
     { id := partnerMachineId
       label := "Partner escort"
       color := "#ff6f91"
       position := position 10 0 (-4)
       geometry := "drone"
       modes :=
         [{ mode := "partner-negotiating", activity := some "scanning" },
          { mode := "partner-sealed", activity := some "sealed" },
          { mode := "partner-cooperated", activity := some "engaged" },
          { mode := "partner-defected", activity := some "damaged" }] }]
  camera :=
    { position := position 21 25 31
      target := position 0 0 2 }

def relayMode (state : State) : String :=
  match state.phase with
  | .negotiation => "relay-negotiation"
  | .sealed => "relay-sealed"
  | .resolved => "relay-revealed"

def convoyMode (state : State) : String :=
  match state.phase with
  | .negotiation => "convoy-negotiation"
  | .sealed => "convoy-sealed"
  | .resolved =>
      match state.outcome with
      | .paretoAccord | .verifiedCooperation => "convoy-extracted"
      | _ => "convoy-damaged"

def checkpointMode (state : State) : String :=
  match state.outcome with
  | .active => "checkpoint-watching"
  | .paretoAccord | .verifiedCooperation => "checkpoint-secured"
  | _ => "checkpoint-breached"

def partnerMode (state : State) : String :=
  match state.phase with
  | .negotiation => "partner-negotiating"
  | .sealed => "partner-sealed"
  | .resolved =>
      match state.outcome with
      | .paretoAccord | .verifiedCooperation | .trustedBetrayal |
          .preemptiveBetrayal => "partner-cooperated"
      | _ => "partner-defected"

private def machineView
    (id inventory mode : String) : MachineView where
  id
  inventory
  mode
  maximumQueues := "0"
  queues := []

def projectState (timeline : TimelineState State Intent) : StateView :=
  let state := timeline.application
  { holdings := state.accounts.holdings.map fun holding =>
      { account := accountKey holding.account
        resource := resourceKey holding.resourceId
        quantity := exactNat holding.quantity.atoms }
    machines :=
      [machineView relayMachineId (accountKey partnerIntelAccount) (relayMode state),
       machineView convoyMachineId (accountKey convoyAccount) (convoyMode state),
       machineView checkpointMachineId (accountKey authorityAccount) (checkpointMode state),
       machineView partnerMachineId (accountKey partnerAccount) (partnerMode state)]
    custody := []
    nextProcessId := "0"
    logicalTick := some (exactNat timeline.tick.value)
    pendingIntents := some (exactNat timeline.pending.length) }

def issueView : Issue → IssueView
  | issue@(.wrongPhase _ _) => { code := "wrong-phase", detail := reprStr issue }
  | .duplicateClaim =>
      { code := "duplicate-claim", detail := "the claim was already broadcast" }
  | .evidenceAlreadyShared =>
      { code := "evidence-already-shared", detail := "the evidence seal already left command" }
  | .pactAlreadyFunded =>
      { code := "pact-already-funded", detail := "the escrow is already funded" }
  | .sealedOrderHidden =>
      { code := "sealed-order-hidden"
        detail := "the partner order is unavailable until simultaneous reveal" }
  | .noNegotiatedTerms =>
      { code := "no-negotiated-terms", detail := "no claim, evidence, or pact can be sealed" }
  | issue@(.accountRejected _) =>
      { code := "account-transaction-rejected", detail := reprStr issue }

def movementView
    (before after : State)
    (movement : Movement) : MovementView where
  source := accountKey movement.source
  destination := accountKey movement.destination
  resource := resourceKey movement.resource
  quantity := exactNat movement.quantity
  sourceBefore := exactNat (before.accounts.balance movement.source movement.resource).atoms
  sourceAfter := exactNat (after.accounts.balance movement.source movement.resource).atoms
  destinationBefore :=
    exactNat (before.accounts.balance movement.destination movement.resource).atoms
  destinationAfter :=
    exactNat (after.accounts.balance movement.destination movement.resource).atoms

def receiptEffects (before : State) (receipt : Receipt) : List EffectView :=
  if receipt.movements.isEmpty then [] else
    [{ kind := "strategic-account-transaction"
       movements := receipt.movements.map (movementView before receipt.after) }]

def receiptChecks (receipt : Receipt) : List CheckView :=
  let base : CheckView :=
    { kind := "authoritative-assessment"
      condition := receipt.label
      status := "accepted"
      detail := "the selected command carries a replay-exact successor" }
  if receipt.revealedOrders.isEmpty then [base] else
    [base,
     { kind := "sealed-round"
       condition := "unique commit-reveal bindings"
       status := "accepted"
       detail :=
         "both actor-unique orders matched their commitments before deterministic resolution" }]

def eventAccepted (event : TimelineEvent Issue Receipt) : Bool :=
  match event.outcome with
  | .accepted _ => true
  | .rejected _ _ => false

def tickStatus (events : List (TimelineEvent Issue Receipt)) : String :=
  if events.all eventAccepted then "accepted"
  else if events.any eventAccepted then "mixed"
  else "rejected"

def processedIntent
    (processed : List (ScheduledIntent Intent))
    (event : TimelineEvent Issue Receipt) : Option Intent :=
  (processed.find? fun item => item.id = event.intentId).map fun item => item.payload

def intentName : Intent → String
  | .broadcastClaim => "broadcast harbor-safe claim"
  | .shareEvidence => "share verified evidence"
  | .fundPact => "fund mutual-defense escrow"
  | .inspectPartnerOrder => "inspect partner order early"
  | .closeNegotiation => "seal simultaneous orders"
  | .reveal .escort => "reveal escort order"
  | .reveal .seizeAsset => "reveal asset-seizure order"

def projectTick
    (index : Nat)
    (tick : Maquina.CommandGraphStep executor initialState) : StepView :=
  let acceptedReceipts := tick.events.filterMap fun event =>
    match event.outcome with
    | .accepted receipt => some receipt
    | .rejected _ _ => none
  let issues := tick.events.flatMap fun event =>
    match event.outcome with
    | .accepted _ => []
    | .rejected _ eventIssues => eventIssues.map issueView
  let names := tick.events.filterMap fun event =>
    (processedIntent tick.processed event).map intentName
  { index
    operation := String.intercalate " + " names
    trigger := "strategic-command-fork"
    status := tickStatus tick.events
    semanticStatus := "lean-proved-strategic-replay"
    logicalTick := some (exactNat tick.parent.timeline.tick.value)
    eventSequences := tick.events.map fun event => exactNat event.sequence
    intentIds := tick.events.map fun event => exactNat event.intentId.value
    before := projectState tick.parent.timeline
    after := projectState tick.child.timeline
    checks := acceptedReceipts.flatMap receiptChecks
    effects := acceptedReceipts.flatMap (receiptEffects tick.parent.timeline.application)
    issues }

def messageView (message : ScopedMessage Communication) : CommandMessageView where
  id := exactNat message.id
  sender := exactNat message.sender.value
  audience := audienceName message.audience
  statement := statementName message.payload.statement
  verification := if message.payload.verified then "verified" else "claim"

private def commandMetric (id label : String) (value : Nat) : CommandMetricView where
  id
  label
  value := exactNat value

def metrics (snapshot : Command.Snapshot) : List CommandMetricView :=
  let state := snapshot.timeline.application
  [commandMetric "civilians-saved" "Civilians saved" state.civiliansSaved,
   commandMetric "credibility" "Credibility" state.credibility,
   commandMetric "commander-utility" "Command utility" state.commanderUtility,
   commandMetric "partner-utility" "Partner utility" state.partnerUtility,
   commandMetric "escrow" "Escrowed defense"
      (state.accounts.balance escrowAccount defenseTokenId).atoms,
   commandMetric "evidence-exposed" "Evidence exposed"
      (state.accounts.balance partnerIntelAccount intelligenceSealId).atoms]

def agreementViews (state : State) : List CommandAgreementView :=
  if state.pactFunded then
    [{ id := exactNat Simulation.accord.agreement.id
       label := "Mutual-defense accord"
       parties := Simulation.accord.agreement.parties.map fun actor => exactNat actor.value
       status := if state.phase = .resolved then "resolved" else "escrow-funded"
       escrow :=
         [{ resource := resourceKey defenseTokenId
            quantity := exactNat
              (state.accounts.balance escrowAccount defenseTokenId).atoms }] }]
  else []

def projectCandidate
    (before : State)
    (spec : Command.CandidateSpec) : CommandCandidateView :=
  let assessed := assessCandidate executor before spec.candidate
  match assessed.assessment with
  | .accepted applied =>
      { id := exactNat spec.candidate.id.value
        actor := exactNat spec.candidate.actor.value
        component := spec.component
        label := spec.label
        detail := spec.detail
        status := "accepted"
        visibility := "actor-safe"
        sealed := spec.sealed
        checks :=
          [{ kind := "actor-safe-candidate"
             condition := spec.label
             status := "accepted"
             detail :=
               "availability is projected only from the actor observation; authoritative acceptance remains proof-backed" }]
        effects := receiptEffects before applied.receipt
        issues := [] }
  | .rejected issues =>
      { id := exactNat spec.candidate.id.value
        actor := exactNat spec.candidate.actor.value
        component := spec.component
        label := spec.label
        detail := spec.detail
        status := "rejected"
        visibility := "redacted"
        sealed := spec.sealed
        checks :=
          [{ kind := "actor-safe-candidate"
             condition := spec.label
             status := "rejected"
             detail := "the actor-safe surface exposes no hidden authoritative detail" }]
        effects := []
        issues := issues.map issueView }

def nodeInformationSet (node : Command.CommandNode) : Option String :=
  if node.snapshot.id = Command.claimNodeSnapshot.id then some "sealed-partner-order"
  else none

def projectNode (node : Command.CommandNode) : CommandNodeView where
  id := exactNat node.snapshot.id.value
  stateKey := reprStr (Command.commanderView node.snapshot.timeline.application)
  title := node.title
  summary := node.summary
  outcome := outcomeName node.outcome
  state := projectState node.snapshot.timeline
  metrics := metrics node.snapshot
  candidates := node.candidates.map
    (projectCandidate node.snapshot.timeline.application)
  informationSet := nodeInformationSet node
  messages :=
    (messagesFor commanderActor node.snapshot.timeline.application.messages).map messageView
  agreements := agreementViews node.snapshot.timeline.application

def projectResolution
    (resolution : Command.CommandResolution × Command.ProvedResolution) :
    CommandResolutionView where
  id := exactNat resolution.2.id
  source := exactNat resolution.2.source.snapshot.id.value
  target := exactNat resolution.2.target.snapshot.id.value
  label := resolution.1.label
  summary := resolution.1.summary
  actionIds := resolution.2.actionIds.map fun id => exactNat id.value
  automaticOrders := resolution.1.automaticOrders
  reveal := if resolution.1.reveal.isEmpty then none else some resolution.1.reveal
  steps := resolution.2.steps.mapIdx fun index tick => projectTick (index + 1) tick

def commandGraph : CommandGraphView where
  actor := exactNat commanderActor.value
  root := exactNat Command.root.id.value
  nodes := Command.nodes.map projectNode
  resolutions :=
    (Command.resolutions.zip Command.provedResolutions).map projectResolution
  actors :=
    [{ id := exactNat commanderActor.value
       label := "Coalition command"
       role := "player · private objective"
       color := "#66d9ff" },
     { id := exactNat partnerActor.value
       label := "Partner force"
       role := "sealed counterpart"
       color := "#ff6f91" },
     { id := exactNat authorityActor.value
       label := "Neutral authority"
       role := "escrow witness"
       color := "#ffbf5d" }]
  informationSets :=
    [{ id := "sealed-partner-order"
       actor := exactNat commanderActor.value
       label := "Partner order remains hidden"
       detail :=
         "Two authoritative partner orders produce the same observation, candidates, and redacted explanations."
       nodeIds := [exactNat Command.claimNodeSnapshot.id.value]
       observationKey :=
         reprStr (Command.commanderView Command.claimNodeSnapshot.timeline.application) }]

def provenance : ProvenanceView where
  engine := leanProvenance.engine
  toolchain := leanProvenance.toolchain
  guarantees := leanProvenance.guarantees ++
    ["actor-visible command surfaces factor only through declared observations",
     "observation-equivalent hidden partner orders expose identical candidates",
     "private evidence messages are absent from unauthorized actor projections",
     "sealed commitments contain no command payload before reveal",
     "closed rounds bind one unique reveal to each unique actor",
     "multi-party approval is exact and escrow uses ordinary account transactions",
     "terminal payoff vectors and mission outcomes remain game-owned",
     "every command edge extends immutable history and replays exactly"]

def artifact : ScenarioArtifact where
  schemaVersion := protocolVersion
  id := "veiled-accord"
  gameId := "veiled accord"
  title := "Operation Veiled Accord"
  summary :=
    "Negotiate under asymmetric information, distinguish cheap talk from costly evidence, fund cooperation, and reveal sealed orders."
  presentation := presentation
  provenance := provenance
  initial := projectState Command.root.timeline
  steps := []
  commandGraph := some commandGraph

end Maquina.Games.VeiledAccord.Showcase
