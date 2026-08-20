import Maquina.Scheduler

/-!
# Maquina Counterfactual Commands

Game-independent actors, candidate assessment, simultaneous command order sets,
immutable replayable snapshots, and forks. Applications own all candidate
enumeration, observation policy, intent meaning, and outcome vocabulary.
-/

namespace Maquina

/-- Stable identity for an application actor. Core assigns it no authority. -/
structure ActorId where
  value : Nat
  deriving DecidableEq, Repr

/-- Stable identity for one candidate action exposed to an actor. -/
structure CandidateId where
  value : Nat
  deriving DecidableEq, Repr

/-- Stable identity for one immutable replayable snapshot. -/
structure SnapshotId where
  value : Nat
  deriving DecidableEq, Repr

/-- An application-owned intent offered to one actor. -/
structure CommandCandidate (Intent : Type) where
  id : CandidateId
  actor : ActorId
  payload : Intent

/--
Candidate assessment is proof-carrying on acceptance and has no successor field
on rejection.
-/
inductive CandidateAssessment
    (State Issue Receipt : Type)
    (replay : Receipt → State → State)
    (before : State) where
  | accepted (applied : AppliedIntent State Receipt replay before)
  | rejected (issues : List Issue)

def CandidateAssessment.successor?
    (assessment : CandidateAssessment State Issue Receipt replay before) :
    Option State :=
  match assessment with
  | .accepted applied => some applied.after
  | .rejected _ => none

@[simp]
theorem CandidateAssessment.rejected_has_no_successor
    (issues : List Issue) :
    (CandidateAssessment.rejected issues :
      CandidateAssessment State Issue Receipt replay before).successor? = none :=
  rfl

/-- One candidate paired with its complete assessment at a snapshot. -/
structure AssessedCandidate
    (State Intent Issue Receipt : Type)
    (executor : IntentExecutor State Intent Issue Receipt)
    (before : State) where
  candidate : CommandCandidate Intent
  assessment : CandidateAssessment State Issue Receipt executor.replay before

def assessCandidate
    (executor : IntentExecutor State Intent Issue Receipt)
    (before : State)
    (candidate : CommandCandidate Intent) :
    AssessedCandidate State Intent Issue Receipt executor before :=
  match executor.apply before candidate.payload with
  | .ok applied => ⟨candidate, .accepted applied⟩
  | .error issues => ⟨candidate, .rejected issues⟩

@[simp]
theorem assessCandidate_candidate
    (executor : IntentExecutor State Intent Issue Receipt)
    (before : State)
    (candidate : CommandCandidate Intent) :
    (assessCandidate executor before candidate).candidate = candidate := by
  unfold assessCandidate
  split <;> rfl

def assessCandidates
    (executor : IntentExecutor State Intent Issue Receipt)
    (before : State)
    (candidates : List (CommandCandidate Intent)) :
    List (AssessedCandidate State Intent Issue Receipt executor before) :=
  candidates.map (assessCandidate executor before)

def CandidateAssessment.isAccepted
    (assessment : CandidateAssessment State Issue Receipt replay before) : Bool :=
  match assessment with
  | .accepted _ => true
  | .rejected _ => false

def AssessedCandidate.acceptedId?
    (assessed : AssessedCandidate State Intent Issue Receipt executor before) :
    Option CandidateId :=
  if assessed.assessment.isAccepted then some assessed.candidate.id else none

/-- Actor filtering never changes or reassesses candidate payloads. -/
def candidatesFor
    (actor : ActorId)
    (candidates : List (CommandCandidate Intent)) :
    List (CommandCandidate Intent) :=
  candidates.filter fun candidate => candidate.actor = actor

theorem candidatesFor_actor
    (candidate : CommandCandidate Intent)
    (member : candidate ∈ candidatesFor actor candidates) :
    candidate.actor = actor := by
  simpa [candidatesFor] using (List.mem_filter.mp member).2

/-- A game-defined observation boundary with a proof of its own policy. -/
structure ObservationPolicy (State Observation : Type) where
  permitted : ActorId → State → Observation → Prop
  observe : ActorId → State → Observation
  sound : ∀ actor state, permitted actor state (observe actor state)

/-- One actor-scoped view of an immutable snapshot. -/
structure ActorObservation
    (State Observation : Type)
    (policy : ObservationPolicy State Observation)
    (state : State) where
  actor : ActorId
  snapshotId : SnapshotId
  view : Observation
  permitted : policy.permitted actor state view

def observeSnapshot
    (policy : ObservationPolicy State Observation)
    (actor : ActorId)
    (snapshotId : SnapshotId)
    (state : State) : ActorObservation State Observation policy state where
  actor
  snapshotId
  view := policy.observe actor state
  permitted := policy.sound actor state

/-- One simultaneous command order. Actor identity is metadata, not priority. -/
structure CommandOrder (Intent : Type) where
  id : IntentId
  actor : ActorId
  arbitration : ArbitrationKey
  payload : Intent

namespace CommandOrder

def scheduledAt
    (tick : LogicalTick)
    (order : CommandOrder Intent) : ScheduledIntent Intent where
  id := order.id
  submittedAt := tick
  executeAt := tick
  notBeforeSubmission := Nat.le_refl tick.value
  arbitration := order.arbitration
  payload := order.payload

end CommandOrder

/-- A command set cannot contain the same stable order identity twice. -/
structure OrderSet (Intent : Type) where
  orders : List (CommandOrder Intent)
  idsUnique : (orders.map fun order => order.id).Nodup

def scheduledOrders
    (tick : LogicalTick)
    (orders : OrderSet Intent) : List (ScheduledIntent Intent) :=
  orders.orders.map (CommandOrder.scheduledAt tick)

theorem scheduledOrders_ids_unique
    (tick : LogicalTick)
    (orders : OrderSet Intent) :
    ((scheduledOrders tick orders).map fun intent => intent.id).Nodup := by
  unfold scheduledOrders
  rw [List.map_map]
  change (orders.orders.map fun order => order.id).Nodup
  exact orders.idsUnique

/--
Install one command set at the current logical tick. The emptiness proof makes
it impossible for this boundary to silently discard previously pending work.
-/
def prepareOrderSet
    (before : TimelineState State Intent)
    (_ready : before.pending = [])
    (orders : OrderSet Intent) : TimelineState State Intent :=
  { before with
      pending := scheduledOrders before.tick orders
      pendingIdsUnique := scheduledOrders_ids_unique before.tick orders }

/-- Resolve one simultaneous order set through the ordinary scheduler. -/
def resolveOrderSet
    (executor : IntentExecutor State Intent Issue Receipt)
    (before : TimelineState State Intent)
    (ready : before.pending = [])
    (orders : OrderSet Intent) :
    AppliedTick executor (prepareOrderSet before ready orders) :=
  applyTick executor (prepareOrderSet before ready orders)

theorem resolveOrderSet_replay
    (executor : IntentExecutor State Intent Issue Receipt)
    (before : TimelineState State Intent)
    (ready : before.pending = [])
    (orders : OrderSet Intent) :
    replayTimelineEvents executor
        (resolveOrderSet executor before ready orders).events
        before.application =
      (resolveOrderSet executor before ready orders).after.application :=
  (resolveOrderSet executor before ready orders).replayExact

theorem resolveOrderSet_tick
    (executor : IntentExecutor State Intent Issue Receipt)
    (before : TimelineState State Intent)
    (ready : before.pending = [])
    (orders : OrderSet Intent) :
    (resolveOrderSet executor before ready orders).after.tick = before.tick.succ :=
  (resolveOrderSet executor before ready orders).tickAdvanced

/-- A stable snapshot whose complete event history replays from one origin. -/
structure TimelineSnapshot
    (executor : IntentExecutor State Intent Issue Receipt)
    (origin : State) where
  id : SnapshotId
  timeline : TimelineState State Intent
  history : List (TimelineEvent Issue Receipt)
  replayExact :
    replayTimelineEvents executor history origin = timeline.application

/-- A child history extends, and never rewrites, its parent history. -/
structure SnapshotFork
    (executor : IntentExecutor State Intent Issue Receipt)
    (origin : State)
    (parent child : TimelineSnapshot executor origin) where
  events : List (TimelineEvent Issue Receipt)
  historyExtended : child.history = parent.history ++ events

theorem SnapshotFork.parent_history_is_prefix
    (fork : SnapshotFork executor origin parent child) :
    ∃ suffix, child.history = parent.history ++ suffix :=
  ⟨fork.events, fork.historyExtended⟩

theorem SnapshotFork.siblings_share_parent_prefix
    (left : SnapshotFork executor origin parent leftChild)
    (right : SnapshotFork executor origin parent rightChild) :
    ∃ leftSuffix rightSuffix,
      leftChild.history = parent.history ++ leftSuffix ∧
      rightChild.history = parent.history ++ rightSuffix :=
  ⟨left.events, right.events, left.historyExtended, right.historyExtended⟩

/-- Proof-carrying resolution of one order set into one immutable child fork. -/
structure ResolvedSnapshotOrderSet
    (executor : IntentExecutor State Intent Issue Receipt)
    (origin : State)
    (parent : TimelineSnapshot executor origin) where
  orders : OrderSet Intent
  ready : parent.timeline.pending = []
  applied : AppliedTick executor (prepareOrderSet parent.timeline ready orders)
  child : TimelineSnapshot executor origin
  childTimeline : child.timeline = applied.after
  fork : SnapshotFork executor origin parent child
  forkEvents : fork.events = applied.events

def resolveSnapshotOrderSet
    (executor : IntentExecutor State Intent Issue Receipt)
    (origin : State)
    (parent : TimelineSnapshot executor origin)
    (childId : SnapshotId)
    (ready : parent.timeline.pending = [])
    (orders : OrderSet Intent) :
    ResolvedSnapshotOrderSet executor origin parent :=
  let applied := resolveOrderSet executor parent.timeline ready orders
  let child : TimelineSnapshot executor origin :=
    { id := childId
      timeline := applied.after
      history := parent.history ++ applied.events
      replayExact := by
        rw [replayTimelineEvents_append, parent.replayExact]
        exact applied.replayExact }
  { orders
    ready
    applied
    child
    childTimeline := rfl
    fork := { events := applied.events, historyExtended := rfl }
    forkEvents := rfl }

/-! ## Proof-carrying command graphs -/

/--
One immutable graph node. Candidate assessment is stored at the node's exact
application snapshot, so an exported availability status cannot be detached
from the authoritative executor that established it.
-/
structure CommandGraphNode
    (executor : IntentExecutor State Intent Issue Receipt)
    (origin : State) where
  snapshot : TimelineSnapshot executor origin
  candidates : List
    (AssessedCandidate State Intent Issue Receipt executor
      snapshot.timeline.application)
  candidateIdsUnique :
    (candidates.map fun assessed => assessed.candidate.id).Nodup

def CommandGraphNode.candidateIds
    (node : CommandGraphNode executor origin) : List CandidateId :=
  node.candidates.map fun assessed => assessed.candidate.id

def CommandGraphNode.acceptedCandidateIds
    (node : CommandGraphNode executor origin) : List CandidateId :=
  node.candidates.filterMap AssessedCandidate.acceptedId?

def assessCommandGraphNode
    (executor : IntentExecutor State Intent Issue Receipt)
    (origin : State)
    (snapshot : TimelineSnapshot executor origin)
    (candidates : List (CommandCandidate Intent))
    (candidateIdsUnique : (candidates.map fun candidate => candidate.id).Nodup) :
    CommandGraphNode executor origin where
  snapshot
  candidates := assessCandidates executor snapshot.timeline.application candidates
  candidateIdsUnique := by
    simpa [assessCandidates, List.map_map, Function.comp_def] using
      candidateIdsUnique

/--
One exact tick inside a graph edge. It owns both immutable endpoint snapshots,
local replay, logical-time advance, and the append-only history equation.
-/
structure CommandGraphStep
    (executor : IntentExecutor State Intent Issue Receipt)
    (origin : State) where
  parent : TimelineSnapshot executor origin
  child : TimelineSnapshot executor origin
  processed : List (ScheduledIntent Intent)
  events : List (TimelineEvent Issue Receipt)
  replayExact :
    replayTimelineEvents executor events parent.timeline.application =
      child.timeline.application
  tickAdvanced : child.timeline.tick = parent.timeline.tick.succ
  historyExtended : child.history = parent.history ++ events

def commandGraphStep
    (executor : IntentExecutor State Intent Issue Receipt)
    (origin : State)
    (parent : TimelineSnapshot executor origin)
    (resolved : ResolvedSnapshotOrderSet executor origin parent) :
    CommandGraphStep executor origin where
  parent
  child := resolved.child
  processed := resolved.applied.processed
  events := resolved.applied.events
  replayExact := by
    rw [resolved.childTimeline]
    exact resolved.applied.replayExact
  tickAdvanced := by
    rw [resolved.childTimeline]
    exact resolved.applied.tickAdvanced
  historyExtended := by
    rw [← resolved.forkEvents]
    exact resolved.fork.historyExtended

/-- Snapshot equality relevant to graph topology, excluding proof fields. -/
def SameSnapshotData
    (left right : TimelineSnapshot executor origin) : Prop :=
  left.id = right.id ∧
    left.timeline = right.timeline ∧
    left.history = right.history

theorem SameSnapshotData.refl
    (snapshot : TimelineSnapshot executor origin) :
    SameSnapshotData snapshot snapshot :=
  ⟨rfl, rfl, rfl⟩

/-- Every step starts at the previous exact child and the path ends at target. -/
def CommandGraphStepsConnect
    (current target : TimelineSnapshot executor origin) :
    List (CommandGraphStep executor origin) → Prop
  | [] => SameSnapshotData current target
  | step :: rest =>
      SameSnapshotData current step.parent ∧
        CommandGraphStepsConnect step.child target rest

/-- Canonical order-insensitive identity for command and scheduler IDs. -/
def canonicalCommandIds (ids : List Nat) : List Nat :=
  ids.mergeSort fun left right =>
    decide (left < right)

def canonicalCommandActionIds (actionIds : List CandidateId) : List Nat :=
  canonicalCommandIds (actionIds.map fun actionId => actionId.value)

def initialCommandStepIntentIds
    (steps : List (CommandGraphStep executor origin)) : List Nat :=
  match steps with
  | [] => []
  | step :: _ => canonicalCommandIds
      (step.processed.map fun scheduled => scheduled.id.value)

/--
One graph edge. Closure is exact rather than ID-only: its source and target are
members of the graph's node list, and its nonempty tick path connects those
exact immutable snapshots.
-/
structure CommandGraphResolution
    (executor : IntentExecutor State Intent Issue Receipt)
    (origin : State)
    (nodes : List (CommandGraphNode executor origin)) where
  id : Nat
  source : CommandGraphNode executor origin
  target : CommandGraphNode executor origin
  sourceMember : source ∈ nodes
  targetMember : target ∈ nodes
  actionIds : List CandidateId
  actionIdsNonempty : actionIds ≠ []
  actionIdsUnique : actionIds.Nodup
  actionsAccepted :
    ∀ actionId ∈ actionIds, actionId ∈ source.acceptedCandidateIds
  steps : List (CommandGraphStep executor origin)
  stepsNonempty : steps ≠ []
  firstStepActionsExact :
    canonicalCommandActionIds actionIds = initialCommandStepIntentIds steps
  stepsConnect :
    CommandGraphStepsConnect source.snapshot target.snapshot steps

def CommandGraphResolution.choiceKey
    (resolution : CommandGraphResolution executor origin nodes) :
    SnapshotId × List Nat :=
  (resolution.source.snapshot.id,
    canonicalCommandActionIds resolution.actionIds)

def outgoingCommandResolutionIds
    (resolutions : List (CommandGraphResolution executor origin nodes))
    (source : SnapshotId) : List Nat :=
  resolutions.filterMap fun resolution =>
    if resolution.source.snapshot.id = source then some resolution.id else none

/--
A closed, unambiguous, actor-owned command graph. Terminal completeness is an
iff: a node has no accepted candidate exactly when it has no outgoing edge.
Every deeper edge obligation—accepted action references, exact endpoints,
nonempty path, replay, logical time, and immutable history extension—is carried
by `CommandGraphResolution` and `CommandGraphStep`.
-/
structure CommandGraph
    (executor : IntentExecutor State Intent Issue Receipt)
    (origin : State) where
  actor : ActorId
  nodes : List (CommandGraphNode executor origin)
  root : CommandGraphNode executor origin
  rootMember : root ∈ nodes
  nodeIdsUnique : (nodes.map fun node => node.snapshot.id).Nodup
  candidatesOwned : ∀ node ∈ nodes, ∀ assessed ∈ node.candidates,
    assessed.candidate.actor = actor
  resolutions : List (CommandGraphResolution executor origin nodes)
  resolutionIdsUnique : (resolutions.map fun resolution => resolution.id).Nodup
  resolutionChoicesUnique :
    (resolutions.map CommandGraphResolution.choiceKey).Nodup
  acceptedCandidatesCovered : ∀ node ∈ nodes,
    ∀ actionId ∈ node.acceptedCandidateIds,
      ∃ resolution ∈ resolutions,
        resolution.source.snapshot.id = node.snapshot.id ∧
          actionId ∈ resolution.actionIds
  terminalComplete : ∀ node ∈ nodes,
    (node.acceptedCandidateIds = []) ↔
      (outgoingCommandResolutionIds resolutions node.snapshot.id = [])

theorem CommandGraph.resolution_actions_accepted
    (graph : CommandGraph executor origin)
    (resolution : CommandGraphResolution executor origin graph.nodes)
    (actionId : CandidateId)
    (member : actionId ∈ resolution.actionIds) :
    actionId ∈ resolution.source.acceptedCandidateIds :=
  resolution.actionsAccepted actionId member

theorem CommandGraph.terminal_iff_no_outgoing
    (graph : CommandGraph executor origin)
    (node : CommandGraphNode executor origin)
    (member : node ∈ graph.nodes) :
    node.acceptedCandidateIds = [] ↔
      outgoingCommandResolutionIds graph.resolutions node.snapshot.id = [] :=
  graph.terminalComplete node member

theorem CommandGraph.accepted_candidate_has_resolution
    (graph : CommandGraph executor origin)
    (node : CommandGraphNode executor origin)
    (nodeMember : node ∈ graph.nodes)
    (actionId : CandidateId)
    (accepted : actionId ∈ node.acceptedCandidateIds) :
    ∃ resolution ∈ graph.resolutions,
      resolution.source.snapshot.id = node.snapshot.id ∧
        actionId ∈ resolution.actionIds :=
  graph.acceptedCandidatesCovered node nodeMember actionId accepted

end Maquina
