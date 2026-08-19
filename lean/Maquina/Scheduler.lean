import Std

/-!
# Maquina Deterministic Timeline

Logical time, scheduled application intents, deterministic arbitration, and
immutable replayable events. This module is parameterized by the complete
application state and knows nothing about machines, accounts, games, actors,
or domain vocabulary.
-/

namespace Maquina

/-- Exact modeled time. Wall-clock time is never authoritative. -/
structure LogicalTick where
  value : Nat
  deriving DecidableEq, Repr

namespace LogicalTick

def succ (tick : LogicalTick) : LogicalTick := ⟨tick.value + 1⟩

@[simp]
theorem succ_value (tick : LogicalTick) : tick.succ.value = tick.value + 1 := rfl

end LogicalTick

/-- Stable identity of one submitted intent. -/
structure IntentId where
  value : Nat
  deriving DecidableEq, Repr

/--
Opaque game-owned arbitration coordinates. Maquina interprets smaller
coordinates first but assigns no meaning to either coordinate.
-/
structure ArbitrationKey where
  major : Nat
  minor : Nat := 0
  deriving DecidableEq, Repr

/-- One inert application intent scheduled for modeled time. -/
structure ScheduledIntent (Intent : Type) where
  id : IntentId
  submittedAt : LogicalTick
  executeAt : LogicalTick
  notBeforeSubmission : submittedAt.value ≤ executeAt.value
  arbitration : ArbitrationKey
  payload : Intent

/-- Canonical comparison over time, game-owned arbitration key, and stable ID. -/
def scheduledIntentPrecedes
    (left right : ScheduledIntent Intent) : Bool :=
  if left.executeAt.value ≠ right.executeAt.value then
    decide (left.executeAt.value < right.executeAt.value)
  else if left.arbitration.major ≠ right.arbitration.major then
    decide (left.arbitration.major < right.arbitration.major)
  else if left.arbitration.minor ≠ right.arbitration.minor then
    decide (left.arbitration.minor < right.arbitration.minor)
  else
    decide (left.id.value < right.id.value)

/-- Canonical deterministic ordering. -/
def orderScheduledIntents
    (intents : List (ScheduledIntent Intent)) : List (ScheduledIntent Intent) :=
  intents.mergeSort scheduledIntentPrecedes

/-- Ordering retains exactly the submitted intent multiset. -/
theorem orderScheduledIntents_perm
    (intents : List (ScheduledIntent Intent)) :
    (orderScheduledIntents intents).Perm intents :=
  List.mergeSort_perm intents scheduledIntentPrecedes

/-- Partition pending intents into due and future lists. -/
def collectDue
    (tick : LogicalTick) :
    List (ScheduledIntent Intent) →
      List (ScheduledIntent Intent) × List (ScheduledIntent Intent)
  | [] => ([], [])
  | intent :: rest =>
      let collected := collectDue tick rest
      if intent.executeAt.value ≤ tick.value then
        (intent :: collected.1, collected.2)
      else
        (collected.1, intent :: collected.2)

/-- Retaining future intents never introduces a new scheduled value. -/
theorem collectDue_future_sublist
    (tick : LogicalTick)
    (intents : List (ScheduledIntent Intent)) :
    List.Sublist (collectDue tick intents).2 intents := by
  induction intents with
  | nil => simp [collectDue]
  | cons intent rest ih =>
      simp only [collectDue]
      split
      · exact ih.cons intent
      · exact ih.cons_cons intent

/-- A proof-carrying accepted application transition. -/
structure AppliedIntent
    (State Receipt : Type)
    (replay : Receipt → State → State)
    (before : State) where
  after : State
  receipt : Receipt
  replayExact : replay receipt before = after

/--
The application boundary used by the scheduler. Games own intent assessment,
state transitions, issues, receipts, and replay.
-/
structure IntentExecutor
    (State Intent Issue Receipt : Type) where
  replay : Receipt → State → State
  apply : (before : State) → Intent →
    Except (List Issue) (AppliedIntent State Receipt replay before)

/-- Why an eligible scheduled intent did not commit. -/
inductive IntentRejectionKind where
  | invalidAtSnapshot
  | lostConflict
  deriving DecidableEq, Repr

/-- Immutable result payload for one due intent. -/
inductive IntentEventOutcome (Issue Receipt : Type) where
  | accepted (receipt : Receipt)
  | rejected (kind : IntentRejectionKind) (issues : List Issue)

/-- One immutable, causally ordered timeline event. -/
structure TimelineEvent (Issue Receipt : Type) where
  sequence : Nat
  tick : LogicalTick
  intentId : IntentId
  arbitration : ArbitrationKey
  outcome : IntentEventOutcome Issue Receipt

def replayTimelineEvent
    (executor : IntentExecutor State Intent Issue Receipt)
    (event : TimelineEvent Issue Receipt)
    (state : State) : State :=
  match event.outcome with
  | .accepted receipt => executor.replay receipt state
  | .rejected _ _ => state

def replayTimelineEvents
    (executor : IntentExecutor State Intent Issue Receipt)
    (events : List (TimelineEvent Issue Receipt))
    (state : State) : State :=
  events.foldl (fun current event => replayTimelineEvent executor event current) state

@[simp]
theorem replayTimelineEvent_rejected
    (executor : IntentExecutor State Intent Issue Receipt)
    (event : TimelineEvent Issue Receipt)
    (state : State)
    (kind : IntentRejectionKind)
    (issues : List Issue)
    (rejected : event.outcome = .rejected kind issues) :
    replayTimelineEvent executor event state = state := by
  simp [replayTimelineEvent, rejected]

theorem replayTimelineEvents_append
    (executor : IntentExecutor State Intent Issue Receipt)
    (left right : List (TimelineEvent Issue Receipt))
    (state : State) :
    replayTimelineEvents executor (left ++ right) state =
      replayTimelineEvents executor right
        (replayTimelineEvents executor left state) := by
  simp [replayTimelineEvents, List.foldl_append]

private structure AppliedIntentRun
    (executor : IntentExecutor State Intent Issue Receipt)
    (before : State) where
  after : State
  events : List (TimelineEvent Issue Receipt)
  nextSequence : Nat
  replayExact : replayTimelineEvents executor events before = after

/-
All due intents are first assessed against `snapshot`. Snapshot-invalid intents
reject immediately. Eligible intents then apply in canonical order against the
tentative successor; a later failure is a conflict loss.
-/
private def applyOrderedIntents
    (executor : IntentExecutor State Intent Issue Receipt)
    (snapshot : State)
    (tick : LogicalTick) :
    (sequence : Nat) →
    (before : State) →
    (intents : List (ScheduledIntent Intent)) →
      AppliedIntentRun executor before
  | sequence, before, [] =>
      { after := before
        events := []
        nextSequence := sequence
        replayExact := rfl }
  | sequence, before, intent :: rest =>
      match executor.apply snapshot intent.payload with
      | .error snapshotIssues =>
          let suffix := applyOrderedIntents executor snapshot tick
            (sequence + 1) before rest
          let event : TimelineEvent Issue Receipt :=
            { sequence
              tick
              intentId := intent.id
              arbitration := intent.arbitration
              outcome := .rejected .invalidAtSnapshot snapshotIssues }
          { after := suffix.after
            events := event :: suffix.events
            nextSequence := suffix.nextSequence
            replayExact := by
              change replayTimelineEvents executor suffix.events before = suffix.after
              exact suffix.replayExact }
      | .ok _ =>
          match executor.apply before intent.payload with
          | .error conflictIssues =>
              let suffix := applyOrderedIntents executor snapshot tick
                (sequence + 1) before rest
              let event : TimelineEvent Issue Receipt :=
                { sequence
                  tick
                  intentId := intent.id
                  arbitration := intent.arbitration
                  outcome := .rejected .lostConflict conflictIssues }
              { after := suffix.after
                events := event :: suffix.events
                nextSequence := suffix.nextSequence
                replayExact := by
                  change replayTimelineEvents executor suffix.events before = suffix.after
                  exact suffix.replayExact }
          | .ok applied =>
              let suffix := applyOrderedIntents executor snapshot tick
                (sequence + 1) applied.after rest
              let event : TimelineEvent Issue Receipt :=
                { sequence
                  tick
                  intentId := intent.id
                  arbitration := intent.arbitration
                  outcome := .accepted applied.receipt }
              { after := suffix.after
                events := event :: suffix.events
                nextSequence := suffix.nextSequence
                replayExact := by
                  change replayTimelineEvents executor suffix.events
                      (executor.replay applied.receipt before) = suffix.after
                  rw [applied.replayExact]
                  exact suffix.replayExact }

/-- Authoritative scheduled application state. -/
structure TimelineState (State Intent : Type) where
  tick : LogicalTick
  application : State
  pending : List (ScheduledIntent Intent)
  pendingIdsUnique : (pending.map fun intent => intent.id).Nodup
  nextEventSequence : Nat

namespace TimelineState

def schedule
    (state : TimelineState State Intent)
    (intent : ScheduledIntent Intent)
    (fresh : intent.id ∉ state.pending.map fun pending => pending.id) :
    TimelineState State Intent :=
  { state with
      pending := state.pending ++ [intent]
      pendingIdsUnique := by
        simp only [List.map_append, List.map_cons, List.map_nil]
        apply List.nodup_append.mpr
        refine ⟨state.pendingIdsUnique, by simp, ?_⟩
        intro existing existingMem appended appendedMem
        simp only [List.mem_singleton] at appendedMem
        subst appended
        intro same
        apply fresh
        simpa [same] using existingMem }

end TimelineState

/-- Proof-carrying result of advancing one modeled tick. -/
structure AppliedTick
    (executor : IntentExecutor State Intent Issue Receipt)
    (before : TimelineState State Intent) where
  after : TimelineState State Intent
  processed : List (ScheduledIntent Intent)
  events : List (TimelineEvent Issue Receipt)
  tickAdvanced : after.tick = before.tick.succ
  replayExact :
    replayTimelineEvents executor events before.application = after.application

/-- Advance exactly one modeled tick. -/
def applyTick
    (executor : IntentExecutor State Intent Issue Receipt)
    (before : TimelineState State Intent) : AppliedTick executor before :=
  let collected := collectDue before.tick before.pending
  let due := orderScheduledIntents collected.1
  let run := applyOrderedIntents executor before.application before.tick
    before.nextEventSequence before.application due
  { after :=
      { tick := before.tick.succ
        application := run.after
        pending := collected.2
        pendingIdsUnique := by
          exact List.Nodup.sublist
            ((collectDue_future_sublist before.tick before.pending).map _)
            before.pendingIdsUnique
        nextEventSequence := run.nextSequence }
    processed := due
    events := run.events
    tickAdvanced := rfl
    replayExact := run.replayExact }

@[simp]
theorem applyTick_tick
    (executor : IntentExecutor State Intent Issue Receipt)
    (before : TimelineState State Intent) :
    (applyTick executor before).after.tick = before.tick.succ :=
  (applyTick executor before).tickAdvanced

theorem applyTick_events_replay
    (executor : IntentExecutor State Intent Issue Receipt)
    (before : TimelineState State Intent) :
    replayTimelineEvents executor (applyTick executor before).events
        before.application =
      (applyTick executor before).after.application :=
  (applyTick executor before).replayExact

/-- Fixed application state, pending intents, and executor have one pure result. -/
theorem applyTick_deterministic
    (executor : IntentExecutor State Intent Issue Receipt)
    (before : TimelineState State Intent)
    (left right : AppliedTick executor before)
    (leftExact : left = applyTick executor before)
    (rightExact : right = applyTick executor before) :
    left.after = right.after := by
  rw [leftExact, rightExact]

end Maquina
