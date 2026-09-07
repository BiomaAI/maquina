import Maquina.Game
import VeiledAccordSim.Showcase

open Maquina
namespace Review

-- A rejecting executor can still be paired with a fabricated accepted candidate.
def rejectAll : IntentExecutor Nat Nat String Nat where
  replay := fun receipt _ => receipt
  apply := fun _ _ => .error ["always rejected"]

def falseAcceptance : AssessedCandidate Nat Nat String Nat rejectAll 0 where
  candidate := { id := ⟨1⟩, actor := ⟨1⟩, payload := 7 }
  assessment := .accepted { after := 99, receipt := 99, replayExact := rfl }

example : falseAcceptance.assessment.isAccepted = true := rfl
example : (assessCandidate rejectAll 0 falseAcceptance.candidate).assessment.isAccepted = false := rfl

-- Public graph-step structure permits a processed order with no event at all.
def timeline : TimelineState Nat Nat where
  application := 0
  tick := ⟨0⟩
  pending := []
  pendingIdsUnique := by simp
  nextEventSequence := 0

def parent : TimelineSnapshot rejectAll 0 where
  id := ⟨0⟩
  timeline := timeline
  history := []
  replayExact := rfl

def child : TimelineSnapshot rejectAll 0 where
  id := ⟨1⟩
  timeline := { timeline with tick := ⟨1⟩ }
  history := []
  replayExact := rfl

def scheduled : ScheduledIntent Nat where
  id := ⟨1⟩
  submittedAt := ⟨0⟩
  executeAt := ⟨0⟩
  notBeforeSubmission := Nat.le_refl 0
  arbitration := ⟨0, 0⟩
  payload := 123

def phantomStep : CommandGraphStep rejectAll 0 where
  parent := parent
  child := child
  processed := [scheduled]
  events := []
  replayExact := rfl
  tickAdvanced := rfl
  historyExtended := rfl

example : initialCommandStepIntentIds [phantomStep] = canonicalCommandActionIds [⟨1⟩] := by native_decide
example : phantomStep.events = [] := rfl

-- Actual exported candidates differ across the existing proved information set.
open Maquina.Games.VeiledAccord Simulation
example : Command.commanderView Command.hiddenPartnerAlternative =
    Command.commanderView Command.claimNodeSnapshot.timeline.application := by native_decide
#eval (Showcase.projectCandidate Command.claimNodeSnapshot.timeline.application (Command.claimNode.candidates[0])).effects.length
end Review

namespace ReviewLeak
open Maquina.Games.VeiledAccord Simulation
def visibleEffects (state : State) : String :=
  reprStr ((Showcase.projectCandidate state (Command.claimNode.candidates[0])).effects.map fun effect =>
    effect.movements.map fun movement => (movement.destination, movement.quantity))
#eval visibleEffects Command.claimNodeSnapshot.timeline.application
#eval visibleEffects Command.hiddenPartnerAlternative
theorem exportedEffectsLeak : visibleEffects Command.claimNodeSnapshot.timeline.application ≠
    visibleEffects Command.hiddenPartnerAlternative := by native_decide
#print axioms exportedEffectsLeak
end ReviewLeak
