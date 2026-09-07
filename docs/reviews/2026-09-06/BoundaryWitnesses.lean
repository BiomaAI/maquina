import Maquina.Game
import VeiledAccordSim.Showcase

open Maquina
namespace Review

-- Regression: no accepted assessment can be fabricated for a rejecting executor.
def rejectAll : IntentExecutor Nat Nat String Nat where
  replay := fun receipt _ => receipt
  apply := fun _ _ => .error ["always rejected"]

example (assessed : AssessedCandidate Nat Nat String Nat rejectAll 0) :
    assessed.assessment.isAccepted = false := by
  have exactResult := assessed.assessmentExact
  cases outcome : assessed.assessment with
  | accepted applied => simp [outcome, rejectAll] at exactResult
  | rejected issues => rfl

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

def orders : OrderSet Nat where
  orders := [{ id := ⟨1⟩, actor := ⟨1⟩, arbitration := ⟨0, 0⟩, payload := 123 }]
  idsUnique := by simp

def resolved := resolveSnapshotOrderSet rejectAll 0 parent ⟨1⟩ rfl orders

def checkedStep := commandGraphStep rejectAll 0 parent resolved

-- The scheduler records the rejected order: it cannot be a phantom zero-event tick.
example : checkedStep.events.length = 1 := by native_decide
example : checkedStep.processed.length = 1 := by native_decide
example : checkedStep.child.timeline.application = 0 := by native_decide
example : checkedStep.events.map (·.intentId.value) = [1] := by native_decide

-- Regression: actual exported candidates now agree across the proved information set.
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
theorem exportedEffectsSafe : visibleEffects Command.claimNodeSnapshot.timeline.application =
    visibleEffects Command.hiddenPartnerAlternative := by native_decide
#print axioms exportedEffectsSafe
end ReviewLeak
