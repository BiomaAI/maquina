import Maquina

/-!
# Foundry

The first game-owned vocabulary for a formal game simulation over Maquina.
The generic machine kernel must not learn any of these domain-specific names.
-/

namespace Maquina.Games.Foundry

/-- Stable operating conditions chosen by the Foundry game. -/
inductive Mode where
  | off
  | running
  | broken
  deriving DecidableEq, Repr

/-
The source and destination indices encode the game's static operation graph.
For example, `smelt` can only be constructed from `running` to `running`.
-/
inductive Operation : Mode → Mode → Type where
  | start : Operation .off .running
  | smelt : Operation .running .running
  | stop : Operation .running .off
  | fail : Operation .running .broken
  | repair : Operation .broken .off
  deriving Repr

/-- There is no Foundry operation that remains in `off` while doing work. -/
theorem noOperationFromOffToOff : ¬ Nonempty (Operation .off .off) := by
  intro possible
  obtain ⟨operation⟩ := possible
  cases operation

/-- There is no Foundry operation that remains in `broken` while doing work. -/
theorem noOperationFromBrokenToBroken :
    ¬ Nonempty (Operation .broken .broken) := by
  intro possible
  obtain ⟨operation⟩ := possible
  cases operation

/-- Smelting is constructible precisely at the game-defined running mode. -/
def smeltOperation : Operation .running .running := .smelt

/-! ## First use of the generic Maquina queue -/

/-- Foundry chooses its input capacity; the queue semantics come from Maquina. -/
def inputQueue : Queue (Operation .running .running) :=
  Queue.empty (some 2)

example :
    (Queue.assessAndEnqueue inputQueue smeltOperation).isSome = true := by
  native_decide

end Maquina.Games.Foundry
