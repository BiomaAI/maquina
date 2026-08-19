import NightglassSim

open Maquina
open Maquina.Games.Nightglass
open Maquina.Games.Nightglass.Simulation

def outcomeName : IntentEventOutcome Issue Receipt → String
  | .accepted _ => "accepted"
  | .rejected .invalidAtSnapshot _ => "invalid-at-snapshot"
  | .rejected .lostConflict _ => "lost-conflict"

def printTick
    (tick : Nat)
    (events : List (TimelineEvent Issue Receipt)) : IO Unit := do
  IO.println s!"tick {tick}"
  for event in events do
    IO.println s!"  event {event.sequence}, intent {event.intentId.value}: {outcomeName event.outcome}"

def main : IO Unit := do
  printTick 0 tickZero.events
  printTick 1 tickOne.events
  printTick 2 tickTwo.events
  printTick 3 tickThree.events
  printTick 4 tickFour.events
  printTick 5 tickFive.events
  printTick 6 tickSix.events
  printTick 7 tickSeven.events
  printTick 8 tickEight.events
  IO.println s!"mission: {repr (missionStatus finalTimeline)}"
