import VeiledAccordSim.Showcase

open Lean

def main : IO Unit := do
  IO.println (toJson Maquina.Games.VeiledAccord.Showcase.artifact).pretty
