import FoundrySim.Showcase
import NightglassSim.Showcase
import VeiledAccordSim.Showcase
import MaquinaViz

/-! Build-time exporter for the static, catalog-driven visualization site. -/

open Lean

namespace Maquina.Visualization.Export

def catalog : ShowcaseCatalog where
  schemaVersion := protocolVersion
  entries :=
    [{ id := "veiled-accord"
       gameId := "veiled accord"
       title := "Operation Veiled Accord"
       summary :=
         "Asymmetric information, cheap talk, costly signals, escrow, sealed orders, cooperation, and betrayal."
       artifact := "generated/veiled-accord.v4.json"
       capability := "commandable" },
     { id := "nightglass-extraction"
       gameId := "nightglass"
       title := "Operation Nightglass"
       summary :=
         "Targeting-channel contention, convoy damage, repair, and deterministic extraction."
       artifact := "generated/nightglass-extraction.v4.json"
       capability := "both" },
     { id := "foundry-control-room"
       gameId := "foundry"
       title := "Foundry Control Room"
       summary :=
         "Command two service lines through contention, backpressure, production, maintenance, and recovery."
       artifact := "generated/foundry-control-room.v4.json"
       capability := "commandable" },
     { id := "foundry-workcell-body-contention"
       gameId := "foundry"
       title := "Shared-account Body contention"
       summary :=
         "Foundry-owned workcell stations contend for one unique Body in a shared account state."
       artifact := "generated/foundry-workcell-body-contention.v4.json"
       capability := "trace" },
     { id := "foundry-refuel-lifecycle"
       gameId := "foundry"
       title := "Refuel lifecycle"
       summary :=
         "Body presence, custody, queue progression, completion, and collection."
       artifact := "generated/foundry-refuel-lifecycle.v4.json"
       capability := "trace" },
     { id := "foundry-operating-guards"
       gameId := "foundry"
       title := "Proof-carrying operating guards"
       summary :=
         "Structured evidence for idle and active machine conditions."
       artifact := "generated/foundry-operating-guards.v4.json"
       capability := "trace" },
     { id := "foundry-active-presence"
       gameId := "foundry"
       title := "Active presence boundary"
       summary :=
         "Accepted and rejected operations around a continuously held Body session."
       artifact := "generated/foundry-active-presence.v4.json"
       capability := "trace" }]

private def writeJson [ToJson α] (path : System.FilePath) (value : α) : IO Unit :=
  IO.FS.writeFile path ((toJson value).pretty ++ "\n")

def writeAll (directory : System.FilePath) : IO Unit := do
  IO.FS.createDirAll directory
  writeJson (directory / "catalog.v4.json") catalog
  let artifacts := Maquina.Games.Foundry.Showcase.artifacts
  match artifacts with
  | [refuel, presence, guards, workcell, controlRoom] =>
      writeJson (directory / "foundry-refuel-lifecycle.v4.json") refuel
      writeJson (directory / "foundry-active-presence.v4.json") presence
      writeJson (directory / "foundry-operating-guards.v4.json") guards
      writeJson (directory / "foundry-workcell-body-contention.v4.json")
        workcell
      writeJson (directory / "foundry-control-room.v4.json") controlRoom
  | _ => throw <| IO.userError "Foundry showcase registry does not match the catalog"
  writeJson (directory / "nightglass-extraction.v4.json")
    Maquina.Games.Nightglass.Showcase.artifact
  writeJson (directory / "veiled-accord.v4.json")
    Maquina.Games.VeiledAccord.Showcase.artifact

end Maquina.Visualization.Export

def main (args : List String) : IO Unit := do
  let directory : System.FilePath :=
    match args with
    | path :: _ => path
    | [] => "visualizer/public/generated"
  Maquina.Visualization.Export.writeAll directory
  IO.println s!"Exported Maquina showcases to {directory}"
