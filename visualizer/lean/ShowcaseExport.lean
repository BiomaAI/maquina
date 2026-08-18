import FoundrySim.Showcase
import MaquinaViz

/-! Build-time exporter for the static, catalog-driven visualization site. -/

open Lean

namespace Maquina.Visualization.Export

def catalog : ShowcaseCatalog where
  schemaVersion := protocolVersion
  entries :=
    [{ id := "foundry-refuel-lifecycle"
       gameId := "foundry"
       title := "Refuel lifecycle"
       summary :=
         "Body presence, custody, queue progression, completion, and collection."
       artifact := "generated/foundry-refuel-lifecycle.v2.json" },
     { id := "foundry-active-presence"
       gameId := "foundry"
       title := "Active presence boundary"
       summary :=
         "Accepted and rejected operations around a continuously held Body session."
       artifact := "generated/foundry-active-presence.v2.json" },
     { id := "foundry-operating-guards"
       gameId := "foundry"
       title := "Proof-carrying operating guards"
       summary :=
         "Structured evidence for idle and active machine conditions."
       artifact := "generated/foundry-operating-guards.v2.json" }]

private def writeJson [ToJson α] (path : System.FilePath) (value : α) : IO Unit :=
  IO.FS.writeFile path ((toJson value).pretty ++ "\n")

def writeAll (directory : System.FilePath) : IO Unit := do
  IO.FS.createDirAll directory
  writeJson (directory / "catalog.v2.json") catalog
  let artifacts := Maquina.Games.Foundry.Showcase.artifacts
  match artifacts with
  | [refuel, presence, guards] =>
      writeJson (directory / "foundry-refuel-lifecycle.v2.json") refuel
      writeJson (directory / "foundry-active-presence.v2.json") presence
      writeJson (directory / "foundry-operating-guards.v2.json") guards
  | _ => throw <| IO.userError "Foundry showcase registry does not match the catalog"

end Maquina.Visualization.Export

def main (args : List String) : IO Unit := do
  let directory : System.FilePath :=
    match args with
    | path :: _ => path
    | [] => "visualizer/public/generated"
  Maquina.Visualization.Export.writeAll directory
  IO.println s!"Exported Maquina showcases to {directory}"
