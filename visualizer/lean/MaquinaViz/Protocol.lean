import Lean.Data.Json

/-!
# Maquina Visualization Protocol

Versioned, proof-erased data transferred from Lean simulations to presentation
clients. The protocol contains Maquina concepts and generic scene hints; it
contains no vocabulary from a particular game.
-/

namespace Maquina.Visualization

open Lean

/-- Semantic natural numbers cross the JavaScript boundary as exact decimals. -/
abbrev ExactNat := String

def exactNat (value : Nat) : ExactNat := toString value

structure Vec3 where
  x : Float
  y : Float
  z : Float
  deriving ToJson

structure ThemeView where
  background : String
  surface : String
  accent : String
  deriving ToJson

structure ResourceStyle where
  id : String
  label : String
  symbol : String
  color : String
  geometry : String
  unit : Option String := none
  deriving ToJson

structure AccountStyle where
  id : String
  label : String
  kind : String
  color : String
  position : Vec3
  deriving ToJson

structure MachineStyle where
  id : String
  label : String
  color : String
  position : Vec3
  deriving ToJson

structure CameraStyle where
  position : Vec3
  target : Vec3
  deriving ToJson

/-- Game-owned declarative appearance; the renderer remains game-independent. -/
structure PresentationView where
  theme : ThemeView
  resources : List ResourceStyle
  accounts : List AccountStyle
  machines : List MachineStyle
  camera : CameraStyle
  deriving ToJson

structure HoldingView where
  account : String
  resource : String
  quantity : ExactNat
  deriving ToJson

structure ResourceAmountView where
  resource : String
  quantity : ExactNat
  deriving ToJson

structure ProcessView where
  ticket : ExactNat
  id : String
  kind : String
  progress : ExactNat
  requiredWork : ExactNat
  deriving ToJson

structure QueueView where
  id : String
  stage : String
  capacity : Option ExactNat
  entries : List ProcessView
  deriving ToJson

structure MachineView where
  id : String
  inventory : String
  mode : String
  maximumQueues : ExactNat
  queues : List QueueView
  deriving ToJson

structure CustodyPositionView where
  id : String
  source : String
  destination : String
  contents : List ResourceAmountView
  active : Bool
  deriving ToJson

structure StateView where
  holdings : List HoldingView
  machines : List MachineView
  custody : List CustodyPositionView
  nextProcessId : ExactNat
  deriving ToJson

structure ObservationView where
  account : String
  resource : String
  required : ExactNat
  available : ExactNat
  deriving ToJson

structure MovementView where
  source : String
  destination : String
  resource : String
  quantity : ExactNat
  sourceBefore : ExactNat
  sourceAfter : ExactNat
  destinationBefore : ExactNat
  destinationAfter : ExactNat
  deriving ToJson

structure BalanceChangeView where
  direction : String
  account : String
  resource : String
  quantity : ExactNat
  accountBefore : ExactNat
  accountAfter : ExactNat
  totalBefore : ExactNat
  totalAfter : ExactNat
  deriving ToJson

/--
One generic simulator effect. Optional scalar coordinates keep the protocol
extensible while the structured observations, movements, and changes retain
the exact resource data needed for faithful presentation.
-/
structure EffectView where
  kind : String
  stage : Option String := none
  sourceQueue : Option String := none
  destinationQueue : Option String := none
  process : Option String := none
  ticket : Option ExactNat := none
  before : Option ExactNat := none
  after : Option ExactNat := none
  position : Option String := none
  positions : List String := []
  account : Option String := none
  remaining : Option ExactNat := none
  disposition : Option String := none
  observations : List ObservationView := []
  movements : List MovementView := []
  changes : List BalanceChangeView := []
  deriving ToJson

structure IssueView where
  code : String
  detail : String
  deriving ToJson

/-- A non-mutating precondition check, distinct from transition effects. -/
structure CheckView where
  kind : String
  condition : String
  status : String
  detail : String
  requirementIndex : Option Nat := none
  account : Option String := none
  observations : List ObservationView := []
  issues : List IssueView := []
  deriving ToJson

structure StepView where
  index : Nat
  operation : String
  trigger : String
  status : String
  semanticStatus : String
  before : StateView
  after : StateView
  checks : List CheckView
  effects : List EffectView
  issues : List IssueView
  deriving ToJson

structure ProvenanceView where
  engine : String
  toolchain : String
  guarantees : List String
  deriving ToJson

structure ScenarioArtifact where
  schemaVersion : Nat
  id : String
  gameId : String
  title : String
  summary : String
  presentation : PresentationView
  provenance : ProvenanceView
  initial : StateView
  steps : List StepView
  deriving ToJson

structure CatalogEntry where
  id : String
  gameId : String
  title : String
  summary : String
  artifact : String
  deriving ToJson

structure ShowcaseCatalog where
  schemaVersion : Nat
  entries : List CatalogEntry
  deriving ToJson

def protocolVersion : Nat := 2

def leanProvenance : ProvenanceView where
  engine := "lean"
  toolchain := "leanprover/lean4:v4.33.0"
  guarantees :=
    ["accepted guards carry evidence for every declared condition",
     "rejected guards expose the exact exhaustive issue list",
     "accepted effects replay to the exact successor holdings",
     "direct receipts replay to the exact successor simulator data",
     "rejected operations expose no successor state"]

end Maquina.Visualization
