import Std

/-!
# Maquina

The initial object and quantity model for Maquina's formal specification.
-/

namespace Maquina

structure ObjectId where
  value : Nat
  deriving DecidableEq, Repr

structure ObjectHeader where
  id : ObjectId
  name : String
  deriving Repr

/-- A physical dimension represented by exponents of its base dimensions. -/
structure Dimension where
  lengthExp : Int := 0
  massExp : Int := 0
  timeExp : Int := 0
  deriving DecidableEq, Repr

namespace Dimension

def length : Dimension := { lengthExp := 1 }
def mass : Dimension := { massExp := 1 }
def time : Dimension := { timeExp := 1 }
def volume : Dimension := { lengthExp := 3 }

end Dimension

/-- The way an object's inventory is quantified. -/
inductive MeasureKind where
  | discrete
  | metric (dimension : Dimension)
  deriving DecidableEq, Repr

/-- An exact, nonnegative metric quantity in canonical base units. -/
structure MetricAmount (dimension : Dimension) where
  baseUnits : Rat
  nonnegative : 0 ≤ baseUnits
  deriving Repr

def Quantity : MeasureKind → Type
  | .discrete => Nat
  | .metric dimension => MetricAmount dimension

def quantityLE {measure : MeasureKind} :
    Quantity measure → Quantity measure → Prop :=
  match measure with
  | .discrete => Nat.le
  | .metric _ => fun a b => a.baseUnits ≤ b.baseUnits

/-- A valid object identity and supply model. -/
inductive ObjectSpec where
  /-- An interchangeable quantity, optionally bounded by a global maximum. -/
  | fungible
      (header : ObjectHeader)
      (measure : MeasureKind)
      (maximum : Option (Quantity measure))
  /-- One globally unique object. -/
  | unique (header : ObjectHeader)
  /-- A bounded edition whose copies are interchangeable within the edition. -/
  | edition
      (header : ObjectHeader)
      (maxCopies : Nat)
      (positive : 0 < maxCopies)

/-- The type of legal global supply for an object specification. -/
def Supply : ObjectSpec → Type
  | .fungible _ measure none => Quantity measure
  | .fungible _ measure (some maximum) =>
      { current : Quantity measure // quantityLE current maximum }
  | .unique _ => Fin 2
  | .edition _ maxCopies _ => Fin (maxCopies + 1)

end Maquina
