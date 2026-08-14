import Std

/-!
# Maquina Objects

The object, quantity, and supply foundation for Maquina's formal specification.
-/

namespace Maquina

structure ObjectId where
  value : Nat
  deriving DecidableEq, Repr

structure ObjectHeader where
  id : ObjectId
  name : String
  deriving Repr

/-! ## Exact authoritative quantities -/

/-- A quantity is an exact, nonnegative count of an object's canonical atoms. -/
structure Quantity where
  atoms : Nat
  deriving DecidableEq, Repr

namespace Quantity

def zero : Quantity := ⟨0⟩

def one : Quantity := ⟨1⟩

def add (left right : Quantity) : Quantity :=
  ⟨left.atoms + right.atoms⟩

end Quantity

/-! ## Measurement definitions -/

/-- A physical dimension represented by the seven ISQ base-dimension exponents. -/
structure Dimension where
  lengthExp : Int := 0
  massExp : Int := 0
  timeExp : Int := 0
  electricCurrentExp : Int := 0
  thermodynamicTemperatureExp : Int := 0
  amountOfSubstanceExp : Int := 0
  luminousIntensityExp : Int := 0
  deriving DecidableEq, Repr

namespace Dimension

def dimensionless : Dimension := {}
def length : Dimension := { lengthExp := 1 }
def mass : Dimension := { massExp := 1 }
def time : Dimension := { timeExp := 1 }
def volume : Dimension := { lengthExp := 3 }

end Dimension

/--
A stable semantic distinction between measurements. Distinct kinds may share
the same physical dimension, as energy and torque do.
-/
inductive MeasureKind where
  | plain
  | named (domain : String) (name : String)
  deriving DecidableEq, Repr

/-- A rational value known to be strictly positive. -/
structure PositiveRat where
  value : Rat
  positive : 0 < value
  deriving Repr

/-- The authoritative definition of one canonical object atom. -/
inductive ObjectDefinition where
  | discrete
  | measured
      (dimension : Dimension)
      (kind : MeasureKind)
      (atomicBase : PositiveRat)
  deriving Repr

/-- An optional, strictly positive global maximum expressed in object atoms. -/
inductive SupplyLimit where
  | unbounded
  | bounded (maximum : Quantity) (positive : 0 < maximum.atoms)
  deriving Repr

/--
An object specification defines identity, the meaning of one atom, and its
optional global supply limit. Fungibility is derived from identity and supply:
equal IDs aggregate; unique objects use distinct IDs with a unit limit.
-/
structure ObjectSpec where
  header : ObjectHeader
  definition : ObjectDefinition
  limit : SupplyLimit
  deriving Repr

namespace ObjectSpec

def discrete
    (header : ObjectHeader)
    (limit : SupplyLimit := .unbounded) : ObjectSpec :=
  { header, definition := .discrete, limit }

def measured
    (header : ObjectHeader)
    (dimension : Dimension)
    (kind : MeasureKind)
    (atomicBase : PositiveRat)
    (limit : SupplyLimit := .unbounded) : ObjectSpec :=
  { header, definition := .measured dimension kind atomicBase, limit }

/-- A unique object is a discrete object with its own ID and global limit one. -/
def unique (header : ObjectHeader) : ObjectSpec :=
  discrete header (.bounded .one (by decide))

/-- An edition is one identity with a positive bounded number of copies. -/
def edition
    (header : ObjectHeader)
    (maxCopies : Nat)
    (positive : 0 < maxCopies) : ObjectSpec :=
  discrete header (.bounded ⟨maxCopies⟩ positive)

@[simp]
theorem unique_definition (header : ObjectHeader) :
    (unique header).definition = .discrete := rfl

@[simp]
theorem unique_maximum (header : ObjectHeader) :
    (unique header).limit = .bounded .one (by decide) := rfl

@[simp]
theorem edition_definition
    (header : ObjectHeader)
    (maxCopies : Nat)
    (positive : 0 < maxCopies) :
    (edition header maxCopies positive).definition = .discrete := rfl

end ObjectSpec

/-! ## Proof-carrying supply -/

/-- The type of legal global supply for an object specification. -/
def Supply (spec : ObjectSpec) : Type :=
  match spec.limit with
  | .unbounded => Quantity
  | .bounded maximum _ =>
      { current : Quantity // current.atoms ≤ maximum.atoms }

/-! ## Coherent object catalogs -/

/-- A catalog is authoritative: every logical ID resolves to at most one specification. -/
structure Catalog where
  lookup : ObjectId → Option ObjectSpec
  idMatches : ∀ {id spec}, lookup id = some spec → spec.header.id = id

namespace Catalog

/-- One logical ID cannot resolve to two conflicting object specifications. -/
theorem spec_unique (catalog : Catalog) {id : ObjectId} {left right : ObjectSpec}
    (leftFound : catalog.lookup id = some left)
    (rightFound : catalog.lookup id = some right) :
    left = right := by
  exact Option.some.inj (leftFound.symm.trans rightFound)

/-- In particular, one logical ID cannot carry two conflicting atom definitions. -/
theorem definition_unique (catalog : Catalog) {id : ObjectId} {left right : ObjectSpec}
    (leftFound : catalog.lookup id = some left)
    (rightFound : catalog.lookup id = some right) :
    left.definition = right.definition := by
  exact congrArg ObjectSpec.definition
    (catalog.spec_unique leftFound rightFound)

end Catalog

end Maquina
