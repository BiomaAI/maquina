import Std

/-!
# Maquina Resources

The resource, quantity, and supply foundation for Maquina's formal specification.
-/

namespace Maquina

structure ResourceId where
  value : Nat
  deriving DecidableEq, Repr

structure ResourceHeader where
  id : ResourceId
  name : String
  deriving Repr

/-! ## Exact authoritative quantities -/

/-- A quantity is an exact, nonnegative count of a resource's canonical atoms. -/
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

/-- The authoritative definition of one canonical resource atom. -/
inductive ResourceDefinition where
  | discrete
  | measured
      (dimension : Dimension)
      (kind : MeasureKind)
      (atomicBase : PositiveRat)
  deriving Repr

/-- An optional, strictly positive global maximum expressed in resource atoms. -/
inductive SupplyLimit where
  | unbounded
  | bounded (maximum : Quantity) (positive : 0 < maximum.atoms)
  deriving Repr

/--
A resource specification defines identity, the meaning of one atom, and its
optional global supply limit. Fungibility is derived from identity and supply:
equal IDs aggregate; unique resources use distinct IDs with a unit limit.
-/
structure ResourceSpec where
  header : ResourceHeader
  definition : ResourceDefinition
  limit : SupplyLimit
  deriving Repr

namespace ResourceSpec

def discrete
    (header : ResourceHeader)
    (limit : SupplyLimit := .unbounded) : ResourceSpec :=
  { header, definition := .discrete, limit }

def measured
    (header : ResourceHeader)
    (dimension : Dimension)
    (kind : MeasureKind)
    (atomicBase : PositiveRat)
    (limit : SupplyLimit := .unbounded) : ResourceSpec :=
  { header, definition := .measured dimension kind atomicBase, limit }

/-- A unique resource is a discrete resource with its own ID and global limit one. -/
def unique (header : ResourceHeader) : ResourceSpec :=
  discrete header (.bounded .one (by decide))

/-- An edition is one identity with a positive bounded number of copies. -/
def edition
    (header : ResourceHeader)
    (maxCopies : Nat)
    (positive : 0 < maxCopies) : ResourceSpec :=
  discrete header (.bounded ⟨maxCopies⟩ positive)

@[simp]
theorem unique_definition (header : ResourceHeader) :
    (unique header).definition = .discrete := rfl

@[simp]
theorem unique_maximum (header : ResourceHeader) :
    (unique header).limit = .bounded .one (by decide) := rfl

@[simp]
theorem edition_definition
    (header : ResourceHeader)
    (maxCopies : Nat)
    (positive : 0 < maxCopies) :
    (edition header maxCopies positive).definition = .discrete := rfl

end ResourceSpec

/-! ## Proof-carrying supply -/

/-- The type of legal global supply for a resource specification. -/
def Supply (spec : ResourceSpec) : Type :=
  match spec.limit with
  | .unbounded => Quantity
  | .bounded maximum _ =>
      { current : Quantity // current.atoms ≤ maximum.atoms }

/-! ## Coherent resource catalogs -/

/--
A resource catalog is authoritative: every logical ID resolves to at most one
specification.
-/
structure ResourceCatalog where
  lookup : ResourceId → Option ResourceSpec
  idMatches : ∀ {id spec}, lookup id = some spec → spec.header.id = id

namespace ResourceCatalog

/-- The authoritative catalog containing exactly one resource specification. -/
def singleton (spec : ResourceSpec) : ResourceCatalog where
  lookup := fun id =>
    if id = spec.header.id then some spec else none
  idMatches := by
    intro id foundSpec found
    by_cases same : id = spec.header.id
    · simp only [same, ↓reduceIte] at found
      have specEq : spec = foundSpec := Option.some.inj found
      rw [← specEq, same]
    · simp [same] at found

@[simp]
theorem singleton_lookup_same (spec : ResourceSpec) :
    (singleton spec).lookup spec.header.id = some spec := by
  simp [singleton]

@[simp]
theorem singleton_lookup_other
    (spec : ResourceSpec)
    (id : ResourceId)
    (different : id ≠ spec.header.id) :
    (singleton spec).lookup id = none := by
  simp [singleton, different]

/-- One logical ID cannot resolve to two conflicting resource specifications. -/
theorem spec_unique
    (resourceCatalog : ResourceCatalog)
    {id : ResourceId}
    {left right : ResourceSpec}
    (leftFound : resourceCatalog.lookup id = some left)
    (rightFound : resourceCatalog.lookup id = some right) :
    left = right := by
  exact Option.some.inj (leftFound.symm.trans rightFound)

/-- In particular, one logical ID cannot carry two conflicting atom definitions. -/
theorem definition_unique
    (resourceCatalog : ResourceCatalog)
    {id : ResourceId}
    {left right : ResourceSpec}
    (leftFound : resourceCatalog.lookup id = some left)
    (rightFound : resourceCatalog.lookup id = some right) :
    left.definition = right.definition := by
  exact congrArg ResourceSpec.definition
    (resourceCatalog.spec_unique leftFound rightFound)

end ResourceCatalog

end Maquina
