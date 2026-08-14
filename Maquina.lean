import Std

/-!
# Maquina

The initial object, quantity, and supply model for Maquina's formal
specification.
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

/-! ## Proof-carrying supply and allocations -/

/-- The type of legal global supply for an object specification. -/
def Supply (spec : ObjectSpec) : Type :=
  match spec.limit with
  | .unbounded => Quantity
  | .bounded maximum _ =>
      { current : Quantity // current.atoms ≤ maximum.atoms }

/-- One nonzero entry in a finite sparse object allocation. -/
structure Balance (Account : Type) where
  account : Account
  quantity : Quantity
  positive : 0 < quantity.atoms

/-- A finite sparse allocation with at most one balance per account. -/
structure Allocation (Account : Type) where
  balances : List (Balance Account)
  accountsUnique : (balances.map Balance.account).Nodup

def totalAtoms {Account : Type} (allocation : Allocation Account) : Nat :=
  (allocation.balances.map fun balance => balance.quantity.atoms).sum

/-- The actual account allocation respects the object's declared global limit. -/
def RespectsLimit {Account : Type}
    (spec : ObjectSpec)
    (allocation : Allocation Account) : Prop :=
  match spec.limit with
  | .unbounded => True
  | .bounded maximum _ => totalAtoms allocation ≤ maximum.atoms

/-- Account balances for one object, carrying their global-limit proof. -/
structure ObjectState (Account : Type) (spec : ObjectSpec) where
  allocation : Allocation Account
  respectsLimit : RespectsLimit spec allocation

namespace ObjectState

/-- The total of a valid allocation is itself a legal supply value. -/
def supply {Account : Type} {spec : ObjectSpec}
    (state : ObjectState Account spec) : Supply spec := by
  unfold Supply
  cases limitEq : spec.limit with
  | unbounded =>
      exact ⟨totalAtoms state.allocation⟩
  | bounded maximum _ =>
      refine ⟨⟨totalAtoms state.allocation⟩, ?_⟩
      simpa [RespectsLimit, limitEq] using state.respectsLimit

/-- Every bounded object state satisfies its declared global maximum. -/
theorem bounded_total_le {Account : Type} {spec : ObjectSpec}
    (maximum : Quantity)
    (positive : 0 < maximum.atoms)
    (limitEq : spec.limit = .bounded maximum positive)
    (state : ObjectState Account spec) :
    totalAtoms state.allocation ≤ maximum.atoms := by
  simpa [RespectsLimit, limitEq] using state.respectsLimit

/-- A unique object's allocation can contain at most one atom globally. -/
theorem unique_total_le_one {Account : Type}
    (header : ObjectHeader)
    (state : ObjectState Account (ObjectSpec.unique header)) :
    totalAtoms state.allocation ≤ 1 :=
  state.respectsLimit

/-- An edition's allocation cannot exceed its declared number of copies. -/
theorem edition_total_le_max {Account : Type}
    (header : ObjectHeader)
    (maxCopies : Nat)
    (positive : 0 < maxCopies)
    (state : ObjectState Account (ObjectSpec.edition header maxCopies positive)) :
    totalAtoms state.allocation ≤ maxCopies :=
  state.respectsLimit

end ObjectState

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
