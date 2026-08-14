import Std

/-!
# Maquina Accounts

Stable account identities and the authoritative account catalog.
-/

namespace Maquina

/-- Stable identity of an account that may hold objects. -/
structure AccountId where
  value : Nat
  deriving DecidableEq, Repr

/-- The authoritative catalog entry for one account identity. -/
structure AccountSpec where
  id : AccountId
  name : String
  deriving Repr

/-!
An account catalog is authoritative: a successful lookup must return a
specification carrying exactly the requested identity.
-/
structure AccountCatalog where
  lookup : AccountId → Option AccountSpec
  idMatches : ∀ {id spec}, lookup id = some spec → spec.id = id

namespace AccountCatalog

/-- One catalog identity cannot resolve to two different account entries. -/
theorem spec_unique
    (catalog : AccountCatalog)
    {id : AccountId}
    {left right : AccountSpec}
    (leftFound : catalog.lookup id = some left)
    (rightFound : catalog.lookup id = some right) :
  left = right := by
  rw [leftFound] at rightFound
  exact Option.some.inj rightFound

/-- Proposition that an account identity resolves in the catalog. -/
def Known (catalog : AccountCatalog) (id : AccountId) : Prop :=
  ∃ spec, catalog.lookup id = some spec

end AccountCatalog

end Maquina
