import Std

/-!
# Maquina Accounts

Stable account identities. An `AccountId` is valid by construction; account
existence is not mediated by a registry.
-/

namespace Maquina

/-- Stable identity of an account that may hold objects. -/
structure AccountId where
  value : Nat
  deriving DecidableEq, Repr

end Maquina
