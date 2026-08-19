import Maquina.Transformation

/-!
# Maquina Account Transactions

Atomic resource changes across arbitrary inventory accounts. Transactions are
defined entirely in terms of accounts and resources: machines may request a
transaction, but they are never part of its identity or execution semantics.

Debit and credit legs are separated so implementation order is canonical. A
transaction is normalized at the account/resource-key level: no key may occur
twice or on both sides of the transaction.
-/

namespace Maquina

/-- One normalized decrease of an account/resource balance. -/
structure AccountDebit where
  account : AccountId
  entry : BasketEntry
  deriving Repr

/-- One normalized increase of an account/resource balance. -/
structure AccountCredit where
  account : AccountId
  entry : BasketEntry
  deriving Repr

namespace AccountDebit

def key (debit : AccountDebit) : AccountId × ResourceId :=
  (debit.account, debit.entry.resourceId)

def delta (debit : AccountDebit) : InventoryDelta :=
  .debit debit.account debit.entry

end AccountDebit

namespace AccountCredit

def key (credit : AccountCredit) : AccountId × ResourceId :=
  (credit.account, credit.entry.resourceId)

def delta (credit : AccountCredit) : InventoryDelta :=
  .credit credit.account credit.entry

end AccountCredit

/--
An inert, normalized multi-account transaction. Opposing changes to the same
account/resource key must be netted before constructing this value.
-/
structure AccountTransaction where
  debits : List AccountDebit
  credits : List AccountCredit
  debitKeysUnique : (debits.map AccountDebit.key).Nodup
  creditKeysUnique : (credits.map AccountCredit.key).Nodup
  directionsDisjoint :
    ∀ debit ∈ debits, ∀ credit ∈ credits, debit.key ≠ credit.key
  deriving Repr

namespace AccountTransaction

def empty : AccountTransaction where
  debits := []
  credits := []
  debitKeysUnique := by simp
  creditKeysUnique := by simp
  directionsDisjoint := by simp

/-- Canonical implementation program: every decrease precedes every increase. -/
def deltas (transaction : AccountTransaction) : List InventoryDelta :=
  transaction.debits.map AccountDebit.delta ++
    transaction.credits.map AccountCredit.delta

def accounts (transaction : AccountTransaction) : List AccountId :=
  (transaction.debits.map AccountDebit.account ++
    transaction.credits.map AccountCredit.account).eraseDups

end AccountTransaction

/-- A rejected transaction reports the underlying account/resource failure. -/
abbrev AccountTransactionIssue := InventoryDeltaIssue

/-- Proof-carrying result of committing one normalized account transaction. -/
abbrev AppliedAccountTransaction
    {resourceCatalog : ResourceCatalog}
    (before : WorldState resourceCatalog)
    (transaction : AccountTransaction) :=
  AppliedInventoryProgram before transaction.deltas

/-- Assess and commit every account leg atomically. -/
def applyAccountTransaction
    {resourceCatalog : ResourceCatalog}
    (before : WorldState resourceCatalog)
    (transaction : AccountTransaction) :
    Except (List AccountTransactionIssue)
      (AppliedAccountTransaction before transaction) :=
  applyInventoryProgram before transaction.deltas

/-- Rejections never expose a partially applied account state. -/
def accountTransactionSuccessor
    {resourceCatalog : ResourceCatalog}
    (before : WorldState resourceCatalog)
    (transaction : AccountTransaction) : Option (WorldState resourceCatalog) :=
  match applyAccountTransaction before transaction with
  | .error _ => none
  | .ok applied => some applied.after

theorem accountTransactionSuccessor_rejected
    {resourceCatalog : ResourceCatalog}
    (before : WorldState resourceCatalog)
    (transaction : AccountTransaction)
    (issues : List AccountTransactionIssue)
    (rejected : applyAccountTransaction before transaction = .error issues) :
    accountTransactionSuccessor before transaction = none := by
  simp [accountTransactionSuccessor, rejected]

/-- Every accepted transaction receipt replays to its exact successor holdings. -/
theorem AppliedAccountTransaction.replay_exact
    {resourceCatalog : ResourceCatalog}
    {before : WorldState resourceCatalog}
    {transaction : AccountTransaction}
    (applied : AppliedAccountTransaction before transaction) :
    replayInventoryProgram applied.receipts before.holdings =
      applied.after.holdings :=
  applied.replayExact

/-- A transaction cannot change an account/resource key it does not mention. -/
theorem AppliedAccountTransaction.balance_untouched
    {resourceCatalog : ResourceCatalog}
    {before : WorldState resourceCatalog}
    {transaction : AccountTransaction}
    (applied : AppliedAccountTransaction before transaction)
    (account : AccountId)
    (resourceId : ResourceId)
    (debitsUntouched : ∀ debit ∈ transaction.debits,
      debit.key ≠ (account, resourceId))
    (creditsUntouched : ∀ credit ∈ transaction.credits,
      credit.key ≠ (account, resourceId)) :
    (applied.after.balance account resourceId).atoms =
      (before.balance account resourceId).atoms := by
  apply AppliedInventoryProgram.balance_untouched applied
  intro delta deltaMem touched
  simp only [AccountTransaction.deltas, List.mem_append,
    List.mem_map] at deltaMem
  rcases deltaMem with ⟨debit, debitMem, debitExact⟩ |
      ⟨credit, creditMem, creditExact⟩
  · subst delta
    apply debitsUntouched debit debitMem
    exact Prod.ext touched.1 touched.2
  · subst delta
    apply creditsUntouched credit creditMem
    exact Prod.ext touched.1 touched.2

/-- A one-leg debit transaction constructor. -/
def AccountTransaction.debit
    (account : AccountId)
    (entry : BasketEntry) : AccountTransaction where
  debits := [{ account, entry }]
  credits := []
  debitKeysUnique := by simp
  creditKeysUnique := by simp
  directionsDisjoint := by simp

/-- A one-leg credit transaction constructor. -/
def AccountTransaction.credit
    (account : AccountId)
    (entry : BasketEntry) : AccountTransaction where
  debits := []
  credits := [{ account, entry }]
  debitKeysUnique := by simp
  creditKeysUnique := by simp
  directionsDisjoint := by simp

end Maquina
