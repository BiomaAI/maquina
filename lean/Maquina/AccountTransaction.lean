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

def precedes (left right : AccountDebit) : Bool :=
  if left.account.value != right.account.value then
    decide (left.account.value < right.account.value)
  else
    decide (left.entry.resourceId.value < right.entry.resourceId.value)

end AccountDebit

namespace AccountCredit

def key (credit : AccountCredit) : AccountId × ResourceId :=
  (credit.account, credit.entry.resourceId)

def delta (credit : AccountCredit) : InventoryDelta :=
  .credit credit.account credit.entry

def precedes (left right : AccountCredit) : Bool :=
  if left.account.value != right.account.value then
    decide (left.account.value < right.account.value)
  else
    decide (left.entry.resourceId.value < right.entry.resourceId.value)

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

def orderedDebits (transaction : AccountTransaction) : List AccountDebit :=
  transaction.debits.mergeSort AccountDebit.precedes

def orderedCredits (transaction : AccountTransaction) : List AccountCredit :=
  transaction.credits.mergeSort AccountCredit.precedes

theorem orderedDebits_perm (transaction : AccountTransaction) :
    transaction.orderedDebits.Perm transaction.debits :=
  List.mergeSort_perm _ _

theorem orderedCredits_perm (transaction : AccountTransaction) :
    transaction.orderedCredits.Perm transaction.credits :=
  List.mergeSort_perm _ _

/--
Canonical implementation program: account/resource keys determine order, with
every decrease preceding every increase. Declaration order is not authoritative.
-/
def deltas (transaction : AccountTransaction) : List InventoryDelta :=
  transaction.orderedDebits.map AccountDebit.delta ++
    transaction.orderedCredits.map AccountCredit.delta

def accounts (transaction : AccountTransaction) : List AccountId :=
  (transaction.debits.map AccountDebit.account ++
    transaction.credits.map AccountCredit.account).eraseDups

end AccountTransaction

/-- A rejected transaction identifies every failing normalized account leg. -/
inductive AccountTransactionIssue where
  | debitRejected
      (index : Nat)
      (account : AccountId)
      (resourceId : ResourceId)
      (issues : List InventoryDeltaIssue)
  | creditRejected
      (index : Nat)
      (account : AccountId)
      (resourceId : ResourceId)
      (issues : List InventoryDeltaIssue)
  deriving DecidableEq, Repr

private def assessDebits
    {resourceCatalog : ResourceCatalog} :
    Nat → WorldState resourceCatalog → List AccountDebit →
      WorldState resourceCatalog × List AccountTransactionIssue
  | _, state, [] => (state, [])
  | index, state, debit :: rest =>
      match assessInventoryDelta state debit.delta with
      | .accepted accepted =>
          assessDebits (index + 1) (applyInventoryDelta accepted) rest
      | .rejected issues _ _ =>
          let suffix := assessDebits (index + 1) state rest
          (suffix.1,
            .debitRejected index debit.account debit.entry.resourceId issues ::
              suffix.2)

private def assessCredits
    {resourceCatalog : ResourceCatalog} :
    Nat → WorldState resourceCatalog → List AccountCredit →
      WorldState resourceCatalog × List AccountTransactionIssue
  | _, state, [] => (state, [])
  | index, state, credit :: rest =>
      match assessInventoryDelta state credit.delta with
      | .accepted accepted =>
          assessCredits (index + 1) (applyInventoryDelta accepted) rest
      | .rejected issues _ _ =>
          let suffix := assessCredits (index + 1) state rest
          (suffix.1,
            .creditRejected index credit.account credit.entry.resourceId issues ::
              suffix.2)

/--
Collect every failing normalized leg. A failed leg is omitted from the
assessment state so independent later legs are still inspected.
-/
def accountTransactionIssues
    {resourceCatalog : ResourceCatalog}
    (before : WorldState resourceCatalog)
    (transaction : AccountTransaction) : List AccountTransactionIssue :=
  let debits := assessDebits 0 before transaction.orderedDebits
  let credits := assessCredits transaction.orderedDebits.length debits.1
    transaction.orderedCredits
  debits.2 ++ credits.2

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
  match applyInventoryProgram before transaction.deltas with
  | .ok applied => .ok applied
  | .error _ => .error (accountTransactionIssues before transaction)

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
  simp only [AccountTransaction.deltas, AccountTransaction.orderedDebits,
    AccountTransaction.orderedCredits, List.mem_append, List.mem_map,
    List.mem_mergeSort] at deltaMem
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

/--
An exact account-to-account movement expressed as one atomic debit/credit
transaction. Supply may decrease transiently inside receipt construction, but
no intermediate state is exposed and the accepted successor conserves the
moved quantity.
-/
def AccountTransaction.transfer
    (source destination : AccountId)
    (entry : BasketEntry)
    (distinct : source ≠ destination) : AccountTransaction where
  debits := [{ account := source, entry }]
  credits := [{ account := destination, entry }]
  debitKeysUnique := by simp
  creditKeysUnique := by simp
  directionsDisjoint := by
    intro debit debitMem credit creditMem
    simp only [List.mem_singleton] at debitMem creditMem
    subst debit
    subst credit
    intro keysEqual
    exact distinct (Prod.mk.inj keysEqual).1

end Maquina
