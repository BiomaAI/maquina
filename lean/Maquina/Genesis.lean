import Maquina.AccountTransaction

/-!
# Maquina Genesis

Genesis is the sole public mechanism for issuing a game's initial holdings.
It has no predecessor world supplied by game code and therefore cannot be
reused as a runtime mutation escape hatch.
-/

namespace Maquina

/-- One positive initial allocation to a concrete account. -/
structure GenesisGrant where
  account : AccountId
  entry : BasketEntry
  deriving Repr

namespace GenesisGrant

def key (grant : GenesisGrant) : AccountId × ResourceId :=
  (grant.account, grant.entry.resourceId)

def credit (grant : GenesisGrant) : AccountCredit :=
  { account := grant.account, entry := grant.entry }

end GenesisGrant

/-- Canonical initial holdings: no account/resource key may be granted twice. -/
structure GenesisPlan where
  grants : List GenesisGrant
  keysUnique : (grants.map GenesisGrant.key).Nodup
  deriving Repr

namespace GenesisPlan

/-- Internal account-level program derived from declarative grants. -/
private def transaction (plan : GenesisPlan) : AccountTransaction where
  debits := []
  credits := plan.grants.map GenesisGrant.credit
  debitKeysUnique := by simp
  creditKeysUnique := by
    have exactKeys :
        (plan.grants.map GenesisGrant.credit).map AccountCredit.key =
          plan.grants.map GenesisGrant.key := by
      simp only [List.map_map]
      congr 1
    rw [exactKeys]
    exact plan.keysUnique
  directionsDisjoint := by simp

end GenesisPlan

/-- Proof-carrying realization of one genesis plan from the canonical void. -/
abbrev AppliedGenesis
    (resourceCatalog : ResourceCatalog)
    (plan : GenesisPlan) :=
  AppliedAccountTransaction (WorldState.empty resourceCatalog) plan.transaction

/-- Validate and realize initial holdings exactly once from the empty world. -/
def applyGenesis
    (resourceCatalog : ResourceCatalog)
    (plan : GenesisPlan) :
    Except (List AccountTransactionIssue) (AppliedGenesis resourceCatalog plan) :=
  applyAccountTransaction (WorldState.empty resourceCatalog) plan.transaction

/-- Canonical complete genesis diagnostics. -/
def genesisIssues
    (resourceCatalog : ResourceCatalog)
    (plan : GenesisPlan) : List AccountTransactionIssue :=
  accountTransactionIssues (WorldState.empty resourceCatalog) plan.transaction

/-- Rejected genesis exposes no partially initialized world. -/
def genesisSuccessor
    (resourceCatalog : ResourceCatalog)
    (plan : GenesisPlan) : Option (WorldState resourceCatalog) :=
  match applyGenesis resourceCatalog plan with
  | .error _ => none
  | .ok applied => some applied.after

theorem genesisSuccessor_rejected
    (resourceCatalog : ResourceCatalog)
    (plan : GenesisPlan)
    (issues : List AccountTransactionIssue)
    (rejected : applyGenesis resourceCatalog plan = .error issues) :
    genesisSuccessor resourceCatalog plan = none := by
  simp [genesisSuccessor, rejected]

/-- Every accepted genesis receipt replays to the exact initialized holdings. -/
theorem AppliedGenesis.replay_exact
    {resourceCatalog : ResourceCatalog}
    {plan : GenesisPlan}
    (applied : AppliedGenesis resourceCatalog plan) :
    replayInventoryProgram applied.receipts
        (WorldState.empty resourceCatalog).holdings = applied.after.holdings :=
  applied.replayExact

end Maquina
