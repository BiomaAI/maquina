# Lean Inventory Working Plan

> Status: Iteration 3 is implemented and checked by `lake build`. Keep this as
> a temporary working design note while Iteration 4 is in progress. Replace or
> remove it when the semantics become stable normative documentation.

This plan combines Axionomy's closed-state and atomic-exchange semantics with
the inventory requirements demonstrated by Maquina-Bevy's
`plugins/maquina_resource`.

## Independence boundary

Axionomy and Maquina-Bevy are conceptual references, not dependencies or
source donors.

- Maquina does not depend on Axionomy crates or import their implementation.
- Maquina's semantic kernel does not depend on Bevy or its ECS types.
- Definitions, algorithms, proofs, and runtime code are developed independently
  for this repository; no source is copied across.
- There is no compatibility, migration, or legacy-behavior requirement.
- Concepts learned from the earlier systems are restated as Maquina semantics
  and justified by Maquina proofs.
- A future Bevy integration, if useful, belongs in an optional adapter outside
  the authoritative kernel.

## Guiding decisions

- Lean defines authoritative meaning; Rust and Bevy implement and project it.
- The world has one authoritative holding representation. Inventories, global
  supply, summaries, indexes, and UI views are derived from it.
- Quantities remain exact, nonnegative counts of resource-specific atoms.
- Assessment is pure and separate from application.
- Application accepts proof that a proposal was assessed successfully.
- Rejections are structured and identify every relevant shortfall.
- Fungibility follows identity. Unique instances and bounded editions are
  expressed through identity and supply constraints.
- Metadata, sorting, filtering, and ECS relationships are non-authoritative
  unless a formal rule explicitly depends on them.

## Iteration 3: canonical inventory and atomic transfer

### Implemented modules

```text
lean/Maquina/Account.lean
lean/Maquina/Resource.lean
lean/Maquina/Inventory.lean
lean/Maquina/Transfer.lean
lean/Maquina/Examples.lean
```

`Maquina.Account` defines stable account identities, valid by construction and
without a separate registry. `Maquina.Resource` defines resource identity,
quantities, measurement semantics, supply limits, and resource catalogs.
`Maquina.Inventory` defines the canonical world holdings and derived inventory
and supply views. `Maquina.Transfer` defines the first proposal, assessment,
accepted witness, receipt, and application semantics. `Maquina.Examples`
contains closed, executable proof examples.

### Canonical state

The conceptual state is:

```text
State : Account x Resource -> Quantity
```

The Lean representation is a finite sparse collection of positive holdings
with no duplicate `(account, resource)` key:

```lean
structure Holding (Account : Type) where -- generic low-level representation
  account : Account
  resourceId : ResourceId
  quantity : Quantity
  positive : 0 < quantity.atoms

structure WorldState (resources : ResourceCatalog) where
  holdings : List (Holding AccountId)
  keysUnique : -- no duplicate (account, resource) pairs
  resourcesKnown : -- every held resource resolves in the resource catalog
  respectsLimits : -- every resource total respects its supply limit
```

The exact proof fields may change as the implementation reveals a clearer
factoring. The semantic requirements must not be weakened.

An account inventory and the global supply of a resource must be projections
from `WorldState`, not separately mutable stores.

### Canonical baskets

A basket is a finite set of positive, resource-qualified quantities:

```lean
structure Basket where
  entries : List BasketEntry -- each entry carries its own positivity proof
  resourcesUnique : -- no repeated resource IDs
```

Baskets will become the common vocabulary for transfers, consumption,
production, requirements, receipts, compositions, processes, and operations.

### Transfer boundary

Assessment and application remain separate:

```lean
assessTransfer
  (state : WorldState resources)
  (proposal : Transfer) :
  TransferAssessment state proposal

applyTransfer
  (accepted : AcceptedTransfer state proposal) :
  WorldState resources x TransferReceipt
```

`AcceptedTransfer` must carry enough evidence for application to be total: the
source owns the requested quantities, referenced resources are valid, and the
projected state satisfies all applicable invariants.

A rejection should report, as applicable:

- a resource that does not resolve to an authoritative definition;
- requested and available quantities;
- exact shortfall;
- incompatible binding;
- capacity violation;
- supply-limit or other invariant violation.

### Proof targets

1. Source and destination balances change by exactly the transferred amounts.
2. Every unrelated balance remains unchanged.
3. Global supply is conserved for every transferred resource.
4. All declared resource supply limits remain satisfied.
5. Application preserves sparse canonical form: positive values and unique
   `(account, resource)` keys.
6. Rejection produces no successor state.
7. Assessment and application are deterministic.
8. Replaying a receipt reconstructs the same resulting state.
9. A multi-resource basket transfer is atomic: all entries apply or none do.

### Iteration 3 proof inventory

All nine targets above are now represented in checked Lean declarations:

| Guarantee | Primary declarations |
| --- | --- |
| Exact source debit | `applyTransferState_source` |
| Exact destination credit | `applyTransferState_destination` |
| Unrelated balances unchanged | `applyTransferState_unlistedResource`, `applyTransferState_otherAccount` |
| Global conservation | `applyTransferState_total` |
| Supply limits and canonical state preserved | `applyTransferState` and its `WorldState` proof fields |
| Rejection has no successor | `applyAssessment_rejected` |
| Deterministic application | `applyTransfer_deterministic`, `assessAndApply_deterministic` |
| Receipt replay | `replay_transferReceipt_state` |
| Multi-resource all-or-none execution | `applyAssessment`, `assessAndApply` |

`AcceptedTransfer.resourceKnown` and `AcceptedTransfer.funded` expose the resource
definition and source funding evidence already implied by successful
assessment. Accounts have no registry or independent validity authority:
`AccountId` is valid by construction, while balances and the accepted transfer
witness determine whether a transfer is enabled.

### Concrete examples

Alongside universal proofs, `Maquina.Examples` constructs and checks:

- an empty inventory;
- a fungible discrete balance;
- a measured balance in canonical atoms;
- one unique resource moving between accounts;
- a bounded edition split between accounts;
- a successful multi-resource transfer;
- a rejected transfer with multiple shortfalls.

These examples demonstrate that the proof premises are constructible and make
the intended API visible.

## Iteration 4: packs, bundles, and expansion

Composition should be modeled only after the inventory transition boundary is
stable.

Requirements:

- pack and bundle coefficients are exact positive atom quantities;
- every referenced resource is declared by the resource catalog;
- a resource cannot directly or indirectly contain itself;
- the composition dependency graph carries an acyclicity proof;
- recursive expansion terminates;
- expansion is deterministic, canonical, and additive;
- unknown resources are rejected rather than silently treated as base resources;
- expansion is a derived view and cannot mutate authoritative holdings.

We must distinguish two meanings before fixing the final representation:

1. A composition view says a resource represents or contains other resources for
   querying and requirements.
2. A conversion rule explicitly consumes a pack or bundle and produces its
   contents, or performs the reverse packing operation.

Economically distinct denominations should remain distinct resource identities
connected by explicit operations. Expansion must not accidentally allow both
the container and its contents to be spent as independent authoritative value.

Expected proofs include termination, absence of undeclared leaves,
determinism, additivity, and preservation of declared weighted measures across
explicit pack and unpack operations.

## Requirements mapped from Maquina-Bevy

| Maquina-Bevy capability | Formal interpretation |
| --- | --- |
| Automatic stacking | Canonical uniqueness of `(account, resource)` holdings |
| Unique instance | Distinct resource identity with supply limit one |
| Bounded edition | One identity with a bounded atom supply |
| Bulk consumption | Atomic basket transition |
| Pack or bundle | Explicit composition and/or conversion definition |
| Recursive expansion | Pure derived projection over an acyclic resource catalog |
| Max stack size | Runtime storage concern, separate from global supply |
| Inventory capacity | Per-account invariant when semantically relevant |
| Metadata and tags | Derived data unless rules explicitly inspect them |
| Sorting and filtering | Presentation-only projection |
| Bevy entity relationships | Runtime adapter for account/resource relationships |

## Deferred work

- Metadata, tags, filtering, sorting, summaries, and display formatting.
- Bevy entity/component and relationship representation.
- Runtime stacking and storage optimization.
- Machine input/output buffers and subject routing.
- General consume/preserve/produce rates beyond the first transfer.
- Persistence, event logs, snapshots, forks, and cross-language fixtures.

These remain requirements, but they must build on the proved state and
transition semantics rather than introducing parallel authority.
