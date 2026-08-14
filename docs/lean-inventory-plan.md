# Lean Inventory Working Plan

> Status: temporary working design note. Keep this document aligned with the
> Lean model while Iterations 3 and 4 are in progress. Replace or remove it
> when the semantics become stable normative documentation.

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
- Quantities remain exact, nonnegative counts of object-specific atoms.
- Assessment is pure and separate from application.
- Application accepts proof that a proposal was assessed successfully.
- Rejections are structured and identify every relevant shortfall.
- Fungibility follows identity. Unique instances and bounded editions are
  expressed through identity and supply constraints.
- Metadata, sorting, filtering, and ECS relationships are non-authoritative
  unless a formal rule explicitly depends on them.

## Iteration 3: canonical inventory and atomic transfer

### Proposed modules

```text
lean/Maquina/Inventory.lean
lean/Maquina/Transfer.lean
```

`Maquina.Inventory` will define the canonical world holdings and derived
inventory and supply views. `Maquina.Transfer` will define the first proposal,
assessment, accepted witness, receipt, and application semantics.

### Canonical state

The conceptual state is:

```text
State : Account x Object -> Quantity
```

The initial Lean representation should be a finite sparse collection of
positive holdings with no duplicate `(account, object)` key:

```lean
structure Holding (Account : Type) where
  account : Account
  objectId : ObjectId
  quantity : Quantity
  positive : 0 < quantity.atoms

structure WorldState (Account : Type) where
  holdings : List (Holding Account)
  keysUnique : -- no duplicate (account, object) pairs
  objectsKnown : -- every held object resolves in the catalog
  respectsLimits : -- every object total respects its supply limit
```

The exact proof fields may change as the implementation reveals a clearer
factoring. The semantic requirements must not be weakened.

An account inventory and the global supply of an object must be projections
from `WorldState`, not separately mutable stores.

### Canonical baskets

A basket is a finite set of positive, object-qualified quantities:

```lean
structure Basket where
  entries : List (ObjectId x Quantity)
  objectsUnique : -- no repeated object IDs
  quantitiesPositive : -- zero entries are absent
```

Baskets will become the common vocabulary for transfers, consumption,
production, requirements, receipts, compositions, processes, and operations.

### Transfer boundary

Assessment and application remain separate:

```lean
assessTransfer :
  WorldState Account ->
  Transfer Account ->
  Except TransferRejection (AcceptedTransfer ...)

applyTransfer :
  AcceptedTransfer state proposal ->
  WorldState Account x Receipt Account
```

`AcceptedTransfer` must carry enough evidence for application to be total: the
source owns the requested quantities, referenced objects are valid, and the
projected state satisfies all applicable invariants.

A rejection should report, as applicable:

- unknown account or object;
- requested and available quantities;
- exact shortfall;
- incompatible binding;
- capacity violation;
- supply-limit or other invariant violation.

### Proof targets

1. Source and destination balances change by exactly the transferred amounts.
2. Every unrelated balance remains unchanged.
3. Global supply is conserved for every transferred object.
4. All declared object supply limits remain satisfied.
5. Application preserves sparse canonical form: positive values and unique
   `(account, object)` keys.
6. Rejection produces no successor state.
7. Assessment and application are deterministic.
8. Replaying a receipt reconstructs the same resulting state.
9. A multi-object basket transfer is atomic: all entries apply or none do.

### Concrete examples

Alongside universal proofs, construct small examples for:

- an empty inventory;
- a fungible discrete balance;
- a measured balance in canonical atoms;
- one unique object moving between accounts;
- a bounded edition split between accounts;
- a successful multi-object transfer;
- a rejected transfer with multiple shortfalls.

These examples demonstrate that the proof premises are constructible and make
the intended API visible.

## Iteration 4: packs, bundles, and expansion

Composition should be modeled only after the inventory transition boundary is
stable.

Requirements:

- pack and bundle coefficients are exact positive atom quantities;
- every referenced object is declared by the catalog;
- an object cannot directly or indirectly contain itself;
- the composition dependency graph carries an acyclicity proof;
- recursive expansion terminates;
- expansion is deterministic, canonical, and additive;
- unknown objects are rejected rather than silently treated as base objects;
- expansion is a derived view and cannot mutate authoritative holdings.

We must distinguish two meanings before fixing the final representation:

1. A composition view says an object represents or contains other objects for
   querying and requirements.
2. A conversion rule explicitly consumes a pack or bundle and produces its
   contents, or performs the reverse packing operation.

Economically distinct denominations should remain distinct object identities
connected by explicit operations. Expansion must not accidentally allow both
the container and its contents to be spent as independent authoritative value.

Expected proofs include termination, absence of undeclared leaves,
determinism, additivity, and preservation of declared weighted measures across
explicit pack and unpack operations.

## Requirements mapped from Maquina-Bevy

| Maquina-Bevy capability | Formal interpretation |
| --- | --- |
| Automatic stacking | Canonical uniqueness of `(account, object)` holdings |
| Unique instance | Distinct object identity with supply limit one |
| Bounded edition | One identity with a bounded atom supply |
| Bulk consumption | Atomic basket transition |
| Pack or bundle | Explicit composition and/or conversion definition |
| Recursive expansion | Pure derived projection over an acyclic catalog |
| Max stack size | Runtime storage concern, separate from global supply |
| Inventory capacity | Per-account invariant when semantically relevant |
| Metadata and tags | Derived data unless rules explicitly inspect them |
| Sorting and filtering | Presentation-only projection |
| Bevy entity relationships | Runtime adapter for account/object relationships |

## Deferred work

- Metadata, tags, filtering, sorting, summaries, and display formatting.
- Bevy entity/component and relationship representation.
- Runtime stacking and storage optimization.
- Machine input/output buffers and subject routing.
- General consume/preserve/produce rates beyond the first transfer.
- Persistence, event logs, snapshots, forks, and cross-language fixtures.

These remain requirements, but they must build on the proved state and
transition semantics rather than introducing parallel authority.
