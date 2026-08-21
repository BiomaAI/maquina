# Machine Composition and Emergent Features

Maquina deliberately keeps its authoritative vocabulary small. Rich features
such as attachments, nested containers, vehicles, crews, situations, regional
conditions, and shared capabilities are composed from the same four elements:

1. **Resources** state what exists and where it is held.
2. **Processes** declare the exact resources consumed, reserved, and produced.
3. **Operations** declare when a Process may execute and how a Machine changes
   mode or queue state.
4. **Machines** provide stable Body identity, inventory, custody, queues, and
   the typed Operation language.

The recipes in this document are compile-checked recommendations, not new
kernel primitives and not complete games.

## The authoring transition rule

Game and recipe code should not submit arbitrary debits, credits, transfers, or
account transactions to mutate runtime state. The documented runtime path is:

```text
typed Operation proposal
  -> structured guards and possession requirements
  -> declared Process
  -> generic Maquina simulator
  -> proof-carrying successor and replayable receipts
```

Initial holdings use `GenesisPlan`, which can only be applied to the canonical
empty world. This is an explicit authoring discipline: contributors should not
let a convenient helper silently become a second execution model.

## Foundational composition features

### Body identity

Every Machine declares one stable `body : ResourceId`. A `Machine.BodyBacked`
witness connects that identity to a unique Body Resource held by the Machine's
inventory in an exact world. Queue topology changes preserve the Body.

A Body is identity, not containment. A Machine does not gain child fields or a
second ownership tree when components are attached.

### Structured Resource families

`ResourceFamily Key` gives parameterized resources a reversible identity
scheme, canonical specification, injective encoding, and optional disjointness
proofs. Endpoint, Link, lease, claim, and other keyed resources can therefore
be generated without treating arbitrary numeric IDs as semantics.

### Endpoints, Links, and leases

An endpoint is a finite attachment position on a Body. An open endpoint is
represented by its unique endpoint Resource in the owning Machine inventory.
A Link is a unique Resource describing two concrete endpoints and a game-owned
relation kind.

Attaching is a normal Process:

```text
left open endpoint + right open endpoint
  -> active Link + Link lease
```

Detaching is the inverse Process. A missing half-Link is unnecessary: the open
endpoint Resource already means “this position is available but not linked.”
The number of endpoint Resources created at genesis or by a declared Process
is the Machine's connection capacity.

The Link lease is a unique lock token. Long-running Processes reserve leases
for every relation path on which they depend. A detach Operation must consume
the Link and the same lease, so normal possession/reservation assessment blocks
detachment while the path is in use. This adds no special graph lock API.

### Relations are projections

`RelationModel` maps structured endpoint, Link, and lease keys to Resources and
maps Link keys to game-owned relation descriptions. The authoritative fact is
the Link Resource held by the relation ledger. Connectivity is rebuilt from
holdings and declared descriptions.

`RelationPolicy` remains game policy. It declares endpoint compatibility and
forward/backward traversal for each relation kind. The kernel does not decide
whether a relation means attachment, containment, membership, influence, or
capability access.

`RelationPath` is a concrete candidate path with no repeated Link. Assessment
checks, in order:

- hop continuity;
- endpoint compatibility;
- allowed traversal direction; and
- presence of every Link Resource in the exact world.

Acceptance carries proof that the complete issue list is empty. Rejection is
complete, deterministic, and has no successor because it is used as an
Operation guard before Process execution.

### Pure manifests and reachable requirements

A Machine manifest is a rebuildable collection of accepted reachability
evidence. It is not an inventory cache and cannot be debited. Each entry names
an exact root Body, path, destination Machine, Resource, minimum quantity, and
world.

A reachable-resource requirement succeeds only when:

- the path begins at the declared root Body;
- the entire relation path is accepted;
- the destination Body resolves to one inventory account; and
- that inventory holds the declared quantity.

Games place this assessment in a structured Operation guard, then bind the
same destination account to the Process or possession requirement. Thus a
reachable capability can authorize a real Operation without copying it into
the caller's inventory or inventing contextual balances.

## Recipe catalog

| Feature | Compile-checked recipe | Formation rule |
| --- | --- | --- |
| Attachment | [`Attachment.lean`](../lean/Maquina/Recipes/Attachment.lean) | Consume two open endpoints; produce one Link and lease; detach by the inverse Process. |
| Bag of bags | [`NestedContainers.lean`](../lean/Maquina/Recipes/NestedContainers.lean) | A containment Link connects bag and pouch Machines; contents stay in their original inventories and appear through a manifest. |
| Vehicle | [`Vehicle.lean`](../lean/Maquina/Recipes/Vehicle.lean) | Assembly links separately identified component Machines to a vehicle Machine. |
| Crew | [`Crew.lean`](../lean/Maquina/Recipes/Crew.lean) | Mounting consumes vehicle and crew endpoints to create a membership Link. |
| Emergent situation | [`Situation.lean`](../lean/Maquina/Recipes/Situation.lean) | An ordinary Machine transforms phase Resources and manifests opportunity tokens; agents decide whether to use them. |
| Region overlay | [`RegionOverlay.lean`](../lean/Maquina/Recipes/RegionOverlay.lean) | A Region Machine Process creates an overlay Link and contextual Resources in affected inventories. |
| Shared capability | [`SharedCapability.lean`](../lean/Maquina/Recipes/SharedCapability.lean) | A reachable-resource guard validates access; active work reserves the path lease and blocks detachment. |

All recipes define a real Machine schema, Process, state-indexed typed
Operation, proposal bindings, Genesis plan, generic simulator execution, and
checked outcome. Shared support contains only vocabulary, identity families,
catalog data, and relation descriptions—never transition helpers.

## Situations without a Situation primitive

A situation is an emergent Machine configuration:

- its Body gives it identity;
- its inventory holds phase, slot, opportunity, and condition Resources;
- its Operations expose possible transitions;
- its Processes transform those Resources;
- relation Links describe participants, regions, vehicles, or subordinate
  situations; and
- reachable-resource guards make contextual capabilities available to related
  Machines.

The Machine does not command participants or perform their actions. For
example, an escalation Process may produce three `Violence` opportunity tokens.
Agents choose whether their own Operations exchange those tokens. A
de-escalation Process may require all three tokens returned, making the phase
flow depend on authoritative inventory without adding a behavior-tree executor
to the kernel.

Hierarchy is likewise derived. A game can be a root Machine, a vehicle can be
a Machine related to component and crew Machines, and a local incident can be
a Machine related to a region. There is no stored parent pointer and no special
“multi-machine state.”

## Design guidance

Prefer a new recipe or game-owned relation kind when a feature can be stated as
Resources transformed by Processes. Add a kernel primitive only when the
existing execution boundary cannot express a universal invariant.

Good composition:

- uses unique endpoint, Link, and lease Resources for exclusive structure;
- keeps game meaning in Process, Operation, guard, and relation policy data;
- derives graphs and manifests from exact holdings;
- reserves path leases for work that must survive topology changes;
- binds every transformed resource through the proposal; and
- exercises the generic simulator and its receipts.

Boundary violations:

- a helper that directly edits account balances;
- a second graph or containment store that can disagree with Link Resources;
- cached manifest quantities treated as spendable inventory;
- a “situation effect” that mutates participants outside their Operations;
- attachment represented only by a Boolean or parent field; or
- game code importing transaction implementation modules.

## What remains game-defined

Maquina proves mechanics, not meaning. Games still define:

- relation kinds and compatibility;
- which paths propagate capabilities or conditions;
- who may propose attach, detach, enter, leave, escalate, or resolve Operations;
- Process duration, queues, cancellation, and scheduling policy;
- how opportunity tokens are used;
- whether missing resources mean waiting, failure, or another phase; and
- what observations expose to each actor.

This boundary keeps the kernel small while allowing sophisticated structures
to emerge from a few common primitives.
