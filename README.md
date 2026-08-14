# Maquina

Maquina is a formally specified execution model for deterministic, replayable
worlds. It describes what exists, where it belongs, which changes are allowed,
what each accepted change produces, and how the resulting history can be
reconstructed and verified.

The central boundary is simple:

> Agents, people, policies, planners, and solvers propose. Maquina determines
> what those proposals mean, whether they are valid, and what consequences
> they produce.

This repository is a conceptual foundation. It contains an empty Rust
workspace and a minimal Lean 4 project, but no implementation has been copied
from earlier projects.

## Conceptual lineage

Maquina consolidates ideas explored independently across four repositories.
This is conceptual lineage, not a code merge.

| Source | Contribution to the concept |
| --- | --- |
| [`rozgo/maquina`](https://github.com/rozgo/maquina) | Typed objects, inventories, event sourcing, replayed projections, knowledge access, and MCP tools for agent interaction. |
| [`rozgo/maquina-bevy`](https://github.com/rozgo/maquina-bevy) | Composable resources, queues, universal machines, operations, processes, behavior trees, deterministic time, and simulation through Bevy ECS. |
| [`BiomaAI/bioma`](https://github.com/BiomaAI/bioma) | Persistent worlds, capability-and-rule interaction, mixed human/robot/agent participation, operational hierarchy, branching history, and realtime observation. |
| [`BiomaAI/axionomy`](https://github.com/BiomaAI/axionomy) | Closed authoritative state, assets and accounts, rates and exchanges, explicit invariants, structured rejection, exact forks, solver-neutral search, and verified replay. |

The new Maquina keeps the common thesis while remaining independent of the
existing implementations, storage systems, interfaces, and frameworks.

## What Maquina is

Maquina is a semantic kernel for systems whose state and changes must be
explicit, inspectable, and reproducible. The same model should be usable for:

- operational software;
- industrial and logistics systems;
- games and persistent simulated worlds;
- planning, optimization, and counterfactual exploration;
- human, robotic, and AI-agent coordination;
- auditable automation and formally checked execution.

Maquina is not an agent framework or a solver. It is the authoritative
environment those systems act against. An agent can propose an action, a
planner can explore a fork, and an optimizer can rank alternatives, but none
of them can make an invalid transition valid or mutate authoritative state
through a side channel.

## Core model

The vocabulary will be refined in Lean before the Rust runtime is designed,
but the initial model has the following roles.

### Assets and objects

An asset identifies anything that can exist or matter: a physical resource, a
unique object, a fact, a capability, a permission, a condition, a goal, an
observation, or a state token. Quantities may be discrete, measured, unique,
or composed, while preserving exact identity and units.

### Accounts and inventories

An account answers "where?" or "whose?" It can represent a person, agent,
machine, location, organization, scope, or namespace. An inventory is a useful
view of the assets held by an account; it is not a separate source of truth.

At its simplest, authoritative state can be understood as:

```text
State : Account x Asset -> Quantity
```

### Rules, rates, operations, and processes

A rule defines an allowed kind of change. It can declare:

- required and preserved conditions;
- consumed inputs;
- produced outputs;
- actor and account bindings;
- capabilities and permissions;
- capacity, timing, ordering, and uniqueness constraints;
- invariants that must remain true.

An operation changes the condition of a machine or actor. A process transforms
inputs into outputs. Both are specializations of explicit transition rules,
not permission to run arbitrary hidden mutation.

### Proposals, exchanges, and events

A proposal binds a rule to concrete actors, accounts, assets, quantities, and
parameters. Assessment is pure: it either returns a structured explanation of
why the proposal cannot apply or a complete description of its effects.

Applying an accepted proposal atomically produces a receipt and an immutable
event. The event history can reconstruct the same state through replay.

```text
proposal -> assess -> reject(reason)
                   -> accept(effects) -> apply -> receipt + event
```

### Machines and queues

A machine is a stateful processor governed by rules. It may own inventories,
accept work through ordered queues, run one or more processing slots, consume
and produce assets, expose operating conditions, and record its evolution.

Queues make ordering, capacity, ownership, cancellation, and collection
explicit. Time is supplied by the environment so tests and simulations remain
deterministic.

### Agents and behaviors

Agents observe the portion of state they are permitted to see and propose
actions through the same transition boundary as every other participant.
Behavior trees, LLMs, policies, planners, scripts, and human interfaces are
replaceable decision systems outside the authoritative kernel.

### Projections, observations, and knowledge

Indexes, projections, graphs, dashboards, search structures, embeddings, and
knowledge views are derived from authoritative state and events. They may help
participants understand the world or choose a proposal, but rebuilding or
losing a projection cannot change what is valid.

## What Maquina should enable

When implemented, Maquina should be able to:

- define typed assets, objects, capabilities, conditions, and units;
- place and transfer them across accounts, inventories, and locations;
- describe machines, workflows, queues, operations, and transformations as
  data;
- assess actions without mutation and explain every missing requirement;
- apply valid actions atomically and reject invalid actions consistently;
- derive current views from an append-only history;
- snapshot, fork, simulate, compare, and replay possible futures;
- expose actor-scoped observations and valid-action information;
- support competing or cooperating actors with different objectives;
- integrate through APIs, events, and MCP without giving integrations direct
  mutation authority;
- verify foundational invariants against a formal specification.

## Rust and Lean

Maquina starts as two deliberately separate layers.

### Lean 4: semantic specification

Lean defines the meaning of Maquina before runtime concerns are introduced.
The formal model should eventually specify:

- identity, quantity, state, and canonical representation;
- rule well-formedness and proposal assessment;
- atomic transition semantics;
- receipts, traces, and replay;
- authorization and actor-scoped observation;
- machines, queues, time, and concurrent intent resolution;
- declared goals and invariants.

Initial proof targets include:

- quantities and capacities never become invalid;
- rejected proposals do not change state;
- accepted transitions satisfy their declared preconditions;
- application is atomic;
- replay produces the same state as sequential application;
- protected supply, ownership, and permission invariants are preserved;
- equivalent bindings do not create order-dependent results;
- derived projections cannot alter transition validity.

Lean is the source of semantic truth, not the production runtime. The project
may later generate test vectors, executable reference behavior, or checked
artifacts that the Rust implementation must satisfy.

### Rust: executable kernel

Rust will eventually provide the production engine, persistence boundaries,
projection machinery, simulation APIs, and integration surfaces. The runtime
must implement the Lean-defined semantics and demonstrate parity through
shared fixtures and conformance tests.

The Rust workspace is intentionally empty today. No crate structure or
framework choice should harden before the vocabulary and transition contract
are precise.

## Architectural boundary

```text
people / agents / policies / planners / solvers
                       |
                       v
                proposed action
                       |
                       v
        +-------------------------------+
        |            MAQUINA            |
        | observe -> assess -> apply     |
        | state + rules + invariants     |
        +-------------------------------+
                       |
                       v
      receipt + event + new observation + trace
```

Decision systems may use snapshots and forks to reason before proposing a
change. Only Maquina applies changes to the authoritative state.

## Non-goals for this foundation

This repository does not yet choose or provide:

- code copied from any predecessor;
- a database or event-store implementation;
- a UI, web framework, ECS, robotics stack, or deployment platform;
- an agent runtime, model provider, or training system;
- a universal ontology for every domain;
- compatibility guarantees with existing Maquina, Bioma, or Axionomy data.

Those decisions should follow the formal model rather than define it by
accident.

## Development sequence

1. Define the smallest closed state and transition model in Lean.
2. State and prove the first safety and replay properties.
3. Design a pure Rust kernel against that specification.
4. Establish cross-language conformance fixtures.
5. Add event persistence, projections, snapshots, and forks.
6. Add optional adapters for APIs, MCP, simulation, ECS, and operational
   platforms.

## Repository layout

```text
Cargo.toml          Empty Rust workspace
rust-toolchain.toml Pinned Rust toolchain
lakefile.toml       Lean project definition
lean-toolchain      Pinned Lean 4 toolchain
lake-manifest.json  Reproducible Lake dependency manifest
Maquina.lean        Reserved root module for the formal specification
README.md           The single conceptual document
.github/workflows/  Rust workspace and Lean build validation
```

The repository should remain concept-first until the formal vocabulary is
stable enough to support implementation.
