# Games

This directory contains games implemented as formal Lean simulations over
Maquina.

`games` is the user-facing name: these should be understandable as games with
rules, choices, goals, and consequences. “Formal game simulation” describes
how they are implemented and validated. A game may later gain a Rust runtime,
agents, or a user interface without changing the meaning established here.

## Directory convention

Each game may contain:

- `README.md` for its rules, goals, and proof targets;
- `lean/` for its authoritative simulation and proofs;
- `rust/` for an optional runtime implementation;
- `fixtures/` for shared replay and conformance scenarios;
- `assets/` for optional presentation assets; and
- a thin showcase adapter defining names, scenarios, and declarative styles for
  the shared visualizer protocol.

Games depend on Maquina. Maquina must not depend on the games or absorb their
domain-specific states and operations. The visualizer renderer must likewise
remain independent of game identities and rules.

## Games

| Game | Status | Purpose |
| --- | --- | --- |
| [Foundry](foundry/) | Seed | Drive resources, queues, typed operations, machines, time, failure, repair, and replay. |
| [Operation Nightglass](nightglass/) | Interactive | Pressure-test heterogeneous components, deterministic contention, immutable forks, actor observations, and counterfactual command. |
| [Operation Veiled Accord](veiled-accord/) | Interactive | Pressure-test information sets, scoped communication, costly signals, escrow, sealed orders, cooperation, and betrayal. |
