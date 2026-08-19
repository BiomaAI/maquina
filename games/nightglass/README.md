# Operation Nightglass

Operation Nightglass is a proof-backed extraction mission built downstream of
Maquina. It is deliberately unlike Foundry: radar, two interceptor batteries,
and an evacuation convoy have different mode graphs and policies, yet share one
authoritative account state and one deterministic logical timeline.

## Architectural boundary

Nightglass owns every military concept:

- radar scanning, contact tracking, and track clearing;
- battery acquisition, interceptor launch, engagement, damage, and repair;
- convoy routes, hostile strikes, extraction, and mission outcome;
- the meaning and priority of arbitration coordinates; and
- the heterogeneous state containing the radar, batteries, convoy, and their
  custody proofs.

Maquina core knows none of those terms. It supplies resources, accounts,
normalized account transactions, operation assessment, isolated machine
runtimes, logical ticks, scheduled opaque intents, canonical ordering,
proof-carrying accepted transitions, immutable events, and replay.

```text
Nightglass policy and heterogeneous state
                  |
                  v
Maquina IntentExecutor + deterministic TimelineState
                  |
                  v
accepted receipt / snapshot rejection / conflict rejection
```

## Mission trace

Run the checked headless mission with:

```sh
lake exe nightglass-demo
```

Sixteen scheduled intents resolve over ticks zero through eight. At tick two,
both batteries are eligible to acquire the single targeting channel from the
same snapshot. Alpha wins the declared canonical order and Bravo emits a
`lostConflict` event without mutation. At tick four, the hostile strike wins
the declared order and damages the convoy; the snapshot-valid route advance
then loses against the tentative state. The convoy consumes a spare to repair
at tick five, resumes its route at tick six, extracts at tick seven, and the
remaining battery engagement resolves at tick eight.

The final authoritative state is tick nine with no pending intents, the
targeting channel returned to command, two of four interceptors consumed, all
24 evacuees still in the convoy manifest, one spare remaining, and the convoy
in `extracted` mode.

## Checked properties

Lean checks that:

- pending intent identities are unique by construction;
- due intents are ordered by logical time, opaque game-owned arbitration
  coordinates, then stable intent identity;
- every due intent is first assessed against the unchanged tick snapshot;
- cross-component contact tracking is assessed by Nightglass against the radar
  state before the generic battery operation runs;
- a snapshot-valid intent that fails against the tentative successor is an
  explicit conflict loss and cannot mutate that successor;
- accepted account costs are atomic and rejected costs expose no successor;
- ammunition and repair parts are ordinary account resources, independent of
  component identity;
- the unique targeting channel cannot occupy two battery accounts;
- damage and repair form a separate checked branch, with repair consuming one
  spare part;
- rejected timeline events replay as identity;
- accepted snapshot receipts replay the complete heterogeneous game state;
- concatenated events from all nine ticks replay exactly from the initial
  state to the final mission state; and
- reversing the submitted Alpha/Bravo contenders does not change their
  canonical resolved order.

## Visualization

The [Maquina simulation atlas](https://biomaai.github.io/maquina/?showcase=nightglass-extraction)
renders the Lean-exported ticks and event receipts. Nightglass contributes only
declarative protocol metadata: radar, battery, and convoy geometry; mode-driven
activity and convoy positions; colors; labels; and camera placement. The shared
scene projector and Three.js renderer contain no mission-specific transition
logic.
