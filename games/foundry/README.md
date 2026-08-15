# Foundry

Foundry is the first formal game simulation built on Maquina.

The player operates a small industrial machine: supply ore and fuel, start the
machine, queue smelting work, collect produced ingots, and manage wear before
the machine fails. A broken machine cannot smelt until it is repaired.

## Why this game comes first

The loop is deliberately small while exercising the foundational model:

- exact discrete and measured resources;
- labeled process inputs and outputs;
- bounded FIFO input and output queues;
- one or more processing queues;
- game-defined machine modes and typed operations;
- exact time, fuel consumption, heat, and wear;
- reactive failure and commanded repair;
- atomic transitions, receipts, deterministic replay, and forks.

## Game-owned vocabulary

Foundry, not Maquina, defines the meanings of:

- `off`, `running`, and `broken`;
- `start`, `smelt`, `stop`, `fail`, and `repair`;
- ore, fuel, ingots, heat, wear, and repair parts;
- the game's goals and scoring.

The Lean modules define the typed mode graph, machine schema, queue ports, and
a declarative refueling program. Foundry contains no custom state-transition
functions: the generic Maquina simulator interprets the same process,
operation-effect, process-binding, and queue-binding data for every game.

## Run the trace

```sh
lake exe foundry-demo
```

The executable applies the declarative program one operation at a time and
prints each generic effect receipt plus a readable state snapshot. Its
Foundry-specific code only names accounts and selects balances to display;
all state transitions still come from `Maquina.applyOperation`.

## Defined refueling program

Refueling is expressed as five inert operation proposals:

1. Reserve the process inputs and enqueue into the service input queue.
2. Move the queued process into the service processing queue.
3. Advance the active process by one exact unit of work.
4. Complete into output custody and the production output queue.
5. Bind the collector and atomically deliver every output allocation.

The refuel process consumes ten liters from `provider`, reserves the worker's
unique Body and one unit of labor capacity, produces ten liters for `machine`,
and allocates one service credit each to the operator and collector. Concrete
bindings distinguish source, process custody, output custody, and recipients.

## Initial proof targets

- Smelting cannot execute while the foundry is off or broken.
- Starting changes an off foundry to running.
- Stopping changes a running foundry to off.
- Failure changes a running foundry to broken.
- Repair is possible only while broken.
- Rejected work does not consume inputs or change queue order.
- Queue and slot capacities are never exceeded.
- Completed output is not lost under output backpressure.
- Replaying an accepted command trace reconstructs the same game state.
