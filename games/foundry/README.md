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

The Lean modules now define the typed mode graph, machine schema, queue ports,
and a declarative refueling program. Foundry contains no simulator or custom
state-transition functions: a future generic Maquina simulator will interpret
the same process, operation-effect, process-binding, and queue-binding data for
every game.

## Defined refueling program

Refueling is expressed as four inert operation proposals:

1. Reserve the process inputs and enqueue into the service input queue.
2. Move the queued process into the service processing queue.
3. Advance the active process by one exact unit of work.
4. Complete directly into bound inventories, without using an output queue.

The refuel process declares ten liters from `provider` as input and ten liters
to `machine` as output. Concrete process bindings distinguish the provider,
escrow custody, and machine inventory accounts.

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
