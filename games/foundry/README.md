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
- one or more processing slots;
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

The initial Lean module records the typed mode graph. It will be connected to
generic Maquina machine schemas, queues, processes, and operations as those
foundations are introduced.

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
