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

The same scenarios are published through the shared visualization protocol at
[the Maquina simulation atlas](https://biomaai.github.io/maquina/). Foundry's
showcase adapter supplies vocabulary and declarative positions, colors, and
geometry. The generic scene projector and Three.js renderer contain no
Foundry-specific behavior.

## Defined refueling program

Refueling is expressed as seven inert operation proposals:

1. Enter the machine by depositing the unique Body into receipt-backed machine
   custody.
2. Prove the machine holds Body, stage fuel, and enqueue the process.
3. Reserve Labor, bind the declared active Body requirement to an open custody
   position, and dispatch the queued process into processing.
4. Advance the active process by one exact unit of work.
5. Complete into output custody, returning Labor to its source and releasing
   the active Body dependency.
6. Leave the machine by closing custody and returning Body to the source
   recorded by the deposit receipt.
7. Bind the collector and atomically deliver every output allocation without
   requiring Body to remain present.

The refuel process consumes ten liters from `provider`, temporarily reserves
one unit of labor capacity, produces ten liters for `machine`, and allocates
one service credit each to the operator and collector. Body is not a process
input: it is a non-consuming admission requirement plus a process-declared
active-custody dependency. The worker may leave while the job is queued, but
dispatch requires a current Body position and active work prevents that
position from closing.

## Checked scenarios

Lean computes and checks that:

- enqueue is rejected with an exact Body shortfall before the worker enters;
- entering moves Body into machine inventory and opens custody position zero;
- queued work does not pin Body: leaving succeeds, dispatch then rejects with
  the closed position, and re-entry allocates the never-reused position one;
- active refueling binds Body position one, rejects an attempted exit, and
  releases the dependency at completion or cancellation so exit can proceed;
- open custody locks Body against unrelated transfers and debits while still
  allowing non-consuming possession checks;
- a second job can enqueue while the first job holds the only Labor unit;
- dispatching that second job is rejected until the first completion returns
  Labor;
- completing a second job is rejected atomically while the one-slot output
  queue remains full;
- queued and active cancellation return staged fuel, active cancellation also
  returns Labor, and both remove their queue entry atomically;
- the operator allocation can be collected independently, cannot be collected
  twice, and leaves the machine and collector allocations in custody;
- a two-lot fuel/service-credit rate settles atomically, reverses exactly,
  reports exact shortfalls, and cannot spend custody-locked Body;
- every processing-queue entry carries proof that its temporary inputs are
  completely reserved;
- leaving returns the exact Body to the deposit receipt's source;
- output collection succeeds after Body has left the machine;
- unique Body cannot occupy two accounts simultaneously;
- queue capacities, monotonic tickets, and custody IDs remain valid;
- deterministic replay reconstructs the exact one-job and two-job final
  states.
