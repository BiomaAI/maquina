# Lean Process Lifecycle Working Plan

> Status: the first complete lifecycle slice is implemented and checked by
> `lake build`. Keep this note temporary until the vocabulary stabilizes.

## Boundary

Maquina defines generic resource, process, queue, machine, operation, and
simulation semantics. A game supplies names and declarations only. It does not
implement resource-specific transition helpers.

Accounts represent current holding locations. Maquina has no external owner
registry. Persistent return provenance comes from accepted reservation and
machine-custody transfer receipts; transferable rights can themselves be
modeled as resources.

## Resource lifecycle

A process declares three distinct resource flows:

- `consumed`: staged in custody and transformed at completion;
- `reserved`: staged in custody and returned unchanged to the receipt-recorded
  source;
- `outputs`: canonical produced baskets with labeled destinations.

Operations separately declare non-consuming possession requirements. The
simulator observes an exact account and basket in the current world, returns
all structured shortfalls on rejection, and emits an observation receipt on
acceptance. Possession is eligibility only: it neither moves nor locks the
observed resources.

An accepted reservation stores the exact transfer receipt. Its source and
custody are derived from that receipt rather than independently supplied owner
fields. Queue movement preserves the queued process and its reservation
provenance.

Outputs derive their amounts from the canonical process definition. An output
recipient may be bound at admission or deliberately left unresolved. A later
operation can bind a game-defined label, such as a collector, exactly once.
Produced resources remain in output custody until collection transfers every
allocation atomically.

## Generic lifecycle

```text
enter -> observe/stage -> enqueue -> claim/dispatch -> advance
      -> complete -> leave -> collect
```

The generic simulator interprets the declared effects:

1. Machine entry moves a resource into long-lived, receipt-backed custody.
2. Operation requirements are checked atomically before any effects.
3. Admission stages consumed inputs and enqueues the proof-carrying job.
4. Dispatch claims temporary inputs and can construct a processing entry only
   with proof that every canonical reserved port is covered.
5. Advance changes only exact work progress and preserves the FIFO ticket.
6. Completion consumes staged inputs, returns preserved reservations to their
   recorded sources, creates canonical outputs, clears reservation records,
   and either delivers or enqueues allocations.
7. Machine exit reverses the exact custodied basket to the original receipt
   source and closes the monotonic custody position.
8. Collection late-binds declared recipients, transfers every allocation, and
   removes the output entry so it cannot be collected twice.

Reservation release is also an explicit generic effect for queued work. It
returns preserved capabilities and removes their live reservation records.
Active processing entries cannot be constructed without complete temporary
input evidence, so Labor cannot be returned while an active job continues.
Mode changes such as failure do not implicitly release anything.

Queue addition and removal are generic effects. Addition respects the
machine-wide queue maximum and allocates a monotonic stage-specific ID. Removal
requires an existing empty queue, and removed IDs are never reused.

## Current proof inventory

Lean now checks that:

- transfers are funded, atomic, conservative, and replayable;
- debits and credits preserve canonical holdings, catalog validity, and supply
  limits;
- rejected inventory programs expose no successor;
- inventory-program receipts reconstruct their exact successor holdings;
- possession assessment is state-indexed, non-mutating, and reports every
  independent shortfall;
- operation-scoped possession requirements are checked before effects and
  rejected requirements expose no successor;
- two distinct accounts cannot simultaneously hold the same unique resource;
- every live queued reservation matches a canonical process port and the exact
  bound source and custody accounts;
- every input and processing queue entry proves all canonical consumed inputs
  are staged as exact consumed reservations;
- every processing entry proves all canonical temporary inputs are reserved;
- machine custody positions preserve exact receipt provenance, use monotonic
  non-reused IDs, and return the exact basket to its recorded source;
- queues remain within capacity, preserve FIFO order, and never reuse tickets;
- front updates preserve the FIFO ticket;
- machine queue replacement, addition, and removal preserve topology proofs;
- rejected operations expose no successor;
- every accepted operation trace carries a proof that deterministic semantic
  replay reaches its exact final simulator state.

Foundry additionally computes a closed scenario showing that:

- fuel moves from provider custody to the machine;
- unique `WorkerBody` moves into machine custody once and enables repeated
  enqueue operations through non-consuming possession proofs;
- bounded `LaborCapacity` is claimed only at dispatch and returned at
  completion, limiting active work without limiting queued work;
- enqueue fails before Body enters, while collection succeeds after Body
  leaves;
- two jobs use the same present Body sequentially while the second dispatch is
  rejected until Labor returns;
- operator and late-bound collector allocations are delivered once;
- a second collection is rejected;
- input, processing, and output queues drain;
- adding and removing an upgrade queue respects the maximum and advances the
  monotonic queue ID.

## Remaining work

The canonical list of current proof gaps, future semantics, and runtime
conformance work is maintained in
[`lean-proof-todo.md`](lean-proof-todo.md). In particular, the backlog
distinguishes current implementations that still need stronger universal
theorems from semantics—such as time, events, forks, and exchanges—that have
not been implemented yet.
