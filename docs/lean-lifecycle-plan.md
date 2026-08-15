# Lean Process Lifecycle Working Plan

> Status: the first complete lifecycle slice is implemented and checked by
> `lake build`. Keep this note temporary until the vocabulary stabilizes.

## Boundary

Maquina defines generic resource, process, queue, machine, operation, and
simulation semantics. A game supplies names and declarations only. It does not
implement resource-specific transition helpers.

Accounts represent current holding locations. Maquina has no external owner
registry. Persistent return provenance comes from an accepted reservation;
transferable rights can themselves be modeled as resources.

## Resource lifecycle

A process declares three distinct resource flows:

- `consumed`: staged in custody and transformed at completion;
- `reserved`: staged in custody and returned unchanged to the receipt-recorded
  source;
- `outputs`: canonical produced baskets with labeled destinations.

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
reserve -> enqueue -> dispatch -> advance -> complete -> collect
```

The generic simulator interprets the declared effects:

1. Reservation atomically moves consumed and reserved inputs into custody.
2. Enqueue admits the proof-carrying job to a direction-typed FIFO queue.
3. Dispatch preserves its identity and bindings while moving it to processing.
4. Advance changes only exact work progress and preserves the FIFO ticket.
5. Completion consumes staged inputs, returns preserved reservations to their
   recorded sources, creates canonical outputs, clears reservation records,
   and either delivers or enqueues allocations.
6. Collection late-binds declared recipients, transfers every allocation, and
   removes the output entry so it cannot be collected twice.

Reservation release is also an explicit generic effect. It returns preserved
capabilities and removes their live reservation records. Mode changes such as
failure do not implicitly release anything; games compose the effects they
intend.

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
- two distinct accounts cannot simultaneously hold the same unique resource;
- every live queued reservation matches a canonical process port and the exact
  bound source and custody accounts;
- queues remain within capacity, preserve FIFO order, and never reuse tickets;
- front updates preserve the FIFO ticket;
- machine queue replacement, addition, and removal preserve topology proofs;
- rejected operations expose no successor;
- every accepted operation trace carries a proof that deterministic semantic
  replay reaches its exact final simulator state.

Foundry additionally computes a closed scenario showing that:

- fuel moves from provider custody to the machine;
- a unique `WorkerBody` and bounded `LaborCapacity` become unavailable during
  reservation and return at completion;
- a second concurrent reservation is rejected while the Body is in custody;
- operator and late-bound collector allocations are delivered once;
- a second collection is rejected;
- input, processing, and output queues drain;
- adding and removing an upgrade queue respects the maximum and advances the
  monotonic queue ID.

## Remaining work

- Replace the current boolean guard callback with proof-carrying structured
  guard assessment and explanations.
- Give full operation receipts a direct effect-replay format in addition to
  deterministic semantic replay of their recorded proposals.
- Add explicit cancellation effects for removing queued jobs after releasing
  or transforming their staged inputs.
- Generalize partial allocation collection when different recipients collect
  independently.
- Add rates, exchanges, pack/bundle conversion, deterministic time, event
  storage, snapshots, and forks on top of the proved lifecycle boundary.
- Design the Rust kernel only after these Lean semantics settle.
