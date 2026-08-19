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

Processes may additionally declare `activeCustody` ports. These are not input
reservations: dispatch binds each port to an existing receipt-backed machine
custody position and active work carries the exact bindings. The simulator
state proves every live dependency remains open and sufficiently funded.
Queued work has no such dependency, so a game can require Body for admission
without forcing the worker to remain while waiting. Dispatch requires current
presence; completion or active cancellation releases it.

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
   with proof that every canonical reserved port is covered and every declared
   active-custody port is bound to an open covering position.
5. Advance changes only exact work progress and preserves the FIFO ticket.
6. Completion consumes staged inputs, returns preserved reservations to their
   recorded sources, creates canonical outputs, clears reservation records,
   and either delivers or enqueues allocations.
7. Machine exit reverses the exact custodied basket to the original receipt
   source and closes the monotonic custody position, but only when no active
   process depends on that position.
8. Collection late-binds declared recipients, transfers every allocation, and
   removes the output entry so it cannot be collected twice.

Collection may also target one labeled allocation. The remaining allocation
list is proof-carrying and label-unique; removing a label proves it is absent
from the successor while the original FIFO ticket and unresolved custody stay
in place.

Reservation release is also an explicit generic effect for queued work. It
returns preserved capabilities and removes their live reservation records.
Active processing entries cannot be constructed without complete temporary
input evidence, so Labor cannot be returned while an active job continues.
Mode changes such as failure do not implicitly release anything.

Queued and active cancellation are separate generic effects. A declaration
chooses whether consumed inputs are returned or transformed as consumed;
temporary reservations are returned in either consuming cancellation. The
resource program and queue removal form one atomic operation transition.

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
- operation-scoped possession requirements are checked exhaustively before
  effects, carry stable declaration indices, and rejected requirements expose
  the exact canonical nonempty failure list with no successor;
- game-declared operation guards have proof-carrying acceptance, inspectable
  positive evidence, and exhaustive exact rejection issues;
- two distinct accounts cannot simultaneously hold the same unique resource;
- one authoritative world owns uniquely identified machines with distinct
  inventory accounts, and every world operation explicitly targets one ID;
- accepted targeted operations preserve every unrelated machine runtime and
  use exact receipt isolation to retain its custody-backing proof;
- missing targets and rejected targeted operations expose no world successor;
- ordered world transactions either commit every intent with exact shared
  receipt replay or expose no successor at the first rejected intent;
- a unique resource cannot simultaneously occupy two distinct machines;
- every live queued reservation matches a canonical process port and the exact
  bound source and custody accounts;
- every input and processing queue entry proves all canonical consumed inputs
  are staged as exact consumed reservations;
- every processing entry proves all canonical temporary inputs are reserved;
- every processing entry carries exactly its process-declared active-custody
  dependencies, and every dependency is proven open and covering in the
  simulator state;
- successful completion carries an exact debit, return, and output receipt
  contract and preserves every unrelated account/resource balance;
- successful allocation delivery is complete and receipt-sound, and a removed
  output ticket cannot recur in its successor queue;
- machine custody positions preserve exact receipt provenance, use monotonic
  non-reused IDs, remain aggregate-backed by locked machine balances, and
  return the exact basket to their recorded source only when no active process
  references them;
- queues remain within capacity, preserve FIFO order, and never reuse tickets;
- front updates preserve the FIFO ticket;
- machine queue replacement, addition, and removal preserve topology proofs;
- rejected operations expose no successor;
- every accepted operation trace carries a proof that deterministic semantic
  replay reaches its exact final simulator state;
- every accepted trace also carries proposal-free direct receipts whose world
  effects are folded from transfer/transformation receipts and whose explicit
  non-world patches reconstruct exact final simulator data.

Foundry additionally computes a closed scenario showing that:

- fuel moves from provider custody to the machine;
- unique `WorkerBody` moves into machine custody and enables repeated
  enqueue operations through non-consuming possession proofs;
- queued work permits Body to leave, dispatch rejects while Body is absent,
  re-entry uses a fresh custody ID, and active work blocks Body exit until
  completion or cancellation;
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
- stopping and repair require idle processing, reactive failure requires active
  processing, rejected guards explain the observed boundary, and accepted
  failure atomically cancels active work before entering the broken mode.
- two machines share one authoritative world, the first targeted entry acquires
  the unique Body, the second reports an exact shortfall without mutation, and
  a contended two-intent transaction exposes no successor.

## Remaining work

The canonical list of current proof gaps, future semantics, and runtime
conformance work is maintained in
[`lean-proof-todo.md`](lean-proof-todo.md). In particular, the backlog
distinguishes current implementations that still need stronger universal
theorems from semantics—such as time, events, and forks—that have not been
implemented yet.
