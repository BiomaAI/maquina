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
- normalized multi-account transactions use canonical account/resource order,
  collect indexed independent failures, expose no rejected successor, replay
  exact accepted holdings, and preserve every unmentioned balance;
- `MachineRuntime` separates machine-local mode, queue, custody, and counters
  from authoritative accounts, leaving component topology to each game;
- generic receipt-isolation theorems preserve custody backing for every runtime
  whose inventory account is untouched by an accepted operation or account
  transaction;
- a unique resource cannot simultaneously occupy two distinct runtime
  inventory accounts;
- logical ticks and scheduled opaque application intents contain no wall-clock
  dependency, and pending intent identities are unique by construction;
- due intents are canonically ordered by tick, game-owned arbitration key, and
  stable identity after all are assessed against the unchanged tick snapshot;
- every due intent emits one immutable accepted, snapshot-invalid, or
  conflict-losing event; rejected events replay as identity and every applied
  tick carries exact complete-state replay evidence;
- command candidates are actor-addressed and assessed through the same
  authoritative executor, with proof-carrying acceptance or complete rejection
  issues and no rejected successor;
- simultaneous command order sets require unique stable identities and an
  explicitly empty pending boundary, then resolve through the ordinary
  canonical scheduler;
- timeline snapshots replay their complete immutable histories from one
  origin, while every resolved fork proves its child history is the exact
  parent prefix plus the newly emitted tick events;
- actor observation policies prove their returned projection is permitted;
  Nightglass additionally proves observation noninterference for all state
  fields outside its declared commander-visible relation;
- actor-safe command policies construct candidate surfaces only from declared
  observations, so observation-equivalent states expose identical visible
  availability and explanations;
- information sets check indistinguishable authoritative alternatives against
  the observation policy, and observation strategies cannot choose differently
  inside one information set;
- audience-scoped messages filter immutable claims without promoting message
  content to truth, while closed sealed rounds bind actor-unique reveals to
  opaque commitments;
- joint agreements carry exact multi-party approval and use ordinary
  machine-independent account transactions for resource escrow;
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
- Foundry owns a two-station workcell over one account state: the first station
  acquires the unique Body, the second reports an exact shortfall without
  mutation, and accepted station operations preserve the other's local runtime.

Operation Nightglass additionally computes a closed scenario showing that:

- one radar, two batteries, and one convoy use distinct game-owned mode graphs
  over one authoritative account state;
- sixteen scheduled intents resolve over nine exact logical ticks with stable
  event sequences;
- reversed contender submission still gives the same targeting-channel winner;
- snapshot-valid losing contenders emit explicit conflict events without
  overspending the unique channel or mutating the tentative successor;
- ammunition and repair costs are atomic account transactions;
- damage and repair are checked independently from the victory trace;
- the convoy extracts with all evacuees, two remaining interceptors, and no
  pending intents; and
- concatenated immutable events replay the complete heterogeneous final state.
- a bounded command graph exposes eleven replayable snapshots, ten exact
  order-set resolutions, structured rejected candidates, four terminal outcome
  classes, immutable sibling prefixes, deterministic declaration-order
  independence, actor-visible equivalent histories, unique-channel and
  evacuee conservation, and bounded consumable spending.

Operation Veiled Accord additionally computes a closed strategic game showing
that:

- an unverified defense promise and route claim remain inert cheap talk;
- a unique intelligence seal moves through an account transaction and becomes
  a costly, actor-scoped verified signal;
- a two-party accord has exact consent and moves two defense tokens into
  machine-independent escrow;
- an opportunistic and cooperative partner order are indistinguishable at the
  sealed decision point and expose the same actor-safe candidate surface;
- an unauthorized outsider cannot observe the verified coalition message;
- a closed round contains two commitment-bound reveals with unique actors;
- cooperation after cheap talk can be exploited, mutual defection collapses
  the corridor, costly evidence coordinates partial success, evidence plus
  escrow supports the Pareto outcome, and betrayal destroys credibility; and
- all command paths extend immutable histories, replay exact application state,
  conserve the unique evidence seal and strategic asset, and settle the exact
  twenty-four-evacuee edition across sanctuary and loss accounts.

## Remaining work

The canonical list of current proof gaps, future semantics, and runtime
conformance work is maintained in
[`lean-proof-todo.md`](lean-proof-todo.md). In particular, the backlog
distinguishes current implementations that still need stronger universal
theorems from semantics not yet implemented. Snapshots, forks, structured
candidate assessment, and actor-scoped observation policies now have their
first generic kernel and downstream command-graph witness.
