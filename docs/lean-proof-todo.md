# Lean Proof Backlog

This is the canonical backlog for semantics that remain unimplemented or not
yet proven at the desired level of generality. Completed properties belong in
the root README and the lifecycle proof inventory; incomplete properties stay
here until their Lean theorem and executable scenario both exist.

## Proof status vocabulary

- **Invariant by construction**: a structure contains the proof required to
  construct a valid value.
- **Universal theorem**: the property is quantified over every value satisfying
  its premises.
- **Closed proof**: `native_decide` or reduction proves one fully concrete
  scenario. This is stronger than an external test but does not generalize to
  every trace.
- **Executable observation**: CLI output helps humans inspect behavior. Logs are
  not themselves proofs.

## P0 — Close gaps in the current lifecycle

- [x] **Consumed-input completeness.** `ConsumedInputsComplete` proves that
  every canonical consumed port has an exact consumed reservation. Input and
  processing queue entries require that evidence to be constructed; adding or
  releasing temporary reservations preserves it. This is an invariant by
  construction. The stronger universal completion theorem remains separate
  below.
- [x] **Continuous custody backing.** Every `SimulatorState` carries
  `MachineCustody.Backed`, relating the aggregate per-resource locks of all open
  positions to current machine balances. Transfers and inventory debits assess
  only unlocked balance and preserve backing; opening increases balance and
  lock equally, while closing releases only the selected lock before returning
  its exact receipt-derived basket. Foundry checks that its held Body has zero
  unlocked balance and cannot be transferred to an unrelated account.
- [ ] **Direct effect-receipt replay.** Replay recorded possession, transfer,
  transformation, queue, and custody effect receipts directly and prove they
  reconstruct the exact successor. Current operation replay deterministically
  re-executes the recorded proposal.
- [x] **Universal requirement-rejection theorem.**
  `applyOperation_requirementsRejected` quantifies over arbitrary schemas,
  states, proposals, evaluators, and possession failures, proving failed
  requirements return exactly `possessionRejected` before effect execution.
  Together with `operationSuccessor_rejected`, no successor is exposed.
- [x] **Universal completion theorem.** `ProcessCompletion.contract` proves
  every staged consumed entry has its exact debit receipt, every temporary
  reservation has an exact reverse-transfer receipt, every canonical output
  entry has its exact credit receipt, no undeclared transformation or return
  receipt exists, reservation records are cleared, and every key untouched by
  those exact plans preserves its balance.
- [x] **Universal collection theorem.** `AllocationDelivery` proves every
  allocation is either already at its bound recipient or has an exact transfer
  receipt, while every emitted receipt corresponds to a declared allocation.
  `Queue.dequeue_removedTicket_absent` proves the collected queue ticket is
  absent from the successor and cannot be delivered from that queue twice.
- [x] **Atomic trace rejection theorem.** `operationTraceSuccessor` exposes only
  a fully successful trace state, and `operationTraceSuccessor_rejected` proves
  any failed suffix yields `none`; locally computed prefix states never become
  an authoritative result.
- [x] **Cancellation.** `cancelInput` and `cancelProcessing` are generic
  operation effects with an explicit `returnInputs` or `consumeInputs`
  disposition. Resource reversal/transformation completes before the input or
  processing entry is removed inside one pure operation transition; any
  rejected suffix exposes no successor. Foundry checks queued fuel return and
  active fuel-plus-Labor return with queue drainage.
- [ ] **Partial output collection.** Allow independent recipients to collect
  separate allocations while proving that each allocation is delivered at
  most once and unresolved allocations remain in custody.

## P1 — Rule and machine semantics

- [ ] Replace the boolean game-guard callback with structured guard assessment,
  proof-carrying acceptance, and exhaustive rejection explanations.
- [ ] Prove operation requirement assessment reports every independent failure
  across multiple required baskets and accounts.
- [x] Prove output backpressure has no partial successor.
  `Queue.assessAndEnqueue_atCapacity` universally rejects every bounded queue
  at capacity, while `operationSuccessor_outputBackpressure` proves an
  interpreter-detected output rejection exposes no successor. Foundry checks
  the boundary with one completed output and one still-processing job.
- [ ] Prove machine entry is impossible for a unique Body already held by any
  other account in a shared multi-machine world.
- [ ] Define machine-session policies such as whether queued or active work
  prevents custody closure, while keeping the policy game-declared.
- [ ] Add first-class rates and atomic multi-account exchanges, including exact
  shortfalls, conservation, receipts, and reverse/custody exchanges.
- [ ] Add packs, bundles, and recursive expansion with termination,
  conservation, and canonical-normalization proofs.

## P2 — Time, concurrency, and history

- [ ] Define deterministic time and a generic tick/scheduler semantics.
- [ ] Prove scheduled and reactive operation ordering is deterministic for an
  explicit conflict-resolution policy.
- [ ] Model multiple machines over one authoritative world rather than one
  machine per `SimulatorState`.
- [ ] Define simultaneous intent assessment and prove conflict resolution does
  not overspend resources or queue capacity.
- [ ] Define immutable events distinct from operation receipts.
- [ ] Prove event replay reconstructs authoritative state.
- [ ] Define snapshots and prove restore-plus-suffix replay equals full replay.
- [ ] Define forks and prove a fork shares its exact prefix while mutations
  after the fork cannot affect sibling histories.
- [ ] State fairness or liveness properties only after scheduling policy is
  explicit; the current kernel proves safety and replay, not eventual progress.

## P3 — Observation and authorization boundaries

- [ ] Define actor-scoped observations and prove hidden state cannot influence
  the returned projection except through explicitly permitted information.
- [ ] Define valid-action projections and prove every advertised action passes
  the same authoritative assessment when applied to the unchanged state.
- [ ] Decide which capabilities are ordinary transferable resources and which
  policies require non-transferable bindings; do not add an external authority
  registry implicitly.
- [ ] Prove derived indexes and projections cannot mutate or redefine
  authoritative transition validity.

## P4 — Runtime conformance

- [ ] Design the Rust kernel only after the corresponding Lean vocabulary is
  stable.
- [ ] Export deterministic Lean fixtures for accepted and rejected transfers,
  transformations, queues, custody, and complete operation traces.
- [ ] Run the same fixtures against Rust and require exact state, issue, and
  receipt parity.
- [ ] Add property-based runtime tests whose expected invariants come from the
  Lean specification.
- [ ] Define versioning rules so persisted events cannot silently change
  meaning when the semantic specification evolves.

## Definition of done for a backlog item

An item is complete when:

1. its semantics are represented as inert generic data where appropriate;
2. accepted construction carries the required invariant evidence;
3. rejection exposes structured issues and no successor;
4. the universal theorem is checked without `sorry` or `admit`;
5. at least one downstream game supplies a closed accepted scenario and a
   closed rejected or boundary scenario;
6. deterministic replay is extended when the new semantics mutate state; and
7. `lake build` and the runnable game trace remain clean.
