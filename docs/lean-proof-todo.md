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

- [ ] **Consumed-input completeness.** Add evidence analogous to
  `ReservedInputsComplete` proving that every canonical consumed port is staged
  before an input-queue entry can be constructed. The simulator currently
  stages all consumed ports, but the queue entry type does not express that
  completeness invariant independently.
- [ ] **Continuous custody backing.** Relate every open `MachineCustody`
  position to the current `WorldState`, proving that its receipt-derived basket
  remains held by the machine or is locked against unrelated transfer. Current
  custody proves receipt provenance and exact return when funded; closing
  correctly rejects if the held basket is no longer available.
- [ ] **Direct effect-receipt replay.** Replay recorded possession, transfer,
  transformation, queue, and custody effect receipts directly and prove they
  reconstruct the exact successor. Current operation replay deterministically
  re-executes the recorded proposal.
- [ ] **Universal requirement-rejection theorem.** Prove directly that any
  unsatisfied operation possession requirement prevents all effects and yields
  no successor. The interpreter ordering and Foundry examples exhibit this,
  while the current generic rejection theorem only characterizes the public
  successor API after a known rejection.
- [ ] **Universal completion theorem.** Prove that completion consumes every
  staged consumed input, returns every temporary reservation, creates exactly
  the canonical output allocations, and preserves all unrelated balances.
- [ ] **Universal collection theorem.** Prove that successful collection
  delivers every bound allocation exactly once and that a collected output
  entry has no second successor.
- [ ] **Atomic trace rejection theorem.** Expose a trace-successor API and prove
  that failure at any suffix returns no partially applied authoritative state.
  `applyOperations` is pure and currently exposes no failed successor, but this
  contract should have a named theorem.
- [ ] **Cancellation.** Define queued cancellation that releases or transforms
  staged inputs and removes the queue entry atomically. Define active
  cancellation so capability release and processing-entry removal cannot be
  separated.
- [ ] **Partial output collection.** Allow independent recipients to collect
  separate allocations while proving that each allocation is delivered at
  most once and unresolved allocations remain in custody.

## P1 — Rule and machine semantics

- [ ] Replace the boolean game-guard callback with structured guard assessment,
  proof-carrying acceptance, and exhaustive rejection explanations.
- [ ] Prove operation requirement assessment reports every independent failure
  across multiple required baskets and accounts.
- [ ] Prove queue backpressure leaves processing state and staged outputs
  unchanged until output capacity becomes available.
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
