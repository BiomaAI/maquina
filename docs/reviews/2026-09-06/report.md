Maquina review — September 6, 2026

Maquina has a strong foundation for more engaging games: deterministic commands, resource and custody invariants, receipt-driven animation, and exact forks. The highest-value next step is to connect those guarantees to the actual exported player experience. This review found an observable hidden-information leak, underconstrained command evidence, and permissive artifact validation. Address these alongside a focused interaction pass, then expand one game into a repeatable loop.

This was an investigation, not an implementation change. Only this report and diagnostic evidence were added. No gameplay rules, kernel implementation, generated artifacts, or deployment settings were changed.

Evidence collected:

- `lake build` passed: 115 jobs.
- `pnpm check` passed: generation, 63 tests across five files, TypeScript compilation, and production build.
- All three game executables exited successfully.
- Regenerated artifacts produced no tracked diff.
- Inspected all three command games in the local browser, including Veiled Accord's actual pre-reveal proof details. Reviewed the remaining Foundry traces through their declarations, artifacts, and tests.
- Compiled [BoundaryWitnesses.lean](BoundaryWitnesses.lean), including a counterexample to exported candidate noninterference. Ran [protocol-probes.mjs](protocol-probes.mjs), which demonstrated seven malformed documents accepted by the parser.
- Source search found no explicit `sorry`, `admit`, or custom `axiom` declarations in the reviewed application/kernel Lean sources. This is not a complete dependency axiom audit. The witness's `#print axioms` confirms that some evaluated game results depend on generated `native_decide` axioms.

The browser review used the normal desktop viewport. Mobile layout, screen readers, sustained GPU usage, and arbitrary long histories were not tested. Passing the existing checks does not cover the defects below.

1. **High priority: Veiled Accord leaks hidden outcomes through candidate evidence.**

In the browser, choose “Broadcast harbor-safe claim,” resolve it, and expand “Proof evidence” under “Reveal escort order” before selecting or revealing that order. The UI already shows 8 evacuees going to Sanctuary, 16 to Corridor losses, and the strategic asset going to Partner command. That discloses the partner-dependent outcome while the interface says its order remains hidden.

The cause is [Showcase.lean](../../../games/veiled-accord/lean/VeiledAccordSim/Showcase.lean), `projectCandidate` at line 355: it runs authoritative assessment on the complete state and exports `receiptEffects before applied.receipt`. It does not use the observation-only `safeCommandPolicy` proved in [Command.lean](../../../games/veiled-accord/lean/VeiledAccordSim/Command.lean), lines 195–224. The attached Lean witness proves the existing hidden partner alternative has the same commander observation, yet its exported escort effects show 20 saved and 4 lost instead of 8 saved and 16 lost.

Export every pre-resolution player field from an observation-indexed view, including availability, explanations, effects, metrics, and scene data. Prove equality of the actual export across observation-equivalent states. Redacting only rejected candidates is insufficient. Where hidden state determines success, show an allowed submission with an uncertain outcome rather than secretly evaluating and exposing the result.

The static artifact also includes every future resolution, reveal string, and terminal state. That is appropriate for a counterfactual explorer, but cannot protect a secret from someone inspecting the downloaded file. Distinguish an openly inspectable exploration mode from a future competitive play mode that keeps unrevealed authoritative state outside the client. Hiding a panel alone would not establish confidentiality.

2. **High priority: some proof-carrying command values do not prove execution provenance.**

[Command.lean](../../../lean/Maquina/Command.lean), `AssessedCandidate` at line 60, stores a candidate beside an assessment without an equation connecting that assessment to `executor.apply before candidate.payload`. The normal `assessCandidate` function constructs the intended pair, but the public structure permits other pairs. The attached witness constructs an accepted candidate for an executor that rejects every intent; ordinary assessment of that same candidate rejects it.

`CommandGraphStep` at line 332 carries replay, time advance, and history extension, but does not relate `processed` to its events or to a particular scheduler result. The witness constructs a step with one processed intent and zero events while satisfying all its fields. `firstStepActionsExact` at line 422 compares candidate IDs with processed intent IDs; it does not establish that the scheduled payload, actor attribution, and arbitration data are the selected candidate's intended order. [Projection.lean](../../../visualizer/lean/MaquinaViz/Projection.lean), `projectCommandGraph` at line 449, also accepts unconstrained root strings and projection callbacks; its signature does not enforce the endpoint guarantee described in its comment.

Strengthen the types around evidence returned by actual assessment and scheduling. Require an assessment-to-executor equality or semantic derivation, retain the exact selected order bindings, and derive processed intents/events from an identified `applyTick` result. Make projection IDs and endpoints come from the proved graph, leaving callbacks responsible for presentation. Restrict constructors where that helps, but retain explicit semantic obligations.

These are specification gaps in what arbitrary evidence values guarantee. They do not demonstrate a balance-conservation failure in `applyOperation`, or establish that the shipped scenarios execute substituted commands. The existing constructors follow the intended path; the types should make that requirement explicit.

3. **High priority: artifact validation allows contradictions and malformed nested data.**

[protocol.ts](../../../visualizer/src/protocol.ts), lines 377–438, checks the presence of many arrays without validating their contents. The diagnostic probes all currently print `ACCEPTED`: a numeric holding quantity, missing provenance, a nonnumeric metric, a null machine, an edge whose first state differs from its source node, an edge whose final state differs from its target node, and a rejected trace step whose world changes.

Require complete nested schemas, exact quantity syntax, finite presentation coordinates, unique/reference-valid identities, and the fields the renderer actually consumes. Verify source → first step, adjacent steps, last step → target, and trace continuity. Rejected steps must retain their predecessor and have no transition effects. Invalid artifacts should fail with a precise path before the renderer or `BigInt` conversion runs.

Structural validation is not a Lean proof checker. Bind generated artifacts to explicit semantics/toolchain/exporter versions and build provenance; describe “Lean checked” as a property of that build pipeline. Eventually add canonical serialization and replay/conformance fixtures rather than treating a string such as `semanticStatus` as executable evidence.

4. **Next formal targets: strengthen scheduling, commitment history, and trust accounting.**

[Scheduler.lean](../../../lean/Maquina/Scheduler.lean), `applyTick_deterministic` at line 329, proves equal results after assuming both inputs equal the same function result. That is valid, but it does not prove invariance under a permutation of submitted intents. Add universal theorems for canonical ordering under unique IDs, exact due/future partition, one event per processed intent, contiguous unique event sequences, and preservation of future work. Add commuting-operation results under explicit disjointness premises. State fairness/liveness only with a named scheduling policy and assumptions that rule out permanent resource starvation.

[Strategic.lean](../../../lean/Maquina/Strategic.lean), lines 120–167, binds a reveal to a token under a game-supplied function, without requiring that function to distinguish payloads or proving a prior commitment was stored. In Veiled Accord, `closedRound` constructs tokens and matching payloads together, and is invoked during reveal ([Simulation.lean](../../../games/veiled-accord/lean/VeiledAccordSim/Simulation.lean), lines 249–272 and 430). This checks internal consistency of a constructed round; it does not establish that a player cannot change an earlier committed order. Add explicit commit/close/reveal phases, round-scoped identities, stored commitments, duplicate rejection, and binding across transitions. A future network protocol will also need a separately specified hiding/authentication boundary.

CI should audit theorem dependencies with an explicit axiom policy, fail on unfinished-proof warnings, and distinguish universal kernel proofs from native-evaluated finite scenarios. Add negative construction/serialization cases and end-to-end browser checks covering the actual exported information boundary. Enforce the authoring convention in CI: resource transitions remain declared Processes exposed by typed Operations and submitted through the simulator; Genesis is restricted to initialization. Direct low-level imports in a few game command modules can be cleaned up as part of that enforcement.

The existing proof backlog already tracks authorization/capability binding, projection boundaries, liveness, and runtime conformance. Prioritize the concrete gaps above ahead of recursive packs/bundles: they affect claims made by today's games. Before persistence or external submissions, also specify stale-snapshot rejection, event/schema versions, and the scope of intent identity reuse. Current pending-ID uniqueness is not a lifetime idempotency contract.

The current interaction surface can improve substantially without introducing another transition engine.

| Observed friction | Proposed improvement | Acceptance target |
| --- | --- | --- |
| Veiled Accord advertises escrow as accepted, but selecting escrow alone produces “No modeled resolution.” Its only escrow edge also requires evidence. | Present Lean-exported compatible bundles and dependencies. Explain unsupported combinations before resolution. | Every advertised interaction has an obvious executable path; no trial-and-error checkbox puzzle. |
| Clicking a scene object adds its raw ID above the full holdings list. | Open that object's named holdings, custody, queues, and candidate commands; highlight the affected endpoints when hovering an order. Add a keyboard-accessible object list. | A player can select a station and act on it without translating internal IDs. |
| Dense labels overlap in default desktop views; several Body resources show as `RESOURCE:104`, `RESOURCE:705`, etc. | Complete declarative resource names, prioritize selected/active labels, add collision-aware labels, camera reset/focus, and an optional schematic view. | The current objective and selected objects remain readable in every catalog scene. |
| Command resolution advances on a fixed 1,350 ms timer; transport buttons are disabled in command mode. | Add pause, step, playback speed, and skip-to-result to exported edge playback. Retain every intermediate receipt. | A player can stop on a conflict and inspect it without racing a timer. |
| Proof internals and raw state signatures dominate the inspector; scroll position carries across scene switches. | Put goal, decision, cost, and consequence first; collapse diagnostics, use plain actor/location names, and reset scroll on a new showcase. | First-time players see their next meaningful choice immediately. |
| Terminal comparison is numeric and available only at the end. | Add visited-branch maps, pinned comparisons, synchronized scene differences, and replay links encoding the selected branch. Gate hidden outcomes in play mode. | Players can explain which decision caused a different outcome. |

Further UI correctness work: `main.ts:336` uses an empty candidate list to identify terminals, whereas the protocol permits terminal nodes containing rejected candidates. Use no accepted candidates/no outgoing edges consistently. `selectShowcase` at line 596 has no request-generation guard; rapid changes can allow stale fetch completion to overwrite a newer selection. Add a stale-result guard and recoverable load errors. Preserve expanded proof details and keyboard focus when changing selections. Add reduced-motion handling and profile idle rendering before choosing rendering optimizations; no GPU performance regression was measured in this review.

The most important gameplay constraint is depth. The generated command graphs contain:

| Game | Snapshots / edges | Player decisions to a terminal | Strong next loop |
| --- | --- | --- | --- |
| Foundry Control Room | 17 / 16 | 2–3 | A shift of several production orders: choose lot, station, worker assignment, and maintenance timing under deadlines, wear, and output capacity. |
| Operation Nightglass | 11 / 10 | 2 | Several decision windows along a route: trade scan time, uncertain contacts, ammunition, repairs, and convoy exposure; give Alpha and Bravo materially different roles. |
| Operation Veiled Accord | 10 / 9 | 2 | Repeated negotiations with persistent reputation, scarce evidence, binding escrow, and multiple explicit partner strategies. |

These are design proposals, not implemented features. Foundry is the best first expansion: its existing custody, queues, cancellation, maintenance, and contention provide meaningful tradeoffs without requiring a new information-security architecture. Target roughly 6–10 meaningful decisions in a short shift, with a reason to preserve resources for later orders. Measure whether playthroughs produce different viable schedules, not merely more graph nodes.

For Nightglass, make protection cost time or another limited opportunity so “shield first” is a real choice; let players intervene between hostile/mission continuations instead of automatically consuming the rest of the mission. For Veiled Accord, make trust affect later behavior and escrow enforcement. Today `partnerOrderAfterNegotiation` is a fixed evidence-or-pact response and does not consult `partnerNature`; the named hidden nature does not yet generate varied negotiation behavior through that function. Keep random/hidden scenario choices explicit in authoritative initial conditions or recorded events so replay stays deterministic.

Grow the static explorer with a bounded Lean graph builder that assesses declared candidates, resolves supported order sets through the generic scheduler, and constructs evidence from those results. Track node/edge budgets and exported size; the current three command artifacts are about 225–336 KB each, before compression. Do not merge authoritative snapshots using an actor-visible state key: equivalent observations can hide different states and futures. Share state storage only where semantics justify it, while retaining distinct histories. For unbounded sessions, add an authoritative execution service or a later conformance-checked runtime; JavaScript should continue to submit proposals and render responses.

Recommended delivery order:

1. Close the exported-information leak; strengthen assessment/step provenance and parser checks. Completion requires the present witnesses to become impossible or appropriately rejected, plus an equality theorem for the real pre-reveal export.
2. Improve compatible order selection, object inspection, labels, playback controls, and browser coverage on the existing scenarios.
3. Extend Foundry into a repeatable shift and prove the new lifecycle/economic invariants. Build reusable graph-generation support only as that game needs it.
4. Extend Nightglass decision windows and Veiled Accord commitment/reputation semantics. Add deployment/runtime boundaries when the intended mode requires hidden state to remain secret.

Reproduce the attached diagnostics from the repository root:

```sh
lake env lean docs/reviews/2026-09-06/BoundaryWitnesses.lean
node docs/reviews/2026-09-06/protocol-probes.mjs
```

The Lean file is deliberately a review witness outside normal library targets. It constructs no game-world resource mutations. The JavaScript probes work on cloned artifact data and a temporary transpiled parser; they do not edit checked-in artifacts.
