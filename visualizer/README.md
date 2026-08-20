# Maquina Visualizer

The visualizer is a catalog-driven Three.js presentation of proof-backed
Maquina simulations. It is intentionally split into five boundaries:

```text
Lean simulation
  -> ScenarioArtifact v3
     -> optional immutable CommandGraphView
  -> generic SceneDocument
  -> semantic primitive composition
  -> Three.js renderer
```

- `lean/MaquinaViz/Protocol.lean` defines the versioned browser contract.
- `lean/MaquinaViz/Projection.lean` projects generic simulator states and
  receipts without knowing any game vocabulary.
- Each game may provide a thin showcase adapter containing names, scenarios,
  and declarative presentation. Foundry's adapter is
  `games/foundry/lean/FoundrySim/Showcase.lean`.
- `src/scene.ts` converts any protocol document into renderer-neutral scene
  nodes, addressable anchors, links, and motions. Anchors let transfers target
  non-rendered account aliases such as a machine inventory.
- `src/three-shapes.ts` composes accounts, machines, queues, resources,
  processes, and custody from reusable Three.js primitives. Shape selection is
  semantic but remains independent of any game identity.
- `src/three-renderer.ts` renders only the scene document. It has no access to
  a game's rules or identity. Curved route flow, effect particles, semantic
  highlights, and label stems are all derived from the shared scene data.
- `src/command.ts` contains game-neutral exact action-set matching, immutable
  branch-trail navigation, and exact-decimal metric comparison. It executes no
  transition rule.

## Counterfactual command graphs

`ScenarioArtifact.commandGraph` is an optional additive v3 field. A game may
export actor-scoped nodes containing projected states, metrics, and structured
candidate assessments, plus resolution edges containing the exact action set
and one or more already-resolved `StepView` ticks.

The protocol parser rejects malformed graphs before rendering: node and edge
identities must be unique, the root and every edge endpoint must exist, action
sets must be nonempty and unambiguous per source, every action must reference
an accepted source candidate, the first scheduler tick must exactly match the
selected action IDs, every accepted candidate must occur in an outgoing
resolution, and terminal status must agree exactly with the absence of
accepted candidates and outgoing edges. Every resolution contains at least one
validated replay step. Rejected candidates remain inspectable but cannot be
selected.

Catalog entries declare `trace`, `commandable`, or `both` capability. Command
mode is shown only for artifacts that actually carry a command graph. Candidate
proof details are collapsible and the exact-order resolution control remains
sticky while browsing longer assessments.

The browser can select an exact order set, animate its exported steps, rewind
the branch trail, and compare terminal metrics. It cannot invent a successor,
resolve an unmodeled combination, or evaluate game policy. This keeps static
GitHub Pages a presentation of Lean-owned counterfactuals rather than a second
runtime.

## Add a showcase

1. Define a Lean `Visualization.Scenario` for a generic simulator trace or a
   `Visualization.ApplicationScenario` for a game-owned composite state,
   timeline, or other application transition.
2. Supply a `Visualization.Projection` for each simulator runtime the game
   wants to expose, then combine those generic state views in the game adapter.
3. Supply declarative account, machine, resource, theme, and camera styles.
4. For command mode, instantiate `Maquina.CommandGraph` and project game-owned
   labels and receipts through the shared `projectCommandGraph` adapter.
5. Register the artifact and its capability in `ShowcaseExport.lean`, then
   regenerate the catalog.

No visualizer conditional or custom Three.js renderer is required. A game with
an unusual presentation may add a projector that still produces the shared
`SceneDocument`.

## Develop and validate

From this directory:

```sh
pnpm install
pnpm generate
pnpm dev
pnpm check
```

Exact resource quantities remain decimal strings across the JSON and
JavaScript boundary. Accepted steps are derived from proof-backed
`AppliedOperation` values; rejected steps retain the unchanged state and expose
the simulator's structured issue. Protocol v3 separates non-mutating
precondition checks from transition effects: accepted guards and requirements
carry inspectable evidence, while rejected checks retain their exact structured
failures.

Protocol v3 represents machines as a list without prescribing how a game stores
or composes them. Application scenarios can also carry logical ticks, event
sequences, intent identities, mixed accepted/rejected arbitration results,
mode-specific positions, activities, and generic geometry variants. The
renderer consumes only that shared protocol and never imports game rules.
