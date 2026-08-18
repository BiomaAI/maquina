# Maquina Visualizer

The visualizer is a catalog-driven Three.js presentation of proof-backed
Maquina simulations. It is intentionally split into five boundaries:

```text
Lean simulation
  -> ScenarioArtifact v2
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

## Add a showcase

1. Define a Lean `Visualization.Scenario` from the game's valid initial state
   and operation proposals.
2. Supply a `Visualization.Projection` for the game's names.
3. Supply declarative account, machine, resource, theme, and camera styles.
4. Project the scenario, register its artifact in `ShowcaseExport.lean`, and
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
the simulator's structured issue. Protocol v2 separates non-mutating
precondition checks from transition effects: accepted guards and requirements
carry inspectable evidence, while rejected checks retain their exact structured
failures.
