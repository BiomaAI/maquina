import { readFileSync } from "node:fs";
import { describe, expect, it } from "vitest";
import type { ScenarioArtifact, StateView } from "./protocol";
import { parseArtifact, parseCatalog } from "./protocol";
import { projectScene } from "./scene";
import { QUEUE_FOOTPRINT } from "./three-shapes";

const QUEUE_CLEARANCE = 0.5;

function fixture(name: string): unknown {
  const url = new URL(`../public/generated/${name}`, import.meta.url);
  return JSON.parse(readFileSync(url, "utf8")) as unknown;
}

function catalogArtifact(path: string): ScenarioArtifact {
  const url = new URL(`../public/${path}`, import.meta.url);
  return parseArtifact(JSON.parse(readFileSync(url, "utf8")) as unknown);
}

function crossComponentQueueLayout(
  artifact: ScenarioArtifact,
  state: StateView,
): { comparisons: number; overlaps: string[] } {
  const ownerByQueue = new Map(
    state.machines.flatMap((machine) =>
      machine.queues.map((queue) => [queue.id, machine.id] as const),
    ),
  );
  const queues = projectScene(artifact, state).nodes.filter((node) => node.kind === "queue");
  const overlaps: string[] = [];
  let comparisons = 0;

  for (const [index, left] of queues.entries()) {
    const leftOwner = ownerByQueue.get(left.id);
    for (const right of queues.slice(index + 1)) {
      const rightOwner = ownerByQueue.get(right.id);
      if (leftOwner === undefined || rightOwner === undefined || leftOwner === rightOwner) continue;
      comparisons += 1;

      const separatedOnX = Math.abs(left.position.x - right.position.x)
        >= QUEUE_FOOTPRINT.width + QUEUE_CLEARANCE;
      const separatedOnZ = Math.abs(left.position.z - right.position.z)
        >= QUEUE_FOOTPRINT.depth + QUEUE_CLEARANCE;
      if (!separatedOnX && !separatedOnZ) {
        overlaps.push(`${leftOwner}/${left.id} overlaps ${rightOwner}/${right.id}`);
      }
    }
  }

  return { comparisons, overlaps };
}

describe("Lean-owned showcase artifacts", () => {
  it("publishes the curated Maquina Playground order", () => {
    const catalog = parseCatalog(fixture("catalog.v4.json"));
    expect(catalog.schemaVersion).toBe(4);
    expect(catalog.entries.map((entry) => entry.id)).toEqual([
      "veiled-accord",
      "nightglass-extraction",
      "foundry-control-room",
      "foundry-workcell-body-contention",
      "foundry-refuel-lifecycle",
      "foundry-operating-guards",
      "foundry-active-presence",
    ]);
    expect(catalog.entries.map((entry) => entry.capability)).toEqual([
      "commandable", "both", "commandable", "trace", "trace", "trace", "trace",
    ]);
  });

  it("treats missing additive catalog capability as a fixed trace", () => {
    const raw = structuredClone(fixture("catalog.v4.json")) as {
      entries: Array<Record<string, unknown>>;
    };
    delete raw.entries[0]!.capability;
    expect(parseCatalog(raw).entries[0]?.capability).toBe("trace");
  });

  it("retains exact decimal quantities and replay provenance", () => {
    const artifact = parseArtifact(fixture("foundry-refuel-lifecycle.v4.json"));
    expect(typeof artifact.initial.nextProcessId).toBe("string");
    expect(artifact.steps).toHaveLength(7);
    expect(artifact.steps.every((step) => step.semanticStatus.startsWith("lean-"))).toBe(true);
    expect(artifact.steps.flatMap((step) => step.checks).some((check) => check.condition === "possession")).toBe(true);
    expect(artifact.steps.flatMap((step) => step.effects).some((effect) => effect.kind === "transfer")).toBe(true);
  });

  it("treats the additive command graph field as absent for trace-only v4 producers", () => {
    const raw = fixture("foundry-refuel-lifecycle.v4.json") as Record<string, unknown>;
    const { commandGraph: _commandGraph, ...withoutCommandGraph } = raw;
    expect(parseArtifact(withoutCommandGraph).commandGraph).toBeNull();
  });

  it("represents rejections as unchanged states with no effects", () => {
    const artifact = parseArtifact(fixture("foundry-active-presence.v4.json"));
    const rejected = artifact.steps.filter((step) => step.status === "rejected");
    expect(rejected).toHaveLength(2);
    for (const step of rejected) {
      expect(step.after).toEqual(step.before);
      expect(step.effects).toEqual([]);
      expect(step.issues.length).toBeGreaterThan(0);
      expect(step.semanticStatus).toBe("lean-rejected-no-successor");
    }
  });

  it("exports accepted evidence and exact structured guard failures", () => {
    const artifact = parseArtifact(fixture("foundry-operating-guards.v4.json"));
    const checks = artifact.steps.flatMap((step) => step.checks);
    expect(checks.some((check) => check.condition === "processing-idle" && check.status === "accepted")).toBe(true);
    expect(checks.some((check) => check.condition === "processing-active" && check.status === "accepted")).toBe(true);
    expect(checks.some((check) => check.issues.some((issue) => issue.code === "active-work-present"))).toBe(true);
    expect(checks.some((check) => check.issues.some((issue) => issue.code === "active-work-missing"))).toBe(true);
  });

  it("projects a game-owned workcell over one authoritative account state", () => {
    const artifact = parseArtifact(fixture("foundry-workcell-body-contention.v4.json"));
    expect(artifact.initial.machines).toHaveLength(2);
    expect(artifact.steps).toHaveLength(2);
    expect(artifact.steps[0]?.status).toBe("accepted");
    expect(artifact.steps[0]?.semanticStatus).toBe("lean-proved-direct-replay");
    expect(artifact.steps[1]?.status).toBe("rejected");
    expect(artifact.steps[1]?.after).toEqual(artifact.steps[1]?.before);
    expect(artifact.steps[1]?.effects).toEqual([]);
    expect(artifact.steps[1]?.issues.some((issue) => issue.code === "transfer-rejected")).toBe(true);
    expect(artifact.provenance.guarantees).toContain(
      "unique resources cannot occupy two distinct inventory accounts",
    );
  });

  it("exports deterministic Nightglass ticks, conflicts, and final extraction", () => {
    const artifact = parseArtifact(fixture("nightglass-extraction.v4.json"));
    expect(artifact.presentation.machines.map((machine) => machine.geometry)).toEqual([
      "radar", "battery", "battery", "convoy",
    ]);
    expect(artifact.steps.map((step) => step.logicalTick)).toEqual([
      "0", "1", "2", "3", "4", "5", "6", "7", "8",
    ]);
    expect(artifact.steps.filter((step) => step.status === "mixed")).toHaveLength(2);
    expect(artifact.steps.flatMap((step) => step.eventSequences)).toEqual(
      Array.from({ length: 16 }, (_, index) => String(index)),
    );
    expect(artifact.steps[2]?.checks.some((check) =>
      check.kind === "scheduler" && check.status === "rejected"
    )).toBe(true);
    expect(artifact.steps[4]?.checks.some((check) =>
      check.kind === "scheduler" && check.condition === "enter route two"
        && check.status === "rejected"
    )).toBe(true);
    expect(artifact.steps[2]?.checks.some((check) =>
      check.kind === "game-policy" && check.condition === "contact-tracked"
        && check.status === "accepted"
    )).toBe(true);
    expect(artifact.steps[4]?.after.machines.find((machine) =>
      machine.id === "machine:nightglass:convoy"
    )?.mode).toBe("convoy-damaged");
    expect(artifact.steps[5]?.after.machines.find((machine) =>
      machine.id === "machine:nightglass:convoy"
    )?.mode).toBe("convoy-route-one");
    expect(artifact.steps.at(-1)?.after.logicalTick).toBe("9");
    expect(artifact.steps.at(-1)?.after.pendingIntents).toBe("0");
    expect(artifact.steps.at(-1)?.after.machines.find((machine) =>
      machine.id === "machine:nightglass:convoy"
    )?.mode).toBe("convoy-extracted");
    expect(artifact.provenance.guarantees).toContain(
      "mission vocabulary and component composition remain game-owned",
    );
  });

  it("exports a lively Foundry command world over shared accounts and isolated runtimes", () => {
    const artifact = parseArtifact(fixture("foundry-control-room.v4.json"));
    const graph = artifact.commandGraph;
    expect(graph).not.toBeNull();
    if (!graph) return;

    expect(artifact.initial.machines).toHaveLength(2);
    expect(graph.nodes.length).toBeGreaterThan(80);
    expect(graph.resolutions.length).toBe(graph.nodes.length - 1);
    expect(new Set(graph.nodes.filter((node) => node.candidates.length === 0)
      .map((node) => node.outcome))).toEqual(new Set([
      "productive", "recovered", "conserved",
    ]));
    const simultaneous = graph.resolutions.filter((resolution) => resolution.actionIds.length > 1);
    expect(simultaneous.some((resolution) => resolution.steps[0]?.status === "accepted")).toBe(true);
    const conflicts = simultaneous.filter((resolution) => resolution.steps[0]?.status === "mixed");
    expect(conflicts).toHaveLength(2);
    expect(conflicts.every((resolution) => resolution.steps[0]?.checks.some(
      (check) => check.kind === "scheduler" && check.status === "rejected",
    ))).toBe(true);
    expect(graph.nodes.some((node) => node.metrics.some(
      (metric) => metric.id === "backlog" && metric.value === "1",
    ))).toBe(true);
    expect(artifact.provenance.guarantees).toContain(
      "selected actions exactly match the first scheduler tick",
    );
  });

  it("offers a full shift with resource tradeoffs and genuine output backpressure", () => {
    const graph = parseArtifact(fixture("foundry-control-room.v4.json")).commandGraph!;
    const terminalFuel = new Set(graph.nodes.filter((node) => !node.candidates.length).map((node) => node.metrics.find((metric) => metric.id === "fuel-delivered")!.value));
    expect(terminalFuel).toEqual(new Set(["0", "10", "20"]));
    const stack = [{ id: graph.root, depth: 0 }];
    const completedDepths: number[] = [];
    while (stack.length) {
      const current = stack.pop()!;
      const node = graph.nodes.find((item) => item.id === current.id)!;
      const outgoing = graph.resolutions.filter((edge) => edge.source === node.id);
      if (!outgoing.length && node.metrics.some((metric) => metric.id === "fuel-delivered" && metric.value === "20")) completedDepths.push(current.depth);
      for (const edge of outgoing) stack.push({ id: edge.target, depth: current.depth + 1 });
    }
    expect(Math.min(...completedDepths)).toBeGreaterThanOrEqual(8);
    expect(Math.max(...completedDepths)).toBeGreaterThan(Math.min(...completedDepths));
    expect(graph.nodes.some((node) => node.title === "Completion is blocked" && node.candidates.some((candidate) => candidate.status === "rejected"))).toBe(true);
    for (const node of graph.nodes.filter((node) => !node.candidates.length)) {
      expect(node.metrics.find((metric) => metric.id === "operator-location")?.value).toBe("0");
      expect(node.metrics.find((metric) => metric.id === "backlog")?.value).toBe("0");
      expect(node.metrics.find((metric) => metric.id === "active-work")?.value).toBe("0");
    }
  });

  it("exports actor-safe information sets, scoped messages, escrow, and sealed outcomes", () => {
    const artifact = parseArtifact(fixture("veiled-accord.v4.json"));
    const graph = artifact.commandGraph;
    expect(graph).not.toBeNull();
    if (!graph) return;

    expect(graph.actors.map((actor) => actor.label)).toEqual([
      "Coalition command", "Partner force", "Neutral authority",
    ]);
    expect(graph.informationSets).toHaveLength(1);
    expect(graph.informationSets[0]?.detail).toMatch(/same observation, candidates/);
    const hiddenNode = graph.nodes.find((node) => node.informationSet !== null);
    expect(hiddenNode?.candidates.every((candidate) => candidate.visibility !== "authoritative"))
      .toBe(true);
    expect(hiddenNode?.candidates.filter((candidate) => candidate.sealed)).toHaveLength(2);
    expect(graph.nodes.flatMap((node) => node.messages).some(
      (message) => message.statement === "Verified threat on Ridge route"
        && message.verification === "verified",
    )).toBe(true);
    expect(graph.nodes.some((node) => node.agreements.some(
      (agreement) => agreement.status === "escrow-funded"
        && agreement.escrow.some((item) => item.quantity === "2"),
    ))).toBe(true);
    expect(graph.resolutions.filter((resolution) => resolution.reveal !== null)).toHaveLength(6);
    const pareto = graph.nodes.find((node) => node.outcome === "pareto-accord");
    expect(pareto?.metrics.find((metric) => metric.id === "civilians-saved")?.value).toBe("24");
    expect(pareto?.metrics.find((metric) => metric.id === "credibility")?.value).toBe("100");
    expect(artifact.provenance.guarantees).toContain(
      "actor-visible command surfaces factor only through declared observations",
    );
  });

  it("enforces reusable structural invariants for every command-capable artifact", () => {
    const catalog = parseCatalog(fixture("catalog.v4.json"));
    const commandEntries = catalog.entries.filter((entry) => entry.capability !== "trace");
    expect(commandEntries.length).toBeGreaterThan(1);

    for (const entry of commandEntries) {
      const artifact = catalogArtifact(entry.artifact);
      const graph = artifact.commandGraph;
      expect(graph, entry.id).not.toBeNull();
      if (!graph) continue;

      expect(new Set(graph.nodes.map((node) => node.id)).size, entry.id).toBe(graph.nodes.length);
      expect(new Set(graph.resolutions.map((resolution) => resolution.id)).size, entry.id)
        .toBe(graph.resolutions.length);

      const nodeById = new Map(graph.nodes.map((node) => [node.id, node]));
      for (const node of graph.nodes) {
        const accepted = node.candidates.filter((candidate) => candidate.status === "accepted");
        const outgoing = graph.resolutions.filter((resolution) => resolution.source === node.id);
        expect(accepted.length === 0, `${entry.id}/${node.id} terminal`).toBe(outgoing.length === 0);
        for (const candidate of accepted) {
          expect(outgoing.some((resolution) => resolution.actionIds.includes(candidate.id)),
            `${entry.id}/${node.id}/${candidate.id} covered`).toBe(true);
        }
      }
      for (const resolution of graph.resolutions) {
        const source = nodeById.get(resolution.source);
        expect(source).toBeDefined();
        expect(nodeById.has(resolution.target)).toBe(true);
        expect(resolution.steps.length).toBeGreaterThan(0);
        expect(resolution.actionIds.every((actionId) => source?.candidates.some(
          (candidate) => candidate.id === actionId && candidate.status === "accepted",
        ))).toBe(true);
        expect([...resolution.steps[0]!.intentIds].sort()).toEqual(
          [...resolution.actionIds].sort(),
        );
      }

      const rejected = graph.nodes.flatMap((node) => node.candidates)
        .filter((candidate) => candidate.status === "rejected");
      expect(rejected.length).toBeGreaterThan(0);
      expect(rejected.every((candidate) =>
        candidate.effects.length === 0 && candidate.issues.length > 0
      )).toBe(true);
      expect(graph.resolutions.some((resolution) => resolution.actionIds.length > 1)).toBe(true);
    }
  });

  it("rejects exported command graphs that detach selections or accepted candidates", () => {
    const detachedTick = structuredClone(
      fixture("foundry-control-room.v4.json") as Record<string, unknown>,
    ) as { commandGraph: { resolutions: Array<{ steps: Array<{ intentIds: string[] }> }> } };
    detachedTick.commandGraph.resolutions[0]!.steps[0]!.intentIds = ["not-selected"];
    expect(() => parseArtifact(detachedTick)).toThrow(/first tick must exactly match/);

    const uncovered = fixture("foundry-control-room.v4.json") as ScenarioArtifact;
    const graph = uncovered.commandGraph!;
    const acceptedId = graph.nodes.find((node) => node.id === graph.root)!.candidates
      .find((candidate) => candidate.status === "accepted")!.id;
    graph.resolutions = graph.resolutions.filter((resolution) => !resolution.actionIds.includes(acceptedId));
    expect(() => parseArtifact(uncovered)).toThrow(new RegExp(`accepted candidate ${acceptedId} has no resolution`));
  });

  it("keeps queue footprints from distinct components disjoint in every generated state", () => {
    const catalog = parseCatalog(fixture("catalog.v4.json"));
    let comparisons = 0;

    for (const entry of catalog.entries) {
      const artifact = catalogArtifact(entry.artifact);
      const states = [artifact.initial, ...artifact.steps.map((step) => step.after)];
      for (const [stateIndex, state] of states.entries()) {
        const layout = crossComponentQueueLayout(artifact, state);
        comparisons += layout.comparisons;
        expect(layout.overlaps, `${artifact.id} state ${stateIndex}`).toEqual([]);
      }
    }

    expect(comparisons).toBeGreaterThan(0);
  });
});


describe("artifact trust boundary", () => {
  it.each([
    ["invalid quantity", (a: ScenarioArtifact) => { a.initial.holdings[0]!.quantity = "1e9"; }],
    ["missing provenance", (a: ScenarioArtifact) => { a.provenance = undefined as unknown as ScenarioArtifact["provenance"]; }],
    ["invalid metric", (a: ScenarioArtifact) => { a.commandGraph!.nodes[0]!.metrics[0]!.value = "NaN"; }],
    ["disconnected first state", (a: ScenarioArtifact) => { a.commandGraph!.resolutions[0]!.steps[0]!.before.holdings = []; }],
    ["disconnected target", (a: ScenarioArtifact) => { a.commandGraph!.resolutions[0]!.steps.at(-1)!.after.holdings = []; }],
    ["null machine", (a: ScenarioArtifact) => { a.initial.machines.push(null as unknown as StateView["machines"][number]); }],
    ["nonfinite camera", (a: ScenarioArtifact) => { a.presentation.camera.position.x = Infinity; }],
  ])("rejects %s before rendering", (_name, corrupt) => {
    const raw = fixture("veiled-accord.v4.json") as ScenarioArtifact;
    corrupt(raw);
    expect(() => parseArtifact(raw)).toThrow();
  });

  it("rejects mutations disguised as rejection", () => {
    const raw = fixture("foundry-active-presence.v4.json") as ScenarioArtifact;
    raw.steps.find((step) => step.status === "rejected")!.after.holdings = [];
    expect(() => parseArtifact(raw)).toThrow(/rejection/);
  });

  it("exports no speculative outcome effects in Veiled Accord candidates", () => {
    const raw = parseArtifact(fixture("veiled-accord.v4.json"));
    for (const node of raw.commandGraph!.nodes) {
      for (const candidate of node.candidates) {
        expect(candidate.effects).toEqual([]);
        expect(candidate.visibility).toBe("actor-safe");
      }
    }
  });
});
