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
  it("publishes a versioned catalog with multiple scenarios", () => {
    const catalog = parseCatalog(fixture("catalog.v3.json"));
    expect(catalog.schemaVersion).toBe(3);
    expect(catalog.entries.map((entry) => entry.id)).toEqual([
      "foundry-refuel-lifecycle",
      "foundry-active-presence",
      "foundry-operating-guards",
      "foundry-workcell-body-contention",
      "nightglass-extraction",
    ]);
  });

  it("retains exact decimal quantities and replay provenance", () => {
    const artifact = parseArtifact(fixture("foundry-refuel-lifecycle.v3.json"));
    expect(typeof artifact.initial.nextProcessId).toBe("string");
    expect(artifact.steps).toHaveLength(7);
    expect(artifact.steps.every((step) => step.semanticStatus.startsWith("lean-"))).toBe(true);
    expect(artifact.steps.flatMap((step) => step.checks).some((check) => check.condition === "possession")).toBe(true);
    expect(artifact.steps.flatMap((step) => step.effects).some((effect) => effect.kind === "transfer")).toBe(true);
  });

  it("treats the additive command graph field as absent for older v3 producers", () => {
    const raw = fixture("foundry-refuel-lifecycle.v3.json") as Record<string, unknown>;
    const { commandGraph: _commandGraph, ...withoutCommandGraph } = raw;
    expect(parseArtifact(withoutCommandGraph).commandGraph).toBeNull();
  });

  it("represents rejections as unchanged states with no effects", () => {
    const artifact = parseArtifact(fixture("foundry-active-presence.v3.json"));
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
    const artifact = parseArtifact(fixture("foundry-operating-guards.v3.json"));
    const checks = artifact.steps.flatMap((step) => step.checks);
    expect(checks.some((check) => check.condition === "processing-idle" && check.status === "accepted")).toBe(true);
    expect(checks.some((check) => check.condition === "processing-active" && check.status === "accepted")).toBe(true);
    expect(checks.some((check) => check.issues.some((issue) => issue.code === "active-work-present"))).toBe(true);
    expect(checks.some((check) => check.issues.some((issue) => issue.code === "active-work-missing"))).toBe(true);
  });

  it("projects a game-owned workcell over one authoritative account state", () => {
    const artifact = parseArtifact(fixture("foundry-workcell-body-contention.v3.json"));
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
    const artifact = parseArtifact(fixture("nightglass-extraction.v3.json"));
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

  it("exports a closed proof-backed command graph with reusable structural invariants", () => {
    const artifact = parseArtifact(fixture("nightglass-extraction.v3.json"));
    const graph = artifact.commandGraph;
    expect(graph).not.toBeNull();
    if (!graph) return;

    expect(graph.nodes).toHaveLength(11);
    expect(graph.resolutions).toHaveLength(10);
    expect(new Set(graph.nodes.map((node) => node.id)).size).toBe(graph.nodes.length);
    expect(new Set(graph.resolutions.map((resolution) => resolution.id)).size)
      .toBe(graph.resolutions.length);

    const nodeById = new Map(graph.nodes.map((node) => [node.id, node]));
    for (const resolution of graph.resolutions) {
      const source = nodeById.get(resolution.source);
      expect(source).toBeDefined();
      expect(nodeById.has(resolution.target)).toBe(true);
      expect(resolution.steps.length).toBeGreaterThan(0);
      expect(resolution.actionIds.every((actionId) => source?.candidates.some(
        (candidate) => candidate.id === actionId && candidate.status === "accepted",
      ))).toBe(true);
    }

    const rejected = graph.nodes.flatMap((node) => node.candidates)
      .filter((candidate) => candidate.status === "rejected");
    expect(rejected.length).toBeGreaterThan(0);
    expect(rejected.every((candidate) =>
      candidate.effects.length === 0 && candidate.issues.length > 0
    )).toBe(true);
    expect(graph.resolutions.some((resolution) => resolution.actionIds.length > 1)).toBe(true);
    expect(new Set(graph.nodes.map((node) => node.stateKey)).size).toBeLessThan(graph.nodes.length);
    expect(new Set(graph.nodes.filter((node) => node.candidates.length === 0)
      .map((node) => node.outcome))).toEqual(new Set([
      "clean-victory", "costly-victory", "exposed-extraction", "defeat",
    ]));
  });

  it("keeps queue footprints from distinct components disjoint in every generated state", () => {
    const catalog = parseCatalog(fixture("catalog.v3.json"));
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
