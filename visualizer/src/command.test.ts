import { readFileSync } from "node:fs";
import { describe, expect, it } from "vitest";
import {
  advanceTrail,
  canonicalActionSet,
  compareMetrics,
  resolutionForSelection,
  rewindTrail,
} from "./command";
import { parseArtifact, type CommandGraphView } from "./protocol";

function generatedCommandGraph(): CommandGraphView {
  const url = new URL("../public/generated/nightglass-extraction.v3.json", import.meta.url);
  const graph = parseArtifact(JSON.parse(readFileSync(url, "utf8")) as unknown).commandGraph;
  if (!graph) throw new Error("The generated command showcase has no command graph");
  return graph;
}

describe("generic command graph navigation", () => {
  it("matches exact simultaneous action sets independent of selection order", () => {
    const graph = generatedCommandGraph();
    const multiAction = graph.resolutions.find((resolution) => resolution.actionIds.length > 1);
    expect(multiAction).toBeDefined();
    expect(resolutionForSelection(graph, multiAction!.source, [...multiAction!.actionIds].reverse())?.id)
      .toBe(multiAction!.id);
    expect(canonicalActionSet(multiAction!.actionIds)).toBe(
      canonicalActionSet([...multiAction!.actionIds].reverse()),
    );
  });

  it("does not silently resolve an unmodeled action combination", () => {
    const graph = generatedCommandGraph();
    const source = graph.nodes.find((node) =>
      node.candidates.filter((candidate) => candidate.status === "accepted").length > 1
    );
    expect(source).toBeDefined();
    const allAccepted = source!.candidates
      .filter((candidate) => candidate.status === "accepted")
      .map((candidate) => candidate.id);
    const modeled = new Set(graph.resolutions
      .filter((resolution) => resolution.source === source!.id)
      .map((resolution) => canonicalActionSet(resolution.actionIds)));
    const unmodeled = allAccepted.length > 1 && !modeled.has(canonicalActionSet(allAccepted));
    expect(unmodeled).toBe(true);
    expect(resolutionForSelection(graph, source!.id, allAccepted)).toBeUndefined();
  });

  it("advances and rewinds an immutable branch trail", () => {
    const graph = generatedCommandGraph();
    const first = graph.resolutions.find((resolution) => resolution.source === graph.root)!;
    const second = graph.resolutions.find((resolution) => resolution.source === first.target)!;
    const advanced = advanceTrail(
      advanceTrail([{ nodeId: graph.root, resolutionId: null }], first),
      second,
    );
    expect(advanced.map((entry) => entry.nodeId)).toEqual([graph.root, first.target, second.target]);
    expect(rewindTrail(advanced, 1)).toEqual([
      { nodeId: graph.root, resolutionId: first.id },
      { nodeId: first.target, resolutionId: null },
    ]);
  });

  it("compares exact-decimal metrics without floating-point loss", () => {
    const graph = generatedCommandGraph();
    const terminals = graph.nodes.filter((node) => node.candidates.length === 0);
    const pair = terminals.flatMap((left, index) =>
      terminals.slice(index + 1).map((right) => ({ left, right })))
      .find(({ left, right }) => compareMetrics(left, right).some((metric) => metric.delta !== "0"));
    expect(pair).toBeDefined();
    const comparison = compareMetrics(pair!.left, pair!.right);
    expect(comparison).toHaveLength(pair!.left.metrics.length);
    expect(comparison.some((metric) => metric.delta.startsWith("+") || metric.delta.startsWith("-")))
      .toBe(true);
  });
});
