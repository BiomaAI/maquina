import { readFileSync } from "node:fs";
import { describe, expect, it } from "vitest";
import {
  advanceTrail,
  canonicalActionSet,
  compareMetrics,
  orderPlanCopy,
  isTerminalNode,
  resolutionForSelection,
  rewindTrail,
} from "./command";
import { parseArtifact, parseCatalog, type CommandGraphView } from "./protocol";

function generatedCommandGraphs(): Array<{ id: string; graph: CommandGraphView }> {
  const catalogUrl = new URL("../public/generated/catalog.v4.json", import.meta.url);
  const catalog = parseCatalog(JSON.parse(readFileSync(catalogUrl, "utf8")) as unknown);
  return catalog.entries.filter((entry) => entry.capability !== "trace").map((entry) => {
    const url = new URL(`../public/${entry.artifact}`, import.meta.url);
    const graph = parseArtifact(JSON.parse(readFileSync(url, "utf8")) as unknown).commandGraph;
    if (!graph) throw new Error(`${entry.id} is labeled command-capable without a command graph`);
    return { id: entry.id, graph };
  });
}

describe("generic command graph navigation", () => {
  it("matches exact simultaneous action sets independent of selection order", () => {
    for (const { id, graph } of generatedCommandGraphs()) {
      const multiAction = graph.resolutions.find((resolution) => resolution.actionIds.length > 1);
      expect(multiAction, id).toBeDefined();
      expect(resolutionForSelection(graph, multiAction!.source, [...multiAction!.actionIds].reverse())?.id)
        .toBe(multiAction!.id);
      expect(canonicalActionSet(multiAction!.actionIds)).toBe(
        canonicalActionSet([...multiAction!.actionIds].reverse()),
      );
    }
  });

  it("does not silently resolve an unmodeled action combination", () => {
    for (const { id, graph } of generatedCommandGraphs()) {
      const source = graph.nodes.find((node) => {
        const allAccepted = node.candidates
          .filter((candidate) => candidate.status === "accepted")
          .map((candidate) => candidate.id);
        const modeled = new Set(graph.resolutions
          .filter((resolution) => resolution.source === node.id)
          .map((resolution) => canonicalActionSet(resolution.actionIds)));
        return allAccepted.length > 1 && !modeled.has(canonicalActionSet(allAccepted));
      });
      expect(source, id).toBeDefined();
      const allAccepted = source!.candidates
        .filter((candidate) => candidate.status === "accepted")
        .map((candidate) => candidate.id);
      expect(resolutionForSelection(graph, source!.id, allAccepted)).toBeUndefined();
    }
  });

  it("advances and rewinds an immutable branch trail", () => {
    for (const { graph } of generatedCommandGraphs()) {
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
    }
  });

  it("compares exact-decimal metrics without floating-point loss", () => {
    for (const { id, graph } of generatedCommandGraphs()) {
      const terminals = graph.nodes.filter((node) => node.candidates.length === 0);
      const pair = terminals.flatMap((left, index) =>
        terminals.slice(index + 1).map((right) => ({ left, right })))
        .find(({ left, right }) => compareMetrics(left, right).some((metric) => metric.delta !== "0"));
      expect(pair, id).toBeDefined();
      const comparison = compareMetrics(pair!.left, pair!.right);
      expect(comparison).toHaveLength(pair!.left.metrics.length);
      expect(comparison.some((metric) => metric.delta.startsWith("+") || metric.delta.startsWith("-")))
        .toBe(true);
    }
  });
});


describe("player-facing plans", () => {
  it("does not disclose a sealed outcome in plan labels or previews", () => {
    const graph = generatedCommandGraphs().find((item) => item.id === "veiled-accord")!.graph;
    const sealedPlans = graph.resolutions.filter((plan) => plan.reveal !== null);
    expect(sealedPlans.length).toBeGreaterThan(0);
    for (const plan of sealedPlans) {
      const poisoned = { ...plan, label: "SECRET PARTNER ORDER", summary: "SECRET OUTCOME", reveal: "SECRET REVEAL" };
      const copy = orderPlanCopy(graph, poisoned);
      expect(copy.sealed).toBe(true);
      expect(JSON.stringify(copy)).not.toContain("SECRET");
    }
  });

  it("recognizes a terminal that still exposes rejected candidates", () => {
    const graph = generatedCommandGraphs()[0]!.graph;
    const terminal = graph.nodes.find((node) => node.candidates.length === 0)!;
    const rejected = graph.nodes.flatMap((node) => node.candidates).find((candidate) => candidate.status === "rejected")!;
    expect(isTerminalNode(graph, { ...terminal, candidates: [rejected] })).toBe(true);
  });
});
