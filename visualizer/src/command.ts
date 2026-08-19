import type {
  CommandGraphView,
  CommandNodeView,
  CommandResolutionView,
} from "./protocol";

export interface CommandTrailEntry {
  nodeId: string;
  resolutionId: string | null;
}

export interface MetricComparison {
  id: string;
  label: string;
  unit: string | null;
  baseline: string;
  alternative: string;
  delta: string;
}

export function canonicalActionSet(actionIds: Iterable<string>): string {
  return [...actionIds].sort().join("\u0000");
}

export function commandNode(
  graph: CommandGraphView,
  nodeId: string,
): CommandNodeView | undefined {
  return graph.nodes.find((node) => node.id === nodeId);
}

export function outgoingResolutions(
  graph: CommandGraphView,
  source: string,
): CommandResolutionView[] {
  return graph.resolutions.filter((resolution) => resolution.source === source);
}

export function resolutionForSelection(
  graph: CommandGraphView,
  source: string,
  selectedActionIds: Iterable<string>,
): CommandResolutionView | undefined {
  const selected = canonicalActionSet(selectedActionIds);
  return outgoingResolutions(graph, source).find(
    (resolution) => canonicalActionSet(resolution.actionIds) === selected,
  );
}

export function advanceTrail(
  trail: CommandTrailEntry[],
  resolution: CommandResolutionView,
): CommandTrailEntry[] {
  const current = trail.at(-1);
  if (current?.nodeId !== resolution.source) {
    throw new Error("Resolution source must match the current command snapshot");
  }
  return [
    ...trail.slice(0, -1),
    { ...current, resolutionId: resolution.id },
    { nodeId: resolution.target, resolutionId: null },
  ];
}

export function rewindTrail(
  trail: CommandTrailEntry[],
  index: number,
): CommandTrailEntry[] {
  if (!Number.isInteger(index) || index < 0 || index >= trail.length) {
    throw new Error("Command trail index is out of range");
  }
  return [...trail.slice(0, index), { nodeId: trail[index]!.nodeId, resolutionId: null }];
}

export function compareMetrics(
  baseline: CommandNodeView,
  alternative: CommandNodeView,
): MetricComparison[] {
  const alternativeById = new Map(alternative.metrics.map((metric) => [metric.id, metric]));
  return baseline.metrics.flatMap((metric) => {
    const other = alternativeById.get(metric.id);
    if (!other) return [];
    const delta = BigInt(other.value) - BigInt(metric.value);
    return [{
      id: metric.id,
      label: metric.label,
      unit: metric.unit,
      baseline: metric.value,
      alternative: other.value,
      delta: delta > 0n ? `+${delta}` : String(delta),
    }];
  });
}
