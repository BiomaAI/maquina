import type {
  EffectView,
  PresentationView,
  ScenarioArtifact,
  StateView,
  Vec3,
} from "./protocol";

export type SceneNodeKind = "account" | "machine" | "queue" | "resource" | "process" | "custody";

export interface SceneNode {
  id: string;
  kind: SceneNodeKind;
  label: string;
  detail?: string;
  color: string;
  geometry?: string;
  position: Vec3;
  scale?: number;
  highlighted?: boolean;
}

export interface SceneLink {
  id: string;
  source: string;
  destination: string;
  color: string;
  active: boolean;
  dashed?: boolean;
}

export interface SceneMotion {
  id: string;
  source: string;
  destination: string;
  color: string;
  label: string;
}

export interface SceneDocument {
  background: string;
  camera: PresentationView["camera"];
  nodes: SceneNode[];
  links: SceneLink[];
  motions: SceneMotion[];
}

const STAGE_COLORS: Record<string, string> = {
  input: "#bd8443",
  processing: "#7e8a95",
  output: "#74a184",
};

function plus(position: Vec3, x: number, y: number, z: number): Vec3 {
  return { x: position.x + x, y: position.y + y, z: position.z + z };
}

function midpoint(left: Vec3, right: Vec3): Vec3 {
  return {
    x: (left.x + right.x) / 2,
    y: Math.max(left.y, right.y) + 1.2,
    z: (left.z + right.z) / 2,
  };
}

function queueOffset(stage: string, index: number): Vec3 {
  const x = stage === "input" ? -2.35 : stage === "output" ? 2.35 : 0;
  return { x, y: 1.05, z: (index - 0.5) * 1.7 };
}

function resourcePosition(base: Vec3, index: number): Vec3 {
  const column = index % 3;
  const row = Math.floor(index / 3);
  return plus(base, (column - 1) * 0.65, 1.05 + row * 0.58, 0.5);
}

function highlightedIds(effects: EffectView[]): Set<string> {
  const ids = new Set<string>();
  for (const effect of effects) {
    if (effect.account) ids.add(effect.account);
    if (effect.sourceQueue) ids.add(effect.sourceQueue);
    if (effect.destinationQueue) ids.add(effect.destinationQueue);
    if (effect.process) ids.add(effect.process);
    if (effect.position) ids.add(effect.position);
    for (const position of effect.positions) ids.add(position);
    for (const movement of effect.movements) {
      ids.add(movement.source);
      ids.add(movement.destination);
    }
    for (const observation of effect.observations) ids.add(observation.account);
    for (const change of effect.changes) ids.add(change.account);
  }
  return ids;
}

export function projectScene(
  artifact: Pick<ScenarioArtifact, "presentation">,
  state: StateView,
  effects: EffectView[] = [],
): SceneDocument {
  const presentation = artifact.presentation;
  const nodes: SceneNode[] = [];
  const links: SceneLink[] = [];
  const motions: SceneMotion[] = [];
  const positions = new Map<string, Vec3>();
  const highlights = highlightedIds(effects);
  const resources = new Map(presentation.resources.map((resource) => [resource.id, resource]));
  const accounts = new Map(presentation.accounts.map((account) => [account.id, account]));
  const machines = new Map(presentation.machines.map((machine) => [machine.id, machine]));

  for (const account of presentation.accounts) {
    positions.set(account.id, account.position);
    if (account.kind !== "machine-inventory") {
      nodes.push({
        id: account.id,
        kind: "account",
        label: account.label,
        detail: account.kind.replaceAll("-", " "),
        color: account.color,
        position: account.position,
        highlighted: highlights.has(account.id),
      });
    }
  }

  for (const machineState of state.machines) {
    const style = machines.get(machineState.id);
    const inventoryStyle = accounts.get(machineState.inventory);
    const base = style?.position ?? inventoryStyle?.position ?? { x: 0, y: 0, z: 0 };
    positions.set(machineState.id, base);
    positions.set(machineState.inventory, base);
    nodes.push({
      id: machineState.id,
      kind: "machine",
      label: style?.label ?? machineState.id,
      detail: `${machineState.mode} · ${machineState.queues.length}/${machineState.maximumQueues} queues`,
      color: style?.color ?? presentation.theme.accent,
      position: base,
      highlighted: highlights.has(machineState.id) || highlights.has(machineState.inventory),
    });

    const stageCounts = new Map<string, number>();
    for (const queue of machineState.queues) {
      const stageIndex = stageCounts.get(queue.stage) ?? 0;
      stageCounts.set(queue.stage, stageIndex + 1);
      const offset = queueOffset(queue.stage, stageIndex);
      const queuePosition = plus(base, offset.x, offset.y, offset.z);
      positions.set(queue.id, queuePosition);
      nodes.push({
        id: queue.id,
        kind: "queue",
        label: `${queue.stage} queue`,
        detail: `${queue.entries.length}/${queue.capacity ?? "∞"}`,
        color: STAGE_COLORS[queue.stage] ?? presentation.theme.accent,
        position: queuePosition,
        highlighted: highlights.has(queue.id),
      });
      links.push({
        id: `${machineState.id}:${queue.id}`,
        source: machineState.id,
        destination: queue.id,
        color: STAGE_COLORS[queue.stage] ?? presentation.theme.accent,
        active: queue.entries.length > 0,
      });
      for (const [entryIndex, process] of queue.entries.entries()) {
        const processPosition = plus(queuePosition, 0, 0.85, (entryIndex - 0.5) * 0.55);
        positions.set(process.id, processPosition);
        nodes.push({
          id: process.id,
          kind: "process",
          label: process.kind,
          detail: `work ${process.progress}/${process.requiredWork} · ticket ${process.ticket}`,
          color: STAGE_COLORS[queue.stage] ?? presentation.theme.accent,
          position: processPosition,
          scale: 0.72,
          highlighted: highlights.has(process.id),
        });
      }
    }
  }

  const holdingCounts = new Map<string, number>();
  for (const holding of state.holdings) {
    const base = positions.get(holding.account) ?? accounts.get(holding.account)?.position;
    if (!base) continue;
    const count = holdingCounts.get(holding.account) ?? 0;
    holdingCounts.set(holding.account, count + 1);
    const style = resources.get(holding.resource);
    nodes.push({
      id: `holding:${holding.account}:${holding.resource}`,
      kind: "resource",
      label: style?.label ?? holding.resource,
      detail: `${holding.quantity}${style?.unit ? ` ${style.unit}` : ""}`,
      color: style?.color ?? presentation.theme.accent,
      geometry: style?.geometry ?? "sphere",
      position: resourcePosition(base, count),
      scale: 0.75,
      highlighted: highlights.has(holding.account),
    });
  }

  for (const custody of state.custody) {
    const source = positions.get(custody.source);
    const destination = positions.get(custody.destination);
    if (!source || !destination) continue;
    const custodyPosition = midpoint(source, destination);
    positions.set(custody.id, custodyPosition);
    nodes.push({
      id: custody.id,
      kind: "custody",
      label: custody.active ? "active custody" : "open custody",
      detail: custody.contents
        .map((item) => `${item.quantity} ${resources.get(item.resource)?.label ?? item.resource}`)
        .join(" · "),
      color: custody.active ? "#c2a15c" : "#7e8a95",
      position: custodyPosition,
      highlighted: highlights.has(custody.id),
    });
    links.push({
      id: `${custody.id}:source`,
      source: custody.source,
      destination: custody.id,
      color: custody.active ? "#c2a15c" : "#7e8a95",
      active: custody.active,
      dashed: true,
    });
    links.push({
      id: `${custody.id}:destination`,
      source: custody.id,
      destination: custody.destination,
      color: custody.active ? "#c2a15c" : "#7e8a95",
      active: custody.active,
      dashed: true,
    });
  }

  let motionIndex = 0;
  for (const effect of effects) {
    for (const movement of effect.movements) {
      const style = resources.get(movement.resource);
      motions.push({
        id: `movement:${motionIndex++}`,
        source: movement.source,
        destination: movement.destination,
        color: style?.color ?? presentation.theme.accent,
        label: `${movement.quantity} ${style?.label ?? movement.resource}`,
      });
    }
    if (effect.sourceQueue && effect.destinationQueue) {
      motions.push({
        id: `queue-motion:${motionIndex++}`,
        source: effect.sourceQueue,
        destination: effect.destinationQueue,
        color: presentation.theme.accent,
        label: effect.kind.replaceAll("-", " "),
      });
    }
  }

  return {
    background: presentation.theme.background,
    camera: presentation.camera,
    nodes,
    links: links.filter((link) => positions.has(link.source) && positions.has(link.destination)),
    motions: motions.filter((motion) => positions.has(motion.source) && positions.has(motion.destination)),
  };
}
