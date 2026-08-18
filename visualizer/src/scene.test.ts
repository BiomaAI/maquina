import { describe, expect, it } from "vitest";
import type { ScenarioArtifact } from "./protocol";
import { projectScene } from "./scene";

const orchardArtifact: ScenarioArtifact = {
  schemaVersion: 1,
  id: "orchard-press",
  gameId: "orchard",
  title: "Orchard press",
  summary: "A deliberately non-Foundry fixture.",
  presentation: {
    theme: { background: "#001100", surface: "#112211", accent: "#eecc55" },
    resources: [
      { id: "resource:apple", label: "Apple", symbol: "A", color: "#cc3344", geometry: "sphere", unit: null },
    ],
    accounts: [
      { id: "account:farmer", label: "Farmer", kind: "participant", color: "#55aa44", position: { x: -5, y: 0, z: 0 } },
      { id: "account:press", label: "Press inventory", kind: "machine-inventory", color: "#777777", position: { x: 0, y: 0, z: 0 } },
    ],
    machines: [
      { id: "machine:press", label: "Apple press", color: "#889977", position: { x: 0, y: 0, z: 0 } },
    ],
    camera: { position: { x: 10, y: 10, z: 10 }, target: { x: 0, y: 0, z: 0 } },
  },
  provenance: { engine: "lean", toolchain: "test", guarantees: [] },
  initial: {
    holdings: [
      { account: "account:farmer", resource: "resource:apple", quantity: "90071992547409930000" },
    ],
    machines: [
      {
        id: "machine:press",
        inventory: "account:press",
        mode: "ready",
        maximumQueues: "8",
        queues: [
          { id: "machine:press:queue:input:0", stage: "input", capacity: "4", entries: [] },
        ],
      },
    ],
    custody: [],
    nextProcessId: "0",
  },
  steps: [],
};

describe("game-independent scene projection", () => {
  it("projects arbitrary resources, accounts, machines, and queues", () => {
    const scene = projectScene(orchardArtifact, orchardArtifact.initial);
    expect(scene.nodes.some((node) => node.id === "machine:press" && node.kind === "machine")).toBe(true);
    expect(scene.nodes.some((node) => node.id === "machine:press:queue:input:0" && node.kind === "queue")).toBe(true);
    expect(scene.nodes.some((node) => node.label === "Apple" && node.detail === "90071992547409930000")).toBe(true);
    expect(scene.nodes.some((node) => node.label.toLowerCase().includes("foundry"))).toBe(false);
  });

  it("derives motion from protocol effects rather than game identity", () => {
    const scene = projectScene(orchardArtifact, orchardArtifact.initial, [{
      kind: "transfer",
      stage: null,
      sourceQueue: null,
      destinationQueue: null,
      process: null,
      ticket: null,
      before: null,
      after: null,
      position: null,
      positions: [],
      account: null,
      remaining: null,
      disposition: null,
      observations: [],
      changes: [],
      movements: [{
        source: "account:farmer",
        destination: "account:press",
        resource: "resource:apple",
        quantity: "3",
        sourceBefore: "10",
        sourceAfter: "7",
        destinationBefore: "0",
        destinationAfter: "3",
      }],
    }]);
    expect(scene.motions).toEqual([
      expect.objectContaining({ source: "account:farmer", destination: "account:press", label: "3 Apple" }),
    ]);
  });
});
