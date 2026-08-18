import * as THREE from "three";
import { describe, expect, it } from "vitest";
import type { SceneNode, SceneNodeKind } from "./scene";
import { createSemanticShape } from "./three-shapes";

function node(kind: SceneNodeKind, overrides: Partial<SceneNode> = {}): SceneNode {
  return {
    id: `${kind}:test`,
    kind,
    label: `Test ${kind}`,
    color: "#c2a15c",
    position: { x: 0, y: 0, z: 0 },
    ...overrides,
  };
}

function meshNames(shape: THREE.Object3D): string[] {
  const names: string[] = [];
  shape.traverse((part) => {
    if (part instanceof THREE.Mesh) names.push(part.name);
  });
  return names;
}

describe("semantic Three.js shape vocabulary", () => {
  it.each([
    ["account", 5],
    ["machine", 13],
    ["queue", 9],
    ["process", 5],
    ["custody", 5],
    ["resource", 3],
  ] as const)("builds %s from multiple meaningful primitive parts", (kind, minimumParts) => {
    const names = meshNames(createSemanticShape(node(kind)).root);
    expect(names.length).toBeGreaterThanOrEqual(minimumParts);
    expect(new Set(names).size).toBeGreaterThan(1);
  });

  it.each(["account", "machine", "queue", "process", "custody", "resource"] as const)(
    "places the %s label above its semantic shape with room for a stem",
    (kind) => {
      const shape = createSemanticShape(node(kind));
      expect(shape.labelHeight).toBeGreaterThan(shape.stemStartY);
      expect(shape.labelHeight - shape.stemStartY).toBeGreaterThan(0.4);
    },
  );

  it("distinguishes participant accounts from custody vaults", () => {
    const participant = meshNames(createSemanticShape(node("account", { detail: "participant" })).root);
    const custody = meshNames(createSemanticShape(node("account", { detail: "custody" })).root);
    expect(participant).toContain("participant-head");
    expect(participant).not.toContain("custody-vault");
    expect(custody).toContain("custody-vault");
    expect(custody).toContain("custody-vault-door");
  });

  it.each([
    ["cube", "resource-crate"],
    ["cylinder", "resource-barrel"],
    ["octahedron", "resource-crystal"],
    ["sphere", "resource-token-head"],
  ])("gives %s resources a recognizable composed form", (geometry, semanticPart) => {
    const names = meshNames(createSemanticShape(node("resource", { geometry })).root);
    expect(names).toContain(semanticPart);
  });
});
