import * as THREE from "three";
import { describe, expect, it } from "vitest";
import type { SceneNode, SceneNodeKind } from "./scene";
import { createSelectionHalo, createSemanticShape } from "./three-shapes";

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

  it.each([
    ["radar", ["radar-dish", "radar-feed", "radar-track-beacon"]],
    ["battery", ["battery-turret-ring", "battery-launch-tube", "battery-warning"]],
    ["convoy", ["convoy-cab", "convoy-wheel-tire", "convoy-beacon", "convoy-damage-spark", "convoy-extraction-ring"]],
  ])("builds the %s machine variant from domain-neutral geometry metadata", (geometry, semanticParts) => {
    const names = meshNames(createSemanticShape(node("machine", { geometry })).root);
    for (const semanticPart of semanticParts) expect(names).toContain(semanticPart);
    expect(names).not.toContain("machine-work-core");
  });

  it("keeps every convoy wheel centered while it rotates around its axle", () => {
    const shape = createSemanticShape(node("machine", { geometry: "convoy" })).root;
    const wheels = shape.children.filter((part) => part.name.startsWith("convoy-wheel-"));

    expect(wheels).toHaveLength(4);
    for (const wheel of wheels) {
      expect(wheel).toBeInstanceOf(THREE.Group);
      expect(wheel.children.map((part) => part.name)).toEqual([
        "convoy-wheel-tire",
        "convoy-wheel-hub",
      ]);

      const center = wheel.position.clone();
      const axleBefore = new THREE.Vector3(0, 0, 1).applyQuaternion(wheel.quaternion);
      wheel.rotateZ(Math.PI / 3);
      const axleAfter = new THREE.Vector3(0, 0, 1).applyQuaternion(wheel.quaternion);

      expect(wheel.position.distanceTo(center)).toBe(0);
      expect(axleAfter.distanceTo(axleBefore)).toBeLessThan(1e-12);
    }
  });

  it.each([
    ["account", {}],
    ["machine", {}],
    ["machine", { geometry: "radar" }],
    ["machine", { geometry: "battery" }],
    ["machine", { geometry: "convoy" }],
    ["queue", {}],
    ["process", {}],
    ["custody", {}],
    ["resource", {}],
  ] as const)("sizes a persistent selection halo for every %s shape", (kind, overrides) => {
    const semanticShape = createSemanticShape(node(kind, overrides));
    const halo = createSelectionHalo(semanticShape, "#57d6ff");
    const primary = halo.getObjectByName("selection-halo-primary");
    const outer = halo.getObjectByName("selection-halo-outer");

    expect(halo.visible).toBe(false);
    expect(halo.position.y).toBe(semanticShape.highlightY);
    expect(primary).toBeInstanceOf(THREE.Mesh);
    expect(outer).toBeInstanceOf(THREE.Mesh);
    expect((primary as THREE.Mesh<THREE.TorusGeometry>).geometry.parameters.radius)
      .toBe(semanticShape.highlightRadius);
    expect((outer as THREE.Mesh<THREE.TorusGeometry>).geometry.parameters.radius)
      .toBe(semanticShape.highlightRadius + 0.16);
  });
});
