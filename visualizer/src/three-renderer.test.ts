import { describe, expect, it, vi } from "vitest";
import * as THREE from "three";
import { ThreeSceneRenderer } from "./three-renderer";
import type { SceneDocument, SceneNode } from "./scene";

// Exercise reconciliation and interpolation without requiring a WebGL context.
// Only the GPU/DOM shell is replaced; these are the renderer's real update methods.
function fixture(reduced: boolean) {
  const node: SceneNode = {
    id: "convoy", kind: "machine", label: "Convoy", color: "#ffffff",
    position: { x: -8, y: 0, z: 7 },
  };
  const root = new THREE.Group();
  root.position.set(-8, 0, 7);
  const visual = {
    node, root, label: { style: {}, classList: { toggle: vi.fn() } },
    selectionHalo: new THREE.Group(), baseScale: 1, opacity: 1,
    targetOpacity: 1, revealAt: 0, removing: false,
  };
  const document = { nodes: [node], anchors: [], links: [], motions: [], background: "#000000" } as unknown as SceneDocument;
  // Private state is inspected here to catch object destruction and pose discontinuities.
  const renderer = Object.create(ThreeSceneRenderer.prototype) as any;
  Object.assign(renderer, {
    currentDocument: document, animationTime: 0, reducedMotion: reduced,
    nodeVisuals: new Map([[node.id, visual]]), linkVisuals: new Map(),
    highlighted: new Set(), mechanisms: [], transferFlights: [], selectable: [],
    scene: new THREE.Scene(), content: new THREE.Group(),
    clearContent: vi.fn(), resize: vi.fn(),
  });
  return { renderer, root, visual, document };
}

describe("renderer animation continuity", () => {
  it.each([false, true])("retains objects and interpolates positions with reduced motion = %s", (reduced) => {
    const { renderer, root, document } = fixture(reduced);
    renderer.update({ ...document, nodes: [{ ...document.nodes[0], position: { x: -2, y: 0, z: 7 } }] });
    expect(renderer.clearContent).not.toHaveBeenCalled();
    expect(renderer.nodeVisuals.get("convoy").root).toBe(root);
    expect(root.position.x).toBe(-8);
    renderer.animateNodes(305, 0.016);
    expect(root.position.x).toBeCloseTo(-7.625);
    renderer.animateNodes(550, 0.016);
    expect(root.position.x).toBeCloseTo(-5);
    renderer.animateNodes(1040, 0.016);
    expect(root.position.x).toBe(-2);
  });

  it("retargets an interrupted transition from the visible position", () => {
    const { renderer, root, document } = fixture(false);
    renderer.update({ ...document, nodes: [{ ...document.nodes[0], position: { x: -2, y: 0, z: 7 } }] });
    renderer.animateNodes(550, 0.016);
    const visibleX = root.position.x;
    renderer.animationTime = 550;
    renderer.update(document);
    expect(root.position.x).toBe(visibleX);
    renderer.animateNodes(610, 0.016);
    expect(root.position.x).toBe(visibleX);
    renderer.animateNodes(1100, 0.016);
    expect(root.position.x).toBeCloseTo((visibleX - 8) / 2);
  });

  it("changes mechanism speed without jumping its angle", () => {
    const { renderer, visual, root } = fixture(false);
    const radar = new THREE.Group();
    radar.name = "radar-azimuth";
    radar.rotation.y = 0.4;
    root.add(radar);
    visual.node.activity = "scanning";
    renderer.syncMechanisms(visual);
    renderer.animateMechanisms(10);
    const scanningAngle = radar.rotation.y;
    visual.node.activity = "tracking";
    renderer.syncMechanisms(visual);
    expect(radar.rotation.y).toBe(scanningAngle);
    renderer.animateMechanisms(0.1);
    expect(radar.rotation.y).toBeCloseTo(scanningAngle + 0.022);
  });
});
