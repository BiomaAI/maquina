import * as THREE from "three";
import { OrbitControls } from "three/addons/controls/OrbitControls.js";
import { CSS2DObject } from "three/addons/renderers/CSS2DRenderer.js";
import { CSS2DRenderer } from "three/addons/renderers/CSS2DRenderer.js";
import type { SceneDocument, SceneNode } from "./scene";
import { createLedgerMaterial, createSemanticShape } from "./three-shapes";

interface CurveParticle {
  particle: THREE.Mesh;
  curve: THREE.QuadraticBezierCurve3;
  phase: number;
  speed: number;
  pulse: number;
}

interface FlowLine {
  baseDistances: Float32Array;
  distances: THREE.BufferAttribute;
  phase: number;
  unitsPerSecond: number;
}

interface EffectMote {
  particle: THREE.Mesh;
  baseY: number;
  phase: number;
  radius: number;
  rise: number;
  speed: number;
}

interface OrbitParticle {
  particle: THREE.Mesh;
  baseY: number;
  phase: number;
  radius: number;
  speed: number;
}

interface AnimatedRoot {
  root: THREE.Group;
  baseY: number;
  baseScale: number;
  phase: number;
  bob: number;
  speed: number;
  sway: number;
  highlighted: boolean;
}

interface PulseRing {
  ring: THREE.Mesh;
  phase: number;
  speed: number;
}

function vector(value: { x: number; y: number; z: number }): THREE.Vector3 {
  return new THREE.Vector3(value.x, value.y, value.z);
}

function samePosition(left: SceneNode, right: { x: number; y: number; z: number }): boolean {
  return left.position.x === right.x && left.position.y === right.y && left.position.z === right.z;
}

function anchorLift(node?: SceneNode): number {
  switch (node?.kind) {
    case "machine": return 1.45;
    case "queue": return 0.35;
    case "account": return 0.45;
    case "resource": return 0.2;
    default: return 0;
  }
}

function labelLift(node: SceneNode): number {
  switch (node.kind) {
    case "machine": return 66;
    case "account": return 52;
    case "queue": return 46;
    case "custody": return 42;
    case "process": return 38;
    case "resource": return 32;
  }
}

function motionProfile(node: SceneNode): { bob: number; speed: number; sway: number } {
  switch (node.kind) {
    case "machine": return { bob: 0.055, speed: 0.2, sway: 0.01 };
    case "account": return { bob: 0.1, speed: 0.32, sway: 0.035 };
    case "queue": return { bob: 0.07, speed: 0.26, sway: 0.022 };
    case "custody": return { bob: 0.12, speed: 0.34, sway: 0.045 };
    case "process": return { bob: 0.17, speed: 0.45, sway: 0.085 };
    case "resource": return { bob: 0.2, speed: 0.52, sway: 0.1 };
  }
}

function connectionCurve(source: THREE.Vector3, destination: THREE.Vector3, emphasis = 1): THREE.QuadraticBezierCurve3 {
  const apex = source.clone().lerp(destination, 0.5);
  const horizontalDistance = Math.hypot(source.x - destination.x, source.z - destination.z);
  apex.y = Math.max(source.y, destination.y) + Math.min(1.6, (0.34 + horizontalDistance * 0.055) * emphasis);
  return new THREE.QuadraticBezierCurve3(source, apex, destination);
}

function disposeObject(object: THREE.Object3D): void {
  object.traverse((child) => {
    if (child instanceof THREE.Mesh || child instanceof THREE.Line) {
      child.geometry.dispose();
      const materials = Array.isArray(child.material) ? child.material : [child.material];
      for (const item of materials) item.dispose();
    }
    if (child instanceof CSS2DObject) child.element.remove();
  });
}

export class ThreeSceneRenderer {
  private readonly scene = new THREE.Scene();
  private readonly camera = new THREE.PerspectiveCamera(42, 1, 0.1, 120);
  private readonly renderer = new THREE.WebGLRenderer({ antialias: true, alpha: false });
  private readonly labels = new CSS2DRenderer();
  private readonly controls: OrbitControls;
  private readonly content = new THREE.Group();
  private readonly raycaster = new THREE.Raycaster();
  private readonly pointer = new THREE.Vector2();
  private readonly selectable: THREE.Object3D[] = [];
  private readonly curveParticles: CurveParticle[] = [];
  private readonly flowLines: FlowLine[] = [];
  private readonly effectMotes: EffectMote[] = [];
  private readonly orbitParticles: OrbitParticle[] = [];
  private readonly animatedRoots: AnimatedRoot[] = [];
  private readonly pulseRings: PulseRing[] = [];
  private readonly resizeObserver: ResizeObserver;
  private currentDocument?: SceneDocument;
  private animationFrame = 0;

  constructor(
    private readonly container: HTMLElement,
    private readonly onSelect?: (id: string) => void,
  ) {
    this.renderer.setPixelRatio(Math.min(window.devicePixelRatio, 2));
    this.renderer.shadowMap.enabled = true;
    this.renderer.shadowMap.type = THREE.PCFSoftShadowMap;
    this.renderer.outputColorSpace = THREE.SRGBColorSpace;
    this.renderer.toneMapping = THREE.ACESFilmicToneMapping;
    this.renderer.toneMappingExposure = 0.96;
    this.renderer.domElement.className = "world-canvas";
    this.labels.domElement.className = "world-labels";
    this.container.append(this.renderer.domElement, this.labels.domElement);

    this.controls = new OrbitControls(this.camera, this.labels.domElement);
    this.controls.enableDamping = true;
    this.controls.dampingFactor = 0.075;
    this.controls.minDistance = 8;
    this.controls.maxDistance = 48;
    this.controls.maxPolarAngle = Math.PI * 0.47;

    this.scene.add(this.content);
    this.addEnvironment();
    this.resizeObserver = new ResizeObserver(() => this.resize());
    this.resizeObserver.observe(this.container);
    this.labels.domElement.addEventListener("pointerdown", (event) => this.pick(event));
    this.animate();
  }

  private addEnvironment(): void {
    const hemisphere = new THREE.HemisphereLight(0xeae6dc, 0x161618, 2.2);
    const key = new THREE.DirectionalLight(0xfff2db, 3.1);
    key.position.set(8, 15, 10);
    key.castShadow = true;
    key.shadow.mapSize.set(2048, 2048);
    key.shadow.camera.left = -20;
    key.shadow.camera.right = 20;
    key.shadow.camera.top = 20;
    key.shadow.camera.bottom = -20;
    this.scene.add(hemisphere, key);

    const floorMaterial = new THREE.MeshStandardMaterial({ color: 0x151517, roughness: 0.96 });
    const floor = new THREE.Mesh(new THREE.PlaneGeometry(42, 30), floorMaterial);
    floor.rotation.x = -Math.PI / 2;
    floor.position.y = -0.22;
    floor.receiveShadow = true;
    this.scene.add(floor);

    const grid = new THREE.GridHelper(42, 42, 0x3e3c38, 0x252527);
    grid.position.y = -0.205;
    const gridMaterials = Array.isArray(grid.material) ? grid.material : [grid.material];
    for (const item of gridMaterials) {
      item.transparent = true;
      item.opacity = 0.42;
    }
    this.scene.add(grid);
  }

  update(document: SceneDocument, resetCamera = false): void {
    this.currentDocument = document;
    this.scene.background = new THREE.Color(document.background);
    for (const child of [...this.content.children]) {
      this.content.remove(child);
      disposeObject(child);
    }
    this.selectable.length = 0;
    this.curveParticles.length = 0;
    this.flowLines.length = 0;
    this.effectMotes.length = 0;
    this.orbitParticles.length = 0;
    this.animatedRoots.length = 0;
    this.pulseRings.length = 0;

    const nodesById = new Map(document.nodes.map((node) => [node.id, node]));
    const positions = new Map(document.anchors.map((anchor) => {
      const semanticNode = nodesById.get(anchor.id)
        ?? document.nodes.find((node) => samePosition(node, anchor.position) && node.kind === "machine")
        ?? document.nodes.find((node) => samePosition(node, anchor.position));
      const position = vector(anchor.position);
      position.y += anchorLift(semanticNode);
      return [anchor.id, position] as const;
    }));
    for (const node of document.nodes) {
      if (positions.has(node.id)) continue;
      const position = vector(node.position);
      position.y += anchorLift(node);
      positions.set(node.id, position);
    }

    for (const [index, link] of document.links.entries()) {
      const source = positions.get(link.source);
      const destination = positions.get(link.destination);
      if (!source || !destination) continue;
      const curve = connectionCurve(source, destination, link.active ? 1.15 : 1);
      const lineGeometry = new THREE.BufferGeometry().setFromPoints(curve.getPoints(32));
      const lineMaterial = new THREE.LineDashedMaterial({
        color: link.color,
        transparent: true,
        opacity: link.active ? 0.94 : link.dashed ? 0.4 : 0.3,
        dashSize: link.active ? 0.4 : 0.18,
        gapSize: link.active ? 0.14 : 0.22,
      });
      const line = new THREE.Line(lineGeometry, lineMaterial);
      line.name = link.active ? "active-route" : "ambient-route";
      line.computeLineDistances();
      this.content.add(line);
      const distances = line.geometry.getAttribute("lineDistance") as THREE.BufferAttribute;
      this.flowLines.push({
        baseDistances: new Float32Array(distances.array),
        distances,
        phase: -index * 0.18,
        unitsPerSecond: link.active ? 1.0 : 0.28,
      });
      const particleCount = link.active ? 6 : 2;
      for (let particleIndex = 0; particleIndex < particleCount; particleIndex += 1) {
        const particle = new THREE.Mesh(
          new THREE.SphereGeometry(link.active ? 0.08 : 0.045, 10, 8),
          new THREE.MeshBasicMaterial({
            color: link.color,
            transparent: true,
            opacity: link.active ? 0.86 : 0.34,
            depthWrite: false,
          }),
        );
        particle.name = link.active ? "active-route-particle" : "ambient-route-particle";
        this.content.add(particle);
        this.curveParticles.push({
          particle,
          curve,
          phase: particleIndex / particleCount + index * 0.09,
          speed: link.active ? 0.3 : 0.1,
          pulse: link.active ? 0.24 : 0.1,
        });
      }
    }

    for (const node of document.nodes) this.addNode(node);
    for (const [index, motion] of document.motions.entries()) {
      const source = positions.get(motion.source);
      const destination = positions.get(motion.destination);
      if (!source || !destination) continue;
      const curve = connectionCurve(source, destination, 1.5);
      const pathMaterial = new THREE.LineDashedMaterial({
        color: motion.color,
        transparent: true,
        opacity: 0.48,
        dashSize: 0.28,
        gapSize: 0.16,
      });
      const path = new THREE.Line(new THREE.BufferGeometry().setFromPoints(curve.getPoints(36)), pathMaterial);
      path.name = "effect-route";
      path.computeLineDistances();
      const distances = path.geometry.getAttribute("lineDistance") as THREE.BufferAttribute;
      this.flowLines.push({
        baseDistances: new Float32Array(distances.array),
        distances,
        phase: -index * 0.22,
        unitsPerSecond: 1.05,
      });
      for (let particleIndex = 0; particleIndex < 7; particleIndex += 1) {
        const particle = new THREE.Mesh(
          new THREE.SphereGeometry(particleIndex === 0 ? 0.17 : 0.105, 14, 10),
          createLedgerMaterial(motion.color, particleIndex === 0 ? 1 : 0.78),
        );
        particle.name = particleIndex === 0 ? "effect-particle-leading" : "effect-particle-trailing";
        particle.castShadow = particleIndex === 0;
        particle.userData.motionLabel = motion.label;
        this.content.add(particle);
        this.curveParticles.push({
          particle,
          curve,
          phase: particleIndex / 7 + index * 0.11,
          speed: 0.64,
          pulse: particleIndex === 0 ? 0.42 : 0.2,
        });
      }
    }

    if (resetCamera) {
      this.camera.position.copy(vector(document.camera.position));
      this.controls.target.copy(vector(document.camera.target));
      this.controls.update();
    }
    this.resize();
  }

  private addNode(node: SceneNode): void {
    const shape = createSemanticShape(node);
    const root = shape.root;
    root.position.copy(vector(node.position));
    root.scale.setScalar(node.scale ?? 1);
    root.userData.sceneId = node.id;
    root.userData.baseScale = node.scale ?? 1;
    root.userData.highlighted = node.highlighted ?? false;
    root.userData.phase = Math.random() * Math.PI * 2;
    const profile = motionProfile(node);
    this.animatedRoots.push({
      root,
      baseY: node.position.y,
      baseScale: node.scale ?? 1,
      phase: root.userData.phase as number,
      ...profile,
      highlighted: node.highlighted ?? false,
    });
    if (node.kind === "machine" && node.detail?.startsWith("running")) {
      for (let index = 0; index < 6; index += 1) {
        const particle = new THREE.Mesh(
          new THREE.SphereGeometry(0.055, 10, 8),
          new THREE.MeshBasicMaterial({ color: node.color, transparent: true, opacity: 0.58 }),
        );
        particle.name = "running-machine-particle";
        root.add(particle);
        this.orbitParticles.push({ particle, baseY: 3.42, phase: index / 6, radius: 0.82, speed: 0.14 });
      }
      for (let index = 0; index < 3; index += 1) {
        const ring = new THREE.Mesh(
          new THREE.RingGeometry(0.75, 0.79, 48),
          new THREE.MeshBasicMaterial({
            color: node.color,
            transparent: true,
            opacity: 0.2,
            side: THREE.DoubleSide,
            depthWrite: false,
          }),
        );
        ring.name = "running-machine-pulse";
        ring.rotation.x = -Math.PI / 2;
        ring.position.y = 0.04;
        root.add(ring);
        this.pulseRings.push({ ring, phase: index / 3, speed: 0.42 });
      }
    }
    if (node.kind === "process") {
      let markerIndex = 0;
      root.traverse((part) => {
        if (!(part instanceof THREE.Mesh) || part.name !== "process-progress-marker") return;
        this.orbitParticles.push({
          particle: part,
          baseY: 0,
          phase: markerIndex / 2,
          radius: 0.61,
          speed: 0.22,
        });
        markerIndex += 1;
      });
    }
    if (node.highlighted) {
      const halo = new THREE.Mesh(
        new THREE.RingGeometry(shape.highlightRadius * 0.82, shape.highlightRadius, 42),
        new THREE.MeshBasicMaterial({ color: node.color, transparent: true, opacity: 0.62, side: THREE.DoubleSide }),
      );
      halo.name = "semantic-highlight";
      halo.rotation.x = -Math.PI / 2;
      halo.position.y = shape.highlightY;
      root.add(halo);
      const moteBase = Math.max(0.18, shape.highlightY + 0.22);
      const moteRise = Math.max(0.55, shape.stemStartY - moteBase);
      for (let index = 0; index < 9; index += 1) {
        const particle = new THREE.Mesh(
          new THREE.SphereGeometry(0.045, 9, 7),
          new THREE.MeshBasicMaterial({
            color: node.color,
            transparent: true,
            opacity: 0.5,
            depthWrite: false,
          }),
        );
        particle.name = "effect-mote";
        root.add(particle);
        this.effectMotes.push({
          particle,
          baseY: moteBase,
          phase: index / 9,
          radius: shape.highlightRadius * (0.38 + (index % 2) * 0.13),
          rise: moteRise,
          speed: 0.22 + (index % 3) * 0.035,
        });
      }
    }
    const labelAnchor = document.createElement("div");
    labelAnchor.className = "node-label-anchor";
    const label = document.createElement("div");
    label.className = `node-label node-${node.kind}${node.highlighted ? " is-highlighted" : ""}`;
    label.style.setProperty("--label-lift", `${labelLift(node)}px`);
    const title = document.createElement("strong");
    title.textContent = node.label;
    label.append(title);
    if (node.detail) {
      const detail = document.createElement("small");
      detail.textContent = node.detail;
      label.append(detail);
    }
    labelAnchor.append(label);
    const labelObject = new CSS2DObject(labelAnchor);
    labelObject.position.set(0, shape.stemStartY, 0);
    root.add(labelObject);
    this.content.add(root);
    this.selectable.push(root);
  }

  private pick(event: PointerEvent): void {
    if (!this.onSelect) return;
    const bounds = this.renderer.domElement.getBoundingClientRect();
    this.pointer.x = ((event.clientX - bounds.left) / bounds.width) * 2 - 1;
    this.pointer.y = -((event.clientY - bounds.top) / bounds.height) * 2 + 1;
    this.raycaster.setFromCamera(this.pointer, this.camera);
    const hit = this.raycaster.intersectObjects(this.selectable, true)[0];
    let selected = hit?.object;
    while (selected && typeof selected.userData.sceneId !== "string") selected = selected.parent ?? undefined;
    const id = selected?.userData.sceneId;
    if (typeof id === "string") this.onSelect(id);
  }

  private resize(): void {
    const width = Math.max(1, this.container.clientWidth);
    const height = Math.max(1, this.container.clientHeight);
    this.camera.aspect = width / height;
    this.camera.updateProjectionMatrix();
    this.renderer.setSize(width, height, false);
    this.labels.setSize(width, height);
  }

  private animate = (): void => {
    const now = performance.now();
    const seconds = now / 1000;
    this.animationFrame = requestAnimationFrame(this.animate);
    this.controls.update();
    for (const flow of this.flowLines) {
      const offset = flow.phase - seconds * flow.unitsPerSecond;
      for (let index = 0; index < flow.distances.count; index += 1) {
        flow.distances.setX(index, (flow.baseDistances[index] ?? 0) + offset);
      }
      flow.distances.needsUpdate = true;
    }
    for (const item of this.curveParticles) {
      const progress = (seconds * item.speed + item.phase) % 1;
      item.particle.position.copy(item.curve.getPoint(progress));
      item.particle.scale.setScalar(0.88 + Math.sin(progress * Math.PI) * item.pulse);
    }
    for (const item of this.effectMotes) {
      const progress = (seconds * item.speed + item.phase) % 1;
      const angle = progress * Math.PI * 2 + item.phase * Math.PI;
      item.particle.position.set(
        Math.cos(angle) * item.radius,
        item.baseY + progress * item.rise,
        Math.sin(angle) * item.radius,
      );
      const opacity = Math.sin(progress * Math.PI) * 0.58;
      if (item.particle.material instanceof THREE.MeshBasicMaterial) item.particle.material.opacity = opacity;
      item.particle.scale.setScalar(0.72 + Math.sin(progress * Math.PI) * 0.48);
    }
    for (const item of this.orbitParticles) {
      const angle = (seconds * item.speed + item.phase) * Math.PI * 2;
      item.particle.position.set(
        Math.cos(angle) * item.radius,
        item.baseY + Math.sin(angle * 2) * 0.045,
        Math.sin(angle) * item.radius,
      );
    }
    for (const item of this.animatedRoots) {
      const wave = Math.sin(seconds * item.speed * Math.PI * 2 + item.phase);
      const emphasis = item.highlighted ? 1.35 : 1;
      item.root.position.y = item.baseY + wave * item.bob * emphasis;
      item.root.rotation.y = wave * item.sway;
      const pulse = item.highlighted ? 0.055 : 0.018;
      item.root.scale.setScalar(item.baseScale * (1 + Math.sin(seconds * item.speed * Math.PI * 4 + item.phase) * pulse));
    }
    for (const item of this.pulseRings) {
      const progress = (seconds * item.speed + item.phase) % 1;
      item.ring.scale.setScalar(1 + progress * 1.9);
      if (item.ring.material instanceof THREE.MeshBasicMaterial) {
        item.ring.material.opacity = (1 - progress) * 0.24;
      }
    }
    this.renderer.render(this.scene, this.camera);
    this.labels.render(this.scene, this.camera);
  };

  dispose(): void {
    cancelAnimationFrame(this.animationFrame);
    this.resizeObserver.disconnect();
    this.controls.dispose();
    this.renderer.dispose();
    this.labels.domElement.remove();
    this.renderer.domElement.remove();
  }
}
