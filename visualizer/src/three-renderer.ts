import * as THREE from "three";
import { OrbitControls } from "three/addons/controls/OrbitControls.js";
import { CSS2DObject, CSS2DRenderer } from "three/addons/renderers/CSS2DRenderer.js";
import { easeInOutCubic, rollingSpinDirection, transitionProgress } from "./motion";
import type { SceneDocument, SceneLink, SceneMotion, SceneNode } from "./scene";
import { createSemanticShape } from "./three-shapes";

interface NodeMove {
  curve: THREE.Curve<THREE.Vector3>;
  startsAt: number;
  duration: number;
}

interface NodeVisual {
  node: SceneNode;
  root: THREE.Group;
  label: HTMLDivElement;
  title: HTMLElement;
  detail: HTMLElement;
  baseScale: number;
  opacity: number;
  targetOpacity: number;
  revealAt: number;
  removing: boolean;
  move?: NodeMove;
  pulseAt?: number;
  pulseDuration: number;
  pendingNode?: SceneNode;
  contentAt?: number;
}

interface LinkVisual {
  link: SceneLink;
  line: THREE.Line;
  material: THREE.LineDashedMaterial;
  baseDistances: Float32Array;
  distances: THREE.BufferAttribute;
  opacity: number;
  targetOpacity: number;
  removing: boolean;
  phase: number;
}

interface TransferFlight {
  group: THREE.Group;
  payload: THREE.Group;
  path: THREE.Line;
  pathMaterial: THREE.LineDashedMaterial;
  trails: THREE.Mesh[];
  curve: THREE.QuadraticBezierCurve3;
  startsAt: number;
  duration: number;
  baseScale: number;
}

interface Mechanism {
  owner: THREE.Group;
  part: THREE.Object3D;
  mode: "spin-x" | "spin-y" | "spin-z" | "pulse";
  speed: number;
  baseRotation: THREE.Euler;
  baseScale: THREE.Vector3;
}

const CONVOY_WHEEL_SPIN = 2.4 * rollingSpinDirection(
  { x: 1, y: 0, z: 0 },
  { x: 0, y: 1, z: 0 },
  { x: 0, y: 0, z: 1 },
);

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

function connectionCurve(source: THREE.Vector3, destination: THREE.Vector3, emphasis = 1): THREE.QuadraticBezierCurve3 {
  const apex = source.clone().lerp(destination, 0.5);
  const horizontalDistance = Math.hypot(source.x - destination.x, source.z - destination.z);
  apex.y = Math.max(source.y, destination.y) + Math.min(1.8, (0.42 + horizontalDistance * 0.06) * emphasis);
  return new THREE.QuadraticBezierCurve3(source, apex, destination);
}

function materialList(object: THREE.Object3D): THREE.Material[] {
  if (!(object instanceof THREE.Mesh || object instanceof THREE.Line)) return [];
  return Array.isArray(object.material) ? object.material : [object.material];
}

function setObjectOpacity(object: THREE.Object3D, opacity: number): void {
  object.traverse((child) => {
    for (const material of materialList(child)) {
      const stored = material.userData.maquinaBaseOpacity;
      const baseOpacity = typeof stored === "number" ? stored : material.opacity;
      if (typeof stored !== "number") material.userData.maquinaBaseOpacity = baseOpacity;
      material.transparent = true;
      material.opacity = baseOpacity * opacity;
    }
  });
}

function disposeObject(object: THREE.Object3D): void {
  object.traverse((child) => {
    if (child instanceof THREE.Mesh || child instanceof THREE.Line) {
      child.geometry.dispose();
      for (const material of materialList(child)) material.dispose();
    }
    if (child instanceof CSS2DObject) child.element.remove();
  });
}

function linkOpacity(link: SceneLink): number {
  if (link.active) return 0.62;
  if (link.dashed) return 0.3;
  return 0.22;
}

function holdingNodeId(account: string, resource: string): string {
  return `holding:${account}:${resource}`;
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
  private readonly nodeVisuals = new Map<string, NodeVisual>();
  private readonly linkVisuals = new Map<string, LinkVisual>();
  private readonly transferFlights: TransferFlight[] = [];
  private mechanisms: Mechanism[] = [];
  private readonly resizeObserver: ResizeObserver;
  private currentDocument?: SceneDocument;
  private animationFrame = 0;
  private lastFrameAt = performance.now();

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

  private clearContent(): void {
    for (const child of [...this.content.children]) {
      this.content.remove(child);
      disposeObject(child);
    }
    this.nodeVisuals.clear();
    this.linkVisuals.clear();
    this.transferFlights.length = 0;
    this.mechanisms.length = 0;
    this.selectable.length = 0;
  }

  private positions(document: SceneDocument): Map<string, THREE.Vector3> {
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
    return positions;
  }

  update(document: SceneDocument, resetCamera = false): void {
    const now = performance.now();
    const initial = resetCamera || !this.currentDocument;
    if (initial) this.clearContent();
    this.currentDocument = document;
    this.scene.background = new THREE.Color(document.background);
    const positions = this.positions(document);

    this.reconcileNodes(document, now, initial);
    this.reconcileLinks(document.links, positions, initial);
    if (!initial) this.spawnTransfers(document.motions, positions, now);
    this.selectable.splice(0, this.selectable.length, ...[...this.nodeVisuals.values()].map((visual) => visual.root));

    if (resetCamera) {
      this.camera.position.copy(vector(document.camera.position));
      this.controls.target.copy(vector(document.camera.target));
      this.controls.update();
    }
    this.resize();
  }

  private reconcileNodes(document: SceneDocument, now: number, initial: boolean): void {
    const nextIds = new Set(document.nodes.map((node) => node.id));
    const destinationHoldings = new Set(document.motions.map((motion) => holdingNodeId(motion.destination, motion.resource)));
    const destinationAccounts = new Set(document.motions.map((motion) => motion.destination));

    for (const visual of this.nodeVisuals.values()) {
      if (nextIds.has(visual.node.id)) continue;
      visual.targetOpacity = 0;
      visual.removing = true;
      visual.revealAt = now;
      visual.pulseAt = undefined;
    }

    for (const node of document.nodes) {
      const existing = this.nodeVisuals.get(node.id);
      if (!existing) {
        const revealDelay = initial ? 0
          : destinationHoldings.has(node.id) ? 820
          : node.kind === "process" ? 140
          : 80;
        this.nodeVisuals.set(node.id, this.createNodeVisual(node, now, initial, revealDelay));
        continue;
      }

      existing.removing = false;
      existing.targetOpacity = 1;
      existing.revealAt = now;
      const target = vector(node.position);
      if (existing.root.position.distanceToSquared(target) > 0.0001) {
        existing.move = {
          curve: node.kind === "process"
            ? connectionCurve(existing.root.position.clone(), target, 0.85)
            : new THREE.LineCurve3(existing.root.position.clone(), target),
          startsAt: now + 60,
          duration: 980,
        };
      }

      const priorActivity = existing.node.activity;
      const contentChanged = existing.node.label !== node.label || existing.node.detail !== node.detail;
      existing.node = node;
      existing.baseScale = node.scale ?? 1;
      existing.label.classList.toggle("is-highlighted", node.highlighted ?? false);
      if (contentChanged) {
        existing.pendingNode = node;
        existing.contentAt = now + (document.motions.length > 0 ? 820 : 320);
      }
      if (priorActivity !== node.activity) this.syncMechanisms(existing);
      if (node.highlighted) {
        existing.pulseAt = now + (destinationAccounts.has(node.id) || destinationHoldings.has(node.id) ? 820 : 90);
        existing.pulseDuration = 620;
      }
    }
  }

  private createNodeVisual(node: SceneNode, now: number, immediate: boolean, revealDelay = 0): NodeVisual {
    const shape = createSemanticShape(node);
    const root = shape.root;
    root.position.copy(vector(node.position));
    root.userData.sceneId = node.id;

    const labelAnchor = document.createElement("div");
    labelAnchor.className = "node-label-anchor";
    const label = document.createElement("div");
    label.className = `node-label node-${node.kind}${node.highlighted ? " is-highlighted" : ""}`;
    label.style.setProperty("--label-lift", `${labelLift(node)}px`);
    const title = document.createElement("strong");
    const detail = document.createElement("small");
    label.append(title, detail);
    labelAnchor.append(label);
    const labelObject = new CSS2DObject(labelAnchor);
    labelObject.position.set(0, shape.stemStartY, 0);
    root.add(labelObject);

    const opacity = immediate ? 1 : 0;
    const visual: NodeVisual = {
      node,
      root,
      label,
      title,
      detail,
      baseScale: node.scale ?? 1,
      opacity,
      targetOpacity: 1,
      revealAt: now + revealDelay,
      removing: false,
      pulseAt: node.highlighted && !immediate ? now + revealDelay : undefined,
      pulseDuration: 620,
    };
    this.applyNodeContent(visual, node);
    setObjectOpacity(root, opacity);
    label.style.opacity = String(opacity);
    root.scale.setScalar(visual.baseScale * (immediate ? 1 : 0.88));
    this.content.add(root);
    this.syncMechanisms(visual);
    return visual;
  }

  private applyNodeContent(visual: NodeVisual, node: SceneNode): void {
    visual.title.textContent = node.label;
    visual.detail.textContent = node.detail ?? "";
    visual.detail.hidden = !node.detail;
    visual.label.classList.toggle("is-highlighted", node.highlighted ?? false);
  }

  private syncMechanisms(visual: NodeVisual): void {
    this.mechanisms = this.mechanisms.filter((mechanism) => mechanism.owner !== visual.root);
    const damage = visual.root.getObjectByName("convoy-damage");
    const extraction = visual.root.getObjectByName("convoy-extraction");
    if (damage) damage.visible = false;
    if (extraction) extraction.visible = false;
    const add = (name: string, mode: Mechanism["mode"], speed: number): void => {
      const part = visual.root.getObjectByName(name);
      if (!part) return;
      this.mechanisms.push({
        owner: visual.root,
        part,
        mode,
        speed,
        baseRotation: part.rotation.clone(),
        baseScale: part.scale.clone(),
      });
    };
    if (visual.node.activity === "running") {
      add("machine-work-core", "spin-y", 0.72);
      add("machine-core-register", "pulse", 1.25);
    }
    if (visual.node.activity === "processing") {
      add("process-progress-ring-horizontal", "spin-z", 1.1);
      add("process-progress-ring-vertical", "spin-y", 0.86);
      add("process-work-core", "pulse", 1.8);
    }
    if (visual.node.activity === "scanning") {
      add("radar-azimuth", "spin-y", 0.82);
      add("radar-feed", "pulse", 1.45);
    }
    if (visual.node.activity === "tracking") {
      add("radar-azimuth", "spin-y", 0.22);
      add("radar-track-beacon", "pulse", 2.1);
      add("battery-turret", "spin-y", 0.18);
      add("battery-warning", "pulse", 1.5);
    }
    if (visual.node.activity === "engaged") {
      add("battery-launcher", "pulse", 2.25);
      add("battery-warning", "pulse", 3.2);
    }
    if (visual.node.activity === "moving") {
      for (const axle of ["0-0", "0-1", "1-0", "1-1"]) {
        add(`convoy-wheel-${axle}`, "spin-z", CONVOY_WHEEL_SPIN);
      }
      add("convoy-beacon", "pulse", 1.65);
    }
    if (visual.node.activity === "damaged") {
      if (damage) damage.visible = true;
      add("battery-warning", "pulse", 4.1);
      add("convoy-beacon", "pulse", 4.1);
      add("convoy-damage", "pulse", 3.4);
    }
    if (visual.node.activity === "extracted") {
      if (extraction) extraction.visible = true;
      add("convoy-beacon", "pulse", 2.6);
      add("convoy-extraction", "pulse", 1.35);
      add("convoy-extraction-inner-ring", "spin-z", 0.72);
    }
  }

  private reconcileLinks(
    links: SceneLink[],
    positions: Map<string, THREE.Vector3>,
    initial: boolean,
  ): void {
    const nextIds = new Set(links.map((link) => link.id));
    for (const visual of this.linkVisuals.values()) {
      if (nextIds.has(visual.link.id)) continue;
      visual.targetOpacity = 0;
      visual.removing = true;
    }
    for (const [index, link] of links.entries()) {
      const source = positions.get(link.source);
      const destination = positions.get(link.destination);
      if (!source || !destination) continue;
      const existing = this.linkVisuals.get(link.id);
      if (!existing) {
        this.linkVisuals.set(link.id, this.createLinkVisual(link, source, destination, index, initial));
        continue;
      }
      existing.link = link;
      existing.targetOpacity = linkOpacity(link);
      existing.removing = false;
      existing.material.color.set(link.color);
      existing.material.dashSize = link.active ? 0.34 : 0.17;
      existing.material.gapSize = link.active ? 0.18 : 0.27;
      this.updateLinkGeometry(existing, source, destination);
    }
  }

  private createLinkVisual(
    link: SceneLink,
    source: THREE.Vector3,
    destination: THREE.Vector3,
    index: number,
    immediate: boolean,
  ): LinkVisual {
    const curve = connectionCurve(source, destination, link.active ? 1.1 : 1);
    const geometry = new THREE.BufferGeometry().setFromPoints(curve.getPoints(32));
    const targetOpacity = linkOpacity(link);
    const material = new THREE.LineDashedMaterial({
      color: link.color,
      transparent: true,
      opacity: immediate ? targetOpacity : 0,
      dashSize: link.active ? 0.34 : 0.17,
      gapSize: link.active ? 0.18 : 0.27,
    });
    const line = new THREE.Line(geometry, material);
    line.name = link.active ? "active-relation" : "structural-relation";
    line.computeLineDistances();
    this.content.add(line);
    const distances = line.geometry.getAttribute("lineDistance") as THREE.BufferAttribute;
    return {
      link,
      line,
      material,
      baseDistances: new Float32Array(distances.array),
      distances,
      opacity: immediate ? targetOpacity : 0,
      targetOpacity,
      removing: false,
      phase: -index * 0.13,
    };
  }

  private updateLinkGeometry(visual: LinkVisual, source: THREE.Vector3, destination: THREE.Vector3): void {
    visual.line.geometry.dispose();
    const curve = connectionCurve(source, destination, visual.link.active ? 1.1 : 1);
    visual.line.geometry = new THREE.BufferGeometry().setFromPoints(curve.getPoints(32));
    visual.line.computeLineDistances();
    visual.distances = visual.line.geometry.getAttribute("lineDistance") as THREE.BufferAttribute;
    visual.baseDistances = new Float32Array(visual.distances.array);
  }

  private spawnTransfers(motions: SceneMotion[], positions: Map<string, THREE.Vector3>, now: number): void {
    for (const [index, motion] of motions.entries()) {
      const source = positions.get(motion.source);
      const destination = positions.get(motion.destination);
      if (!source || !destination) continue;
      const curve = connectionCurve(source, destination, 1.45);
      const group = new THREE.Group();
      group.name = `transfer:${motion.label}`;

      const pathMaterial = new THREE.LineDashedMaterial({
        color: motion.color,
        transparent: true,
        opacity: 0,
        dashSize: 0.26,
        gapSize: 0.18,
        depthWrite: false,
      });
      const path = new THREE.Line(new THREE.BufferGeometry().setFromPoints(curve.getPoints(40)), pathMaterial);
      path.computeLineDistances();
      group.add(path);

      const payload = createSemanticShape({
        id: motion.id,
        kind: "resource",
        label: motion.label,
        color: motion.color,
        geometry: motion.geometry,
        position: { x: 0, y: 0, z: 0 },
      }).root;
      payload.name = "transfer-payload";
      setObjectOpacity(payload, 0);
      group.add(payload);

      const trails: THREE.Mesh[] = [];
      for (let trailIndex = 0; trailIndex < 4; trailIndex += 1) {
        const trail = new THREE.Mesh(
          new THREE.SphereGeometry(0.055 - trailIndex * 0.007, 9, 7),
          new THREE.MeshBasicMaterial({ color: motion.color, transparent: true, opacity: 0, depthWrite: false }),
        );
        trail.name = "transfer-trail";
        trails.push(trail);
        group.add(trail);
      }

      this.content.add(group);
      this.transferFlights.push({
        group,
        payload,
        path,
        pathMaterial,
        trails,
        curve,
        startsAt: now + 90 + index * 110,
        duration: 1080,
        baseScale: 0.58,
      });
    }
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

  private animateNodes(now: number, deltaSeconds: number): void {
    for (const [id, visual] of this.nodeVisuals) {
      if (visual.move) {
        const progress = transitionProgress(now, visual.move.startsAt, visual.move.duration);
        visual.root.position.copy(visual.move.curve.getPoint(easeInOutCubic(progress)));
        if (progress >= 1) visual.move = undefined;
      }
      if (visual.pendingNode && visual.contentAt !== undefined && now >= visual.contentAt) {
        this.applyNodeContent(visual, visual.pendingNode);
        visual.pendingNode = undefined;
        visual.contentAt = undefined;
      }

      const requestedOpacity = now >= visual.revealAt ? visual.targetOpacity : 0;
      visual.opacity = THREE.MathUtils.damp(visual.opacity, requestedOpacity, 11, deltaSeconds);
      setObjectOpacity(visual.root, visual.opacity);
      visual.label.style.opacity = String(visual.opacity);

      let pulse = 1;
      if (visual.pulseAt !== undefined && now >= visual.pulseAt) {
        const progress = transitionProgress(now, visual.pulseAt, visual.pulseDuration);
        pulse += Math.sin(progress * Math.PI) * 0.06;
        if (progress >= 1) visual.pulseAt = undefined;
      }
      const revealScale = 0.88 + visual.opacity * 0.12;
      visual.root.scale.setScalar(visual.baseScale * revealScale * pulse);

      if (visual.removing && visual.opacity < 0.012) {
        this.content.remove(visual.root);
        disposeObject(visual.root);
        this.nodeVisuals.delete(id);
        this.mechanisms = this.mechanisms.filter((mechanism) => mechanism.owner !== visual.root);
      }
    }
  }

  private animateLinks(now: number, deltaSeconds: number): void {
    for (const [id, visual] of this.linkVisuals) {
      visual.opacity = THREE.MathUtils.damp(visual.opacity, visual.targetOpacity, 9, deltaSeconds);
      visual.material.opacity = visual.opacity;
      if (visual.link.active) {
        const offset = visual.phase - now / 1000 * 0.38;
        for (let index = 0; index < visual.distances.count; index += 1) {
          visual.distances.setX(index, (visual.baseDistances[index] ?? 0) + offset);
        }
        visual.distances.needsUpdate = true;
      }
      if (visual.removing && visual.opacity < 0.01) {
        this.content.remove(visual.line);
        disposeObject(visual.line);
        this.linkVisuals.delete(id);
      }
    }
  }

  private animateTransfers(now: number): void {
    for (let index = this.transferFlights.length - 1; index >= 0; index -= 1) {
      const flight = this.transferFlights[index]!;
      const progress = transitionProgress(now, flight.startsAt, flight.duration);
      if (now < flight.startsAt) continue;
      const eased = easeInOutCubic(progress);
      flight.payload.position.copy(flight.curve.getPoint(eased));
      flight.payload.rotation.y = eased * Math.PI * 2;
      flight.payload.rotation.z = Math.sin(progress * Math.PI) * 0.18;
      flight.payload.scale.setScalar(flight.baseScale * (0.9 + Math.sin(progress * Math.PI) * 0.14));
      const visibility = Math.min(1, progress * 9, (1 - progress) * 9);
      setObjectOpacity(flight.payload, visibility);
      flight.pathMaterial.opacity = Math.sin(progress * Math.PI) * 0.34;

      for (const [trailIndex, trail] of flight.trails.entries()) {
        const trailingProgress = Math.max(0, eased - (trailIndex + 1) * 0.035);
        trail.position.copy(flight.curve.getPoint(trailingProgress));
        if (trail.material instanceof THREE.MeshBasicMaterial) {
          trail.material.opacity = Math.sin(progress * Math.PI) * (0.38 - trailIndex * 0.065);
        }
      }

      if (progress >= 1) {
        this.content.remove(flight.group);
        disposeObject(flight.group);
        this.transferFlights.splice(index, 1);
      }
    }
  }

  private animateMechanisms(now: number): void {
    const seconds = now / 1000;
    for (const mechanism of this.mechanisms) {
      const angle = seconds * mechanism.speed;
      if (mechanism.mode === "pulse") {
        const scale = 1 + Math.sin(angle * Math.PI * 2) * 0.035;
        mechanism.part.scale.copy(mechanism.baseScale).multiplyScalar(scale);
        continue;
      }
      mechanism.part.rotation.copy(mechanism.baseRotation);
      if (mechanism.mode === "spin-x") mechanism.part.rotation.x += angle;
      if (mechanism.mode === "spin-y") mechanism.part.rotation.y += angle;
      if (mechanism.mode === "spin-z") mechanism.part.rotation.z += angle;
    }
  }

  private animate = (): void => {
    const now = performance.now();
    const deltaSeconds = Math.min(0.05, (now - this.lastFrameAt) / 1000);
    this.lastFrameAt = now;
    this.animationFrame = requestAnimationFrame(this.animate);
    this.controls.update();
    this.animateNodes(now, deltaSeconds);
    this.animateLinks(now, deltaSeconds);
    this.animateTransfers(now);
    this.animateMechanisms(now);
    this.renderer.render(this.scene, this.camera);
    this.labels.render(this.scene, this.camera);
  };

  dispose(): void {
    cancelAnimationFrame(this.animationFrame);
    this.resizeObserver.disconnect();
    this.controls.dispose();
    this.clearContent();
    this.renderer.dispose();
    this.labels.domElement.remove();
    this.renderer.domElement.remove();
  }
}
