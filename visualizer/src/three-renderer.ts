import * as THREE from "three";
import { OrbitControls } from "three/addons/controls/OrbitControls.js";
import { CSS2DObject } from "three/addons/renderers/CSS2DRenderer.js";
import { CSS2DRenderer } from "three/addons/renderers/CSS2DRenderer.js";
import type { SceneDocument, SceneNode } from "./scene";

interface ActiveMotion {
  particle: THREE.Mesh;
  curve: THREE.QuadraticBezierCurve3;
  startedAt: number;
  offset: number;
}

function vector(value: { x: number; y: number; z: number }): THREE.Vector3 {
  return new THREE.Vector3(value.x, value.y, value.z);
}

function material(color: string, opacity = 1): THREE.MeshStandardMaterial {
  return new THREE.MeshStandardMaterial({
    color,
    roughness: 0.48,
    metalness: 0.2,
    transparent: opacity < 1,
    opacity,
  });
}

function geometryFor(node: SceneNode): THREE.BufferGeometry {
  switch (node.kind) {
    case "account":
      return new THREE.CylinderGeometry(1.15, 1.35, 0.34, 28);
    case "machine":
      return new THREE.BoxGeometry(3.5, 2.8, 3.3, 2, 2, 2);
    case "queue":
      return new THREE.BoxGeometry(1.75, 0.55, 1.35);
    case "process":
      return new THREE.IcosahedronGeometry(0.48, 1);
    case "custody":
      return new THREE.TorusGeometry(0.62, 0.14, 12, 34);
    case "resource":
      switch (node.geometry) {
        case "cube": return new THREE.BoxGeometry(0.55, 0.55, 0.55);
        case "cylinder": return new THREE.CylinderGeometry(0.3, 0.3, 0.65, 18);
        case "octahedron": return new THREE.OctahedronGeometry(0.42);
        default: return new THREE.SphereGeometry(0.37, 20, 14);
      }
  }
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
  private readonly activeMotions: ActiveMotion[] = [];
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
    this.renderer.toneMappingExposure = 1.08;
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
    const hemisphere = new THREE.HemisphereLight(0xc7fff0, 0x14221d, 2.5);
    const key = new THREE.DirectionalLight(0xfff0d0, 3.4);
    key.position.set(8, 15, 10);
    key.castShadow = true;
    key.shadow.mapSize.set(2048, 2048);
    key.shadow.camera.left = -20;
    key.shadow.camera.right = 20;
    key.shadow.camera.top = 20;
    key.shadow.camera.bottom = -20;
    this.scene.add(hemisphere, key);

    const floorMaterial = new THREE.MeshStandardMaterial({ color: 0x0a1713, roughness: 0.93 });
    const floor = new THREE.Mesh(new THREE.PlaneGeometry(42, 30), floorMaterial);
    floor.rotation.x = -Math.PI / 2;
    floor.position.y = -0.22;
    floor.receiveShadow = true;
    this.scene.add(floor);

    const grid = new THREE.GridHelper(42, 42, 0x315b4e, 0x18352d);
    grid.position.y = -0.205;
    const gridMaterials = Array.isArray(grid.material) ? grid.material : [grid.material];
    for (const item of gridMaterials) {
      item.transparent = true;
      item.opacity = 0.36;
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
    this.activeMotions.length = 0;

    const positions = new Map(document.nodes.map((node) => [node.id, vector(node.position)]));
    for (const link of document.links) {
      const source = positions.get(link.source);
      const destination = positions.get(link.destination);
      if (!source || !destination) continue;
      const lineGeometry = new THREE.BufferGeometry().setFromPoints([source, destination]);
      const lineMaterial = link.dashed
        ? new THREE.LineDashedMaterial({ color: link.color, transparent: true, opacity: link.active ? 0.95 : 0.42, dashSize: 0.3, gapSize: 0.22 })
        : new THREE.LineBasicMaterial({ color: link.color, transparent: true, opacity: link.active ? 0.78 : 0.22 });
      const line = new THREE.Line(lineGeometry, lineMaterial);
      if (lineMaterial instanceof THREE.LineDashedMaterial) line.computeLineDistances();
      this.content.add(line);
    }

    for (const node of document.nodes) this.addNode(node);
    for (const [index, motion] of document.motions.entries()) {
      const source = positions.get(motion.source);
      const destination = positions.get(motion.destination);
      if (!source || !destination) continue;
      const apex = source.clone().lerp(destination, 0.5);
      apex.y += Math.max(1.4, source.distanceTo(destination) * 0.13);
      const curve = new THREE.QuadraticBezierCurve3(source, apex, destination);
      const path = new THREE.Line(
        new THREE.BufferGeometry().setFromPoints(curve.getPoints(32)),
        new THREE.LineBasicMaterial({ color: motion.color, transparent: true, opacity: 0.3 }),
      );
      const particle = new THREE.Mesh(new THREE.SphereGeometry(0.19, 14, 10), material(motion.color));
      particle.castShadow = true;
      particle.userData.motionLabel = motion.label;
      this.content.add(path, particle);
      this.activeMotions.push({ particle, curve, startedAt: performance.now(), offset: index * 0.17 });
    }

    if (resetCamera) {
      this.camera.position.copy(vector(document.camera.position));
      this.controls.target.copy(vector(document.camera.target));
      this.controls.update();
    }
    this.resize();
  }

  private addNode(node: SceneNode): void {
    const mesh = new THREE.Mesh(geometryFor(node), material(node.color, node.kind === "queue" ? 0.82 : 1));
    mesh.position.copy(vector(node.position));
    mesh.scale.setScalar(node.scale ?? 1);
    mesh.castShadow = node.kind !== "queue";
    mesh.receiveShadow = true;
    mesh.userData.sceneId = node.id;
    mesh.userData.baseScale = node.scale ?? 1;
    mesh.userData.highlighted = node.highlighted ?? false;
    mesh.userData.phase = Math.random() * Math.PI * 2;
    if (node.kind === "custody") mesh.rotation.x = Math.PI / 2;
    if (node.kind === "queue") {
      const edges = new THREE.LineSegments(
        new THREE.EdgesGeometry(mesh.geometry),
        new THREE.LineBasicMaterial({ color: node.color, transparent: true, opacity: 0.9 }),
      );
      mesh.add(edges);
    }
    if (node.highlighted) {
      const halo = new THREE.Mesh(
        new THREE.RingGeometry(0.85, 1.08, 36),
        new THREE.MeshBasicMaterial({ color: node.color, transparent: true, opacity: 0.62, side: THREE.DoubleSide }),
      );
      halo.rotation.x = -Math.PI / 2;
      halo.position.y = node.kind === "machine" ? -1.38 : -0.35;
      halo.scale.setScalar(node.kind === "machine" ? 2 : 0.8);
      mesh.add(halo);
    }
    const label = document.createElement("div");
    label.className = `node-label node-${node.kind}${node.highlighted ? " is-highlighted" : ""}`;
    const title = document.createElement("strong");
    title.textContent = node.label;
    label.append(title);
    if (node.detail) {
      const detail = document.createElement("small");
      detail.textContent = node.detail;
      label.append(detail);
    }
    const labelObject = new CSS2DObject(label);
    labelObject.position.set(0, node.kind === "machine" ? 2.05 : 0.9, 0);
    mesh.add(labelObject);
    this.content.add(mesh);
    this.selectable.push(mesh);
  }

  private pick(event: PointerEvent): void {
    if (!this.onSelect) return;
    const bounds = this.renderer.domElement.getBoundingClientRect();
    this.pointer.x = ((event.clientX - bounds.left) / bounds.width) * 2 - 1;
    this.pointer.y = -((event.clientY - bounds.top) / bounds.height) * 2 + 1;
    this.raycaster.setFromCamera(this.pointer, this.camera);
    const hit = this.raycaster.intersectObjects(this.selectable, false)[0];
    const id = hit?.object.userData.sceneId;
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
    this.animationFrame = requestAnimationFrame(this.animate);
    this.controls.update();
    for (const motion of this.activeMotions) {
      const elapsed = (now - motion.startedAt) / 1800 - motion.offset;
      const progress = ((elapsed % 1) + 1) % 1;
      motion.particle.position.copy(motion.curve.getPoint(progress));
      const pulse = 0.88 + Math.sin(progress * Math.PI) * 0.42;
      motion.particle.scale.setScalar(pulse);
    }
    this.content.traverse((object) => {
      if (!object.userData.highlighted) return;
      const scale = object.userData.baseScale as number;
      const phase = object.userData.phase as number;
      object.scale.setScalar(scale * (1 + Math.sin(now / 180 + phase) * 0.045));
    });
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
