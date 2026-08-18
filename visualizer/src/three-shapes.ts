import * as THREE from "three";
import type { SceneNode } from "./scene";

const LEDGER = {
  ink: "#161618",
  surface: "#202023",
  bone: "#eae6dc",
  steel: "#7e8a95",
};

export interface SemanticShape {
  root: THREE.Group;
  labelHeight: number;
  highlightRadius: number;
  highlightY: number;
}

interface PartOptions {
  color?: string;
  name: string;
  opacity?: number;
  position?: [number, number, number];
  rotation?: [number, number, number];
  scale?: [number, number, number];
  outline?: boolean;
}

function mixed(color: string, target: string, amount: number): string {
  return `#${new THREE.Color(color).lerp(new THREE.Color(target), amount).getHexString()}`;
}

export function createLedgerMaterial(color: string, opacity = 1): THREE.MeshStandardMaterial {
  return new THREE.MeshStandardMaterial({
    color,
    roughness: 0.62,
    metalness: 0.14,
    transparent: opacity < 1,
    opacity,
  });
}

function addPart(root: THREE.Group, geometry: THREE.BufferGeometry, options: PartOptions): THREE.Mesh {
  const mesh = new THREE.Mesh(
    geometry,
    createLedgerMaterial(options.color ?? LEDGER.surface, options.opacity),
  );
  mesh.name = options.name;
  if (options.position) mesh.position.set(...options.position);
  if (options.rotation) mesh.rotation.set(...options.rotation);
  if (options.scale) mesh.scale.set(...options.scale);
  mesh.castShadow = true;
  mesh.receiveShadow = true;
  root.add(mesh);

  if (options.outline) {
    const outline = new THREE.LineSegments(
      new THREE.EdgesGeometry(geometry),
      new THREE.LineBasicMaterial({
        color: mixed(options.color ?? LEDGER.surface, LEDGER.bone, 0.35),
        transparent: true,
        opacity: 0.45,
      }),
    );
    outline.name = `${options.name}-outline`;
    mesh.add(outline);
  }
  return mesh;
}

function addAccount(root: THREE.Group, node: SceneNode): void {
  const custodyAccount = node.detail === "custody";
  addPart(root, new THREE.CylinderGeometry(1.18, 1.3, 0.2, 28), {
    name: "account-plinth",
    color: LEDGER.ink,
    position: [0, 0.1, 0],
    outline: true,
  });
  addPart(root, new THREE.CylinderGeometry(0.96, 1.06, 0.14, 28), {
    name: "account-register",
    color: mixed(node.color, LEDGER.ink, 0.28),
    position: [0, 0.27, 0],
  });

  if (custodyAccount) {
    addPart(root, new THREE.BoxGeometry(1.05, 0.72, 0.82), {
      name: "custody-vault",
      color: mixed(node.color, LEDGER.ink, 0.22),
      position: [0, 0.69, 0],
      outline: true,
    });
    addPart(root, new THREE.TorusGeometry(0.25, 0.055, 10, 28), {
      name: "custody-vault-door",
      color: node.color,
      position: [0, 0.69, 0.43],
    });
    addPart(root, new THREE.CylinderGeometry(0.065, 0.065, 0.11, 12), {
      name: "custody-vault-key",
      color: LEDGER.bone,
      position: [0, 0.69, 0.5],
      rotation: [Math.PI / 2, 0, 0],
    });
    return;
  }

  addPart(root, new THREE.CylinderGeometry(0.2, 0.3, 0.55, 18), {
    name: "participant-body",
    color: mixed(node.color, LEDGER.ink, 0.08),
    position: [0, 0.62, 0],
  });
  addPart(root, new THREE.SphereGeometry(0.3, 20, 14), {
    name: "participant-head",
    color: node.color,
    position: [0, 1.08, 0],
  });
  addPart(root, new THREE.TorusGeometry(0.48, 0.045, 8, 30), {
    name: "participant-register-ring",
    color: LEDGER.steel,
    position: [0, 0.43, 0],
    rotation: [Math.PI / 2, 0, 0],
  });
}

function addMachine(root: THREE.Group, node: SceneNode): void {
  const chassis = mixed(node.color, LEDGER.ink, 0.26);
  const trim = mixed(node.color, LEDGER.bone, 0.24);
  addPart(root, new THREE.BoxGeometry(4.15, 0.32, 3.85), {
    name: "machine-footprint",
    color: LEDGER.ink,
    position: [0, 0.16, 0],
    outline: true,
  });
  addPart(root, new THREE.BoxGeometry(3.62, 1.55, 3.28), {
    name: "machine-lower-chassis",
    color: chassis,
    position: [0, 1.02, 0],
    outline: true,
  });
  addPart(root, new THREE.BoxGeometry(2.94, 0.92, 2.68), {
    name: "machine-upper-chassis",
    color: mixed(node.color, LEDGER.ink, 0.1),
    position: [0, 2.22, 0],
    outline: true,
  });
  addPart(root, new THREE.CylinderGeometry(1.42, 1.68, 0.3, 8), {
    name: "machine-octagonal-cap",
    color: trim,
    position: [0, 2.83, 0],
  });
  addPart(root, new THREE.CylinderGeometry(0.65, 0.83, 0.38, 16), {
    name: "machine-work-core",
    color: node.color,
    position: [0, 3.12, 0],
  });
  addPart(root, new THREE.TorusGeometry(0.7, 0.075, 9, 32), {
    name: "machine-core-register",
    color: LEDGER.bone,
    position: [0, 3.32, 0],
    rotation: [Math.PI / 2, 0, 0],
  });

  for (const x of [-1.65, 1.65]) {
    for (const z of [-1.44, 1.44]) {
      addPart(root, new THREE.CylinderGeometry(0.17, 0.22, 1.95, 12), {
        name: "machine-corner-column",
        color: trim,
        position: [x, 1.2, z],
      });
    }
  }
  addPart(root, new THREE.BoxGeometry(1.15, 0.72, 0.16), {
    name: "machine-service-port",
    color: node.color,
    position: [0, 1.18, 1.72],
    outline: true,
  });
  for (const y of [1.82, 2.05]) {
    addPart(root, new THREE.CylinderGeometry(0.075, 0.075, 3.25, 10), {
      name: "machine-cross-pipe",
      color: LEDGER.steel,
      position: [0, y, -1.52],
      rotation: [0, 0, Math.PI / 2],
    });
  }
}

function addQueue(root: THREE.Group, node: SceneNode): void {
  const bed = mixed(node.color, LEDGER.ink, 0.5);
  const wall = mixed(node.color, LEDGER.ink, 0.22);
  addPart(root, new THREE.BoxGeometry(1.95, 0.18, 1.55), {
    name: "queue-bed",
    color: bed,
    position: [0, 0.09, 0],
    outline: true,
  });
  addPart(root, new THREE.BoxGeometry(1.95, 0.78, 0.16), {
    name: "queue-back-wall",
    color: wall,
    position: [0, 0.48, 0.7],
    outline: true,
  });
  for (const x of [-0.9, 0.9]) {
    addPart(root, new THREE.BoxGeometry(0.16, 0.64, 1.38), {
      name: "queue-side-wall",
      color: wall,
      position: [x, 0.4, 0],
      outline: true,
    });
  }
  addPart(root, new THREE.BoxGeometry(1.95, 0.3, 0.16), {
    name: "queue-front-lip",
    color: node.color,
    position: [0, 0.22, -0.7],
  });
  addPart(root, new THREE.BoxGeometry(1.48, 0.055, 1.02), {
    name: "queue-stage-surface",
    color: node.color,
    opacity: 0.72,
    position: [0, 0.21, 0],
  });
  for (const x of [-0.48, 0, 0.48]) {
    addPart(root, new THREE.BoxGeometry(0.24, 0.075, 0.06), {
      name: "queue-capacity-mark",
      color: LEDGER.bone,
      position: [x, 0.42, -0.8],
    });
  }
}

function addProcess(root: THREE.Group, node: SceneNode): void {
  addPart(root, new THREE.IcosahedronGeometry(0.43, 1), {
    name: "process-work-core",
    color: node.color,
  });
  addPart(root, new THREE.TorusGeometry(0.61, 0.05, 8, 30), {
    name: "process-progress-ring-horizontal",
    color: LEDGER.bone,
    rotation: [Math.PI / 2, 0, 0],
  });
  addPart(root, new THREE.TorusGeometry(0.55, 0.035, 8, 30), {
    name: "process-progress-ring-vertical",
    color: LEDGER.steel,
    rotation: [0, Math.PI / 2, 0],
  });
  for (const x of [-0.61, 0.61]) {
    addPart(root, new THREE.SphereGeometry(0.09, 12, 8), {
      name: "process-progress-marker",
      color: node.color,
      position: [x, 0, 0],
    });
  }
}

function addCustody(root: THREE.Group, node: SceneNode): void {
  addPart(root, new THREE.TorusGeometry(0.62, 0.115, 12, 36), {
    name: "custody-loop",
    color: node.color,
  });
  addPart(root, new THREE.BoxGeometry(0.46, 0.38, 0.24), {
    name: "custody-lock-body",
    color: mixed(node.color, LEDGER.ink, 0.2),
    position: [0, -0.47, 0],
    outline: true,
  });
  addPart(root, new THREE.CylinderGeometry(0.055, 0.055, 0.13, 12), {
    name: "custody-keyhole",
    color: LEDGER.bone,
    position: [0, -0.47, 0.15],
    rotation: [Math.PI / 2, 0, 0],
  });
  for (const x of [-0.62, 0.62]) {
    addPart(root, new THREE.BoxGeometry(0.16, 0.28, 0.2), {
      name: "custody-binding",
      color: LEDGER.steel,
      position: [x, 0, 0],
    });
  }
}

function addResource(root: THREE.Group, node: SceneNode): void {
  switch (node.geometry) {
    case "cube":
      addPart(root, new THREE.BoxGeometry(0.58, 0.58, 0.58), {
        name: "resource-crate",
        color: node.color,
        outline: true,
      });
      addPart(root, new THREE.BoxGeometry(0.68, 0.08, 0.08), {
        name: "resource-crate-strap-x",
        color: LEDGER.bone,
      });
      addPart(root, new THREE.BoxGeometry(0.08, 0.68, 0.08), {
        name: "resource-crate-strap-y",
        color: LEDGER.bone,
      });
      break;
    case "cylinder":
      addPart(root, new THREE.CylinderGeometry(0.3, 0.3, 0.7, 18), {
        name: "resource-barrel",
        color: node.color,
      });
      for (const y of [-0.27, 0, 0.27]) {
        addPart(root, new THREE.TorusGeometry(0.305, 0.035, 8, 22), {
          name: "resource-barrel-band",
          color: LEDGER.bone,
          position: [0, y, 0],
          rotation: [Math.PI / 2, 0, 0],
        });
      }
      break;
    case "octahedron":
      addPart(root, new THREE.OctahedronGeometry(0.43), {
        name: "resource-crystal",
        color: node.color,
        outline: true,
      });
      addPart(root, new THREE.CylinderGeometry(0.27, 0.34, 0.12, 8), {
        name: "resource-crystal-base",
        color: LEDGER.steel,
        position: [0, -0.43, 0],
      });
      addPart(root, new THREE.TorusGeometry(0.34, 0.03, 8, 24), {
        name: "resource-crystal-register",
        color: LEDGER.bone,
        position: [0, -0.35, 0],
        rotation: [Math.PI / 2, 0, 0],
      });
      break;
    default:
      addPart(root, new THREE.CylinderGeometry(0.3, 0.38, 0.12, 20), {
        name: "resource-token-base",
        color: mixed(node.color, LEDGER.ink, 0.24),
        position: [0, -0.29, 0],
      });
      addPart(root, new THREE.CylinderGeometry(0.17, 0.25, 0.3, 18), {
        name: "resource-token-body",
        color: mixed(node.color, LEDGER.ink, 0.08),
        position: [0, -0.08, 0],
      });
      addPart(root, new THREE.SphereGeometry(0.28, 20, 14), {
        name: "resource-token-head",
        color: node.color,
        position: [0, 0.24, 0],
      });
  }
}

export function createSemanticShape(node: SceneNode): SemanticShape {
  const root = new THREE.Group();
  root.name = `semantic-${node.kind}`;
  switch (node.kind) {
    case "account":
      addAccount(root, node);
      return { root, labelHeight: 1.55, highlightRadius: 1.36, highlightY: 0.02 };
    case "machine":
      addMachine(root, node);
      return { root, labelHeight: 3.9, highlightRadius: 2.45, highlightY: 0.03 };
    case "queue":
      addQueue(root, node);
      return { root, labelHeight: 1.2, highlightRadius: 1.25, highlightY: 0.02 };
    case "process":
      addProcess(root, node);
      return { root, labelHeight: 1.05, highlightRadius: 0.78, highlightY: -0.55 };
    case "custody":
      addCustody(root, node);
      return { root, labelHeight: 1.05, highlightRadius: 0.82, highlightY: -0.72 };
    case "resource":
      addResource(root, node);
      return { root, labelHeight: 0.92, highlightRadius: 0.58, highlightY: -0.48 };
  }
}
