export const PROTOCOL_VERSION = 2;

export interface Vec3 {
  x: number;
  y: number;
  z: number;
}

export interface ThemeView {
  background: string;
  surface: string;
  accent: string;
}

export interface ResourceStyle {
  id: string;
  label: string;
  symbol: string;
  color: string;
  geometry: string;
  unit: string | null;
}

export interface AccountStyle {
  id: string;
  label: string;
  kind: string;
  color: string;
  position: Vec3;
}

export interface MachineStyle {
  id: string;
  label: string;
  color: string;
  position: Vec3;
}

export interface CameraStyle {
  position: Vec3;
  target: Vec3;
}

export interface PresentationView {
  theme: ThemeView;
  resources: ResourceStyle[];
  accounts: AccountStyle[];
  machines: MachineStyle[];
  camera: CameraStyle;
}

export interface HoldingView {
  account: string;
  resource: string;
  quantity: string;
}

export interface ResourceAmountView {
  resource: string;
  quantity: string;
}

export interface ProcessView {
  ticket: string;
  id: string;
  kind: string;
  progress: string;
  requiredWork: string;
}

export interface QueueView {
  id: string;
  stage: string;
  capacity: string | null;
  entries: ProcessView[];
}

export interface MachineView {
  id: string;
  inventory: string;
  mode: string;
  maximumQueues: string;
  queues: QueueView[];
}

export interface CustodyPositionView {
  id: string;
  source: string;
  destination: string;
  contents: ResourceAmountView[];
  active: boolean;
}

export interface StateView {
  holdings: HoldingView[];
  machines: MachineView[];
  custody: CustodyPositionView[];
  nextProcessId: string;
}

export interface ObservationView {
  account: string;
  resource: string;
  required: string;
  available: string;
}

export interface MovementView {
  source: string;
  destination: string;
  resource: string;
  quantity: string;
  sourceBefore: string;
  sourceAfter: string;
  destinationBefore: string;
  destinationAfter: string;
}

export interface BalanceChangeView {
  direction: string;
  account: string;
  resource: string;
  quantity: string;
  accountBefore: string;
  accountAfter: string;
  totalBefore: string;
  totalAfter: string;
}

export interface EffectView {
  kind: string;
  stage: string | null;
  sourceQueue: string | null;
  destinationQueue: string | null;
  process: string | null;
  ticket: string | null;
  before: string | null;
  after: string | null;
  position: string | null;
  positions: string[];
  account: string | null;
  remaining: string | null;
  disposition: string | null;
  observations: ObservationView[];
  movements: MovementView[];
  changes: BalanceChangeView[];
}

export interface IssueView {
  code: string;
  detail: string;
}

export interface CheckView {
  kind: "guard" | "requirement";
  condition: string;
  status: "accepted" | "rejected";
  detail: string;
  requirementIndex: number | null;
  account: string | null;
  observations: ObservationView[];
  issues: IssueView[];
}

export interface StepView {
  index: number;
  operation: string;
  trigger: string;
  status: "accepted" | "rejected";
  semanticStatus: string;
  before: StateView;
  after: StateView;
  checks: CheckView[];
  effects: EffectView[];
  issues: IssueView[];
}

export interface ProvenanceView {
  engine: string;
  toolchain: string;
  guarantees: string[];
}

export interface ScenarioArtifact {
  schemaVersion: number;
  id: string;
  gameId: string;
  title: string;
  summary: string;
  presentation: PresentationView;
  provenance: ProvenanceView;
  initial: StateView;
  steps: StepView[];
}

export interface CatalogEntry {
  id: string;
  gameId: string;
  title: string;
  summary: string;
  artifact: string;
}

export interface ShowcaseCatalog {
  schemaVersion: number;
  entries: CatalogEntry[];
}

function isRecord(value: unknown): value is Record<string, unknown> {
  return typeof value === "object" && value !== null && !Array.isArray(value);
}

function requireRecord(value: unknown, context: string): Record<string, unknown> {
  if (!isRecord(value)) throw new Error(`${context} must be an object`);
  return value;
}

function requireString(record: Record<string, unknown>, key: string, context: string): string {
  const value = record[key];
  if (typeof value !== "string") throw new Error(`${context}.${key} must be a string`);
  return value;
}

function requireArray(record: Record<string, unknown>, key: string, context: string): unknown[] {
  const value = record[key];
  if (!Array.isArray(value)) throw new Error(`${context}.${key} must be an array`);
  return value;
}

function requireVersion(record: Record<string, unknown>, context: string): void {
  if (record.schemaVersion !== PROTOCOL_VERSION) {
    throw new Error(`${context} uses unsupported schema version ${String(record.schemaVersion)}`);
  }
}

export function parseCatalog(value: unknown): ShowcaseCatalog {
  const catalog = requireRecord(value, "catalog");
  requireVersion(catalog, "catalog");
  const entries = requireArray(catalog, "entries", "catalog");
  for (const [index, rawEntry] of entries.entries()) {
    const entry = requireRecord(rawEntry, `catalog.entries[${index}]`);
    for (const key of ["id", "gameId", "title", "summary", "artifact"]) {
      requireString(entry, key, `catalog.entries[${index}]`);
    }
  }
  return value as ShowcaseCatalog;
}

function validateState(value: unknown, context: string): void {
  const state = requireRecord(value, context);
  requireArray(state, "holdings", context);
  requireArray(state, "machines", context);
  requireArray(state, "custody", context);
  requireString(state, "nextProcessId", context);
}

export function parseArtifact(value: unknown): ScenarioArtifact {
  const artifact = requireRecord(value, "artifact");
  requireVersion(artifact, "artifact");
  for (const key of ["id", "gameId", "title", "summary"]) {
    requireString(artifact, key, "artifact");
  }
  const presentation = requireRecord(artifact.presentation, "artifact.presentation");
  requireRecord(presentation.theme, "artifact.presentation.theme");
  requireRecord(presentation.camera, "artifact.presentation.camera");
  requireArray(presentation, "resources", "artifact.presentation");
  requireArray(presentation, "accounts", "artifact.presentation");
  requireArray(presentation, "machines", "artifact.presentation");
  validateState(artifact.initial, "artifact.initial");
  const steps = requireArray(artifact, "steps", "artifact");
  for (const [index, rawStep] of steps.entries()) {
    const step = requireRecord(rawStep, `artifact.steps[${index}]`);
    requireString(step, "operation", `artifact.steps[${index}]`);
    const status = requireString(step, "status", `artifact.steps[${index}]`);
    if (status !== "accepted" && status !== "rejected") {
      throw new Error(`artifact.steps[${index}].status is invalid`);
    }
    const checks = requireArray(step, "checks", `artifact.steps[${index}]`);
    for (const [checkIndex, rawCheck] of checks.entries()) {
      const check = requireRecord(rawCheck, `artifact.steps[${index}].checks[${checkIndex}]`);
      const checkKind = requireString(check, "kind", `artifact.steps[${index}].checks[${checkIndex}]`);
      if (checkKind !== "guard" && checkKind !== "requirement") {
        throw new Error(`artifact.steps[${index}].checks[${checkIndex}].kind is invalid`);
      }
      requireString(check, "condition", `artifact.steps[${index}].checks[${checkIndex}]`);
      const checkStatus = requireString(check, "status", `artifact.steps[${index}].checks[${checkIndex}]`);
      if (checkStatus !== "accepted" && checkStatus !== "rejected") {
        throw new Error(`artifact.steps[${index}].checks[${checkIndex}].status is invalid`);
      }
      requireString(check, "detail", `artifact.steps[${index}].checks[${checkIndex}]`);
      requireArray(check, "observations", `artifact.steps[${index}].checks[${checkIndex}]`);
      requireArray(check, "issues", `artifact.steps[${index}].checks[${checkIndex}]`);
    }
    requireArray(step, "effects", `artifact.steps[${index}]`);
    requireArray(step, "issues", `artifact.steps[${index}]`);
    validateState(step.before, `artifact.steps[${index}].before`);
    validateState(step.after, `artifact.steps[${index}].after`);
  }
  return value as ScenarioArtifact;
}

export function exactLabel(quantity: string, unit: string | null = null): string {
  return unit ? `${quantity} ${unit}` : quantity;
}
