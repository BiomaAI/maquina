export const PROTOCOL_VERSION = 3;

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

export interface MachineModeStyle {
  mode: string;
  position: Vec3 | null;
  activity: string | null;
}

export interface MachineStyle {
  id: string;
  label: string;
  color: string;
  position: Vec3;
  geometry: string;
  modes: MachineModeStyle[];
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
  logicalTick: string | null;
  pendingIntents: string | null;
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
  kind: string;
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
  status: "accepted" | "rejected" | "mixed";
  semanticStatus: string;
  logicalTick: string | null;
  eventSequences: string[];
  intentIds: string[];
  before: StateView;
  after: StateView;
  checks: CheckView[];
  effects: EffectView[];
  issues: IssueView[];
}

export interface CommandMetricView {
  id: string;
  label: string;
  value: string;
  unit: string | null;
}

export interface CommandCandidateView {
  id: string;
  actor: string;
  component: string;
  label: string;
  detail: string;
  status: "accepted" | "rejected";
  checks: CheckView[];
  effects: EffectView[];
  issues: IssueView[];
}

export interface CommandNodeView {
  id: string;
  stateKey: string;
  title: string;
  summary: string;
  outcome: string;
  state: StateView;
  metrics: CommandMetricView[];
  candidates: CommandCandidateView[];
}

export interface CommandResolutionView {
  id: string;
  source: string;
  target: string;
  label: string;
  summary: string;
  actionIds: string[];
  automaticOrders: string[];
  steps: StepView[];
}

export interface CommandGraphView {
  actor: string;
  root: string;
  nodes: CommandNodeView[];
  resolutions: CommandResolutionView[];
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
  commandGraph: CommandGraphView | null;
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

function requireStringArray(record: Record<string, unknown>, key: string, context: string): void {
  const values = requireArray(record, key, context);
  if (values.some((value) => typeof value !== "string")) {
    throw new Error(`${context}.${key} must contain only strings`);
  }
}

function requireNullableString(record: Record<string, unknown>, key: string, context: string): void {
  const value = record[key];
  if (value !== null && typeof value !== "string") {
    throw new Error(`${context}.${key} must be a string or null`);
  }
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
  requireNullableString(state, "logicalTick", context);
  requireNullableString(state, "pendingIntents", context);
}

function validateIssue(value: unknown, context: string): void {
  const issue = requireRecord(value, context);
  requireString(issue, "code", context);
  requireString(issue, "detail", context);
}

function validateCheck(value: unknown, context: string): void {
  const check = requireRecord(value, context);
  requireString(check, "kind", context);
  requireString(check, "condition", context);
  const status = requireString(check, "status", context);
  if (status !== "accepted" && status !== "rejected") {
    throw new Error(`${context}.status is invalid`);
  }
  requireString(check, "detail", context);
  requireArray(check, "observations", context);
  const issues = requireArray(check, "issues", context);
  for (const [index, issue] of issues.entries()) validateIssue(issue, `${context}.issues[${index}]`);
}

function validateEffect(value: unknown, context: string): void {
  const effect = requireRecord(value, context);
  requireString(effect, "kind", context);
  requireArray(effect, "observations", context);
  requireArray(effect, "movements", context);
  requireArray(effect, "changes", context);
}

function validateStep(value: unknown, context: string): void {
  const step = requireRecord(value, context);
  if (!Number.isSafeInteger(step.index) || Number(step.index) < 0) {
    throw new Error(`${context}.index must be a non-negative safe integer`);
  }
  for (const key of ["operation", "trigger", "semanticStatus"]) requireString(step, key, context);
  const status = requireString(step, "status", context);
  if (status !== "accepted" && status !== "rejected" && status !== "mixed") {
    throw new Error(`${context}.status is invalid`);
  }
  requireNullableString(step, "logicalTick", context);
  requireStringArray(step, "eventSequences", context);
  requireStringArray(step, "intentIds", context);
  const checks = requireArray(step, "checks", context);
  for (const [index, check] of checks.entries()) validateCheck(check, `${context}.checks[${index}]`);
  const effects = requireArray(step, "effects", context);
  for (const [index, effect] of effects.entries()) validateEffect(effect, `${context}.effects[${index}]`);
  const issues = requireArray(step, "issues", context);
  for (const [index, issue] of issues.entries()) validateIssue(issue, `${context}.issues[${index}]`);
  validateState(step.before, `${context}.before`);
  validateState(step.after, `${context}.after`);
}

function assertUnique(values: string[], context: string): void {
  if (new Set(values).size !== values.length) throw new Error(`${context} must be unique`);
}

function actionSetKey(actionIds: string[]): string {
  return [...actionIds].sort().join("\u0000");
}

function validateCommandGraph(value: unknown, context: string): void {
  const graph = requireRecord(value, context);
  requireString(graph, "actor", context);
  const root = requireString(graph, "root", context);
  const rawNodes = requireArray(graph, "nodes", context);
  const rawResolutions = requireArray(graph, "resolutions", context);
  const nodes = rawNodes.map((rawNode, index) => {
    const nodeContext = `${context}.nodes[${index}]`;
    const node = requireRecord(rawNode, nodeContext);
    for (const key of ["id", "stateKey", "title", "summary", "outcome"]) {
      requireString(node, key, nodeContext);
    }
    validateState(node.state, `${nodeContext}.state`);
    const metrics = requireArray(node, "metrics", nodeContext);
    for (const [metricIndex, rawMetric] of metrics.entries()) {
      const metricContext = `${nodeContext}.metrics[${metricIndex}]`;
      const metric = requireRecord(rawMetric, metricContext);
      for (const key of ["id", "label", "value"]) requireString(metric, key, metricContext);
      requireNullableString(metric, "unit", metricContext);
    }
    const candidates = requireArray(node, "candidates", nodeContext);
    for (const [candidateIndex, rawCandidate] of candidates.entries()) {
      const candidateContext = `${nodeContext}.candidates[${candidateIndex}]`;
      const candidate = requireRecord(rawCandidate, candidateContext);
      for (const key of ["id", "actor", "component", "label", "detail"]) {
        requireString(candidate, key, candidateContext);
      }
      const status = requireString(candidate, "status", candidateContext);
      if (status !== "accepted" && status !== "rejected") {
        throw new Error(`${candidateContext}.status is invalid`);
      }
      const checks = requireArray(candidate, "checks", candidateContext);
      for (const [checkIndex, check] of checks.entries()) {
        validateCheck(check, `${candidateContext}.checks[${checkIndex}]`);
      }
      const effects = requireArray(candidate, "effects", candidateContext);
      for (const [effectIndex, effect] of effects.entries()) {
        validateEffect(effect, `${candidateContext}.effects[${effectIndex}]`);
      }
      const issues = requireArray(candidate, "issues", candidateContext);
      for (const [issueIndex, issue] of issues.entries()) {
        validateIssue(issue, `${candidateContext}.issues[${issueIndex}]`);
      }
    }
    assertUnique(
      candidates.map((candidate, candidateIndex) =>
        requireString(requireRecord(candidate, `${nodeContext}.candidates[${candidateIndex}]`), "id", nodeContext)),
      `${nodeContext} candidate IDs`,
    );
    return node;
  });

  const nodeIds = nodes.map((node) => requireString(node, "id", context));
  assertUnique(nodeIds, `${context} node IDs`);
  const nodeById = new Map(nodes.map((node) => [requireString(node, "id", context), node]));
  if (!nodeById.has(root)) throw new Error(`${context}.root must identify a node`);

  const resolutionIds: string[] = [];
  const actionSetsBySource = new Map<string, Set<string>>();
  for (const [index, rawResolution] of rawResolutions.entries()) {
    const resolutionContext = `${context}.resolutions[${index}]`;
    const resolution = requireRecord(rawResolution, resolutionContext);
    resolutionIds.push(requireString(resolution, "id", resolutionContext));
    const source = requireString(resolution, "source", resolutionContext);
    const target = requireString(resolution, "target", resolutionContext);
    for (const key of ["label", "summary"]) requireString(resolution, key, resolutionContext);
    if (!nodeById.has(source) || !nodeById.has(target)) {
      throw new Error(`${resolutionContext} must reference existing source and target nodes`);
    }
    const actionIds = requireArray(resolution, "actionIds", resolutionContext);
    if (actionIds.length === 0 || actionIds.some((actionId) => typeof actionId !== "string")) {
      throw new Error(`${resolutionContext}.actionIds must contain strings and cannot be empty`);
    }
    assertUnique(actionIds as string[], `${resolutionContext}.actionIds`);
    requireStringArray(resolution, "automaticOrders", resolutionContext);
    const steps = requireArray(resolution, "steps", resolutionContext);
    if (steps.length === 0) throw new Error(`${resolutionContext}.steps cannot be empty`);
    for (const [stepIndex, step] of steps.entries()) {
      validateStep(step, `${resolutionContext}.steps[${stepIndex}]`);
    }

    const sourceNode = nodeById.get(source)!;
    const candidates = requireArray(sourceNode, "candidates", `${context}.node(${source})`)
      .map((candidate, candidateIndex) =>
        requireRecord(candidate, `${context}.node(${source}).candidates[${candidateIndex}]`));
    const acceptedIds = new Set(candidates
      .filter((candidate) => candidate.status === "accepted")
      .map((candidate) => requireString(candidate, "id", `${context}.node(${source}).candidate`)));
    if ((actionIds as string[]).some((actionId) => !acceptedIds.has(actionId))) {
      throw new Error(`${resolutionContext}.actionIds must reference accepted source candidates`);
    }
    const key = actionSetKey(actionIds as string[]);
    const actionSets = actionSetsBySource.get(source) ?? new Set<string>();
    if (actionSets.has(key)) throw new Error(`${resolutionContext} duplicates a source action set`);
    actionSets.add(key);
    actionSetsBySource.set(source, actionSets);
  }
  assertUnique(resolutionIds, `${context} resolution IDs`);
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
  const machines = requireArray(presentation, "machines", "artifact.presentation");
  for (const [index, rawMachine] of machines.entries()) {
    const machine = requireRecord(rawMachine, `artifact.presentation.machines[${index}]`);
    requireString(machine, "geometry", `artifact.presentation.machines[${index}]`);
    const modes = requireArray(machine, "modes", `artifact.presentation.machines[${index}]`);
    for (const [modeIndex, rawMode] of modes.entries()) {
      const mode = requireRecord(rawMode, `artifact.presentation.machines[${index}].modes[${modeIndex}]`);
      requireString(mode, "mode", `artifact.presentation.machines[${index}].modes[${modeIndex}]`);
      requireNullableString(mode, "activity", `artifact.presentation.machines[${index}].modes[${modeIndex}]`);
    }
  }
  validateState(artifact.initial, "artifact.initial");
  const steps = requireArray(artifact, "steps", "artifact");
  for (const [index, rawStep] of steps.entries()) {
    validateStep(rawStep, `artifact.steps[${index}]`);
  }
  if (artifact.commandGraph !== undefined && artifact.commandGraph !== null) {
    validateCommandGraph(artifact.commandGraph, "artifact.commandGraph");
  }
  return { ...(value as Omit<ScenarioArtifact, "commandGraph">),
    commandGraph: (artifact.commandGraph as ScenarioArtifact["commandGraph"] | undefined) ?? null };
}

export function exactLabel(quantity: string, unit: string | null = null): string {
  return unit ? `${quantity} ${unit}` : quantity;
}
