export const PROTOCOL_VERSION = 4;

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
  visibility: string;
  sealed: boolean;
  checks: CheckView[];
  effects: EffectView[];
  issues: IssueView[];
}

export interface CommandMessageView {
  id: string;
  sender: string;
  audience: string;
  statement: string;
  verification: string;
}

export interface CommandAgreementView {
  id: string;
  label: string;
  parties: string[];
  status: string;
  escrow: ResourceAmountView[];
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
  informationSet: string | null;
  messages: CommandMessageView[];
  agreements: CommandAgreementView[];
}

export interface CommandResolutionView {
  id: string;
  source: string;
  target: string;
  label: string;
  summary: string;
  actionIds: string[];
  automaticOrders: string[];
  reveal: string | null;
  steps: StepView[];
}

export interface CommandActorView {
  id: string;
  label: string;
  role: string;
  color: string;
}

export interface CommandInformationSetView {
  id: string;
  actor: string;
  label: string;
  detail: string;
  nodeIds: string[];
  observationKey: string;
}

export interface CommandGraphView {
  actor: string;
  root: string;
  nodes: CommandNodeView[];
  resolutions: CommandResolutionView[];
  actors: CommandActorView[];
  informationSets: CommandInformationSetView[];
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
  capability: "trace" | "commandable" | "both";
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

function requireBoolean(record: Record<string, unknown>, key: string, context: string): boolean {
  const value = record[key];
  if (typeof value !== "boolean") throw new Error(`${context}.${key} must be a boolean`);
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
  const normalizedEntries = entries.map((rawEntry, index) => {
    const entry = requireRecord(rawEntry, `catalog.entries[${index}]`);
    for (const key of ["id", "gameId", "title", "summary", "artifact"]) {
      requireString(entry, key, `catalog.entries[${index}]`);
    }
    const capability = entry.capability ?? "trace";
    if (capability !== "trace" && capability !== "commandable" && capability !== "both") {
      throw new Error(`catalog.entries[${index}].capability is invalid`);
    }
    return { ...entry, capability } as unknown as CatalogEntry;
  });
  return { ...catalog, entries: normalizedEntries } as unknown as ShowcaseCatalog;
}

function exactNatural(record: Record<string, unknown>, key: string, context: string): string {
  const value = requireString(record, key, context);
  if (!/^(0|[1-9][0-9]*)$/.test(value)) throw new Error(`${context}.${key} must be an exact natural decimal`);
  return value;
}

function records(record: Record<string, unknown>, key: string, context: string,
  visit: (item: Record<string, unknown>, path: string) => void): void {
  requireArray(record, key, context).forEach((value, index) => {
    const path = `${context}.${key}[${index}]`;
    visit(requireRecord(value, path), path);
  });
}

function strings(record: Record<string, unknown>, keys: string[], context: string): void {
  for (const key of keys) requireString(record, key, context);
}

function amounts(record: Record<string, unknown>, key: string, context: string): void {
  records(record, key, context, (item, path) => {
    requireString(item, "resource", path);
    exactNatural(item, "quantity", path);
  });
}

function validateState(value: unknown, context: string): void {
  const state = requireRecord(value, context);
  records(state, "holdings", context, (holding, path) => {
    strings(holding, ["account", "resource"], path);
    exactNatural(holding, "quantity", path);
  });
  assertUnique((state.holdings as HoldingView[]).map((holding) => JSON.stringify([holding.account, holding.resource])), `${context} holding keys`);
  const queueIds: string[] = [];
  records(state, "machines", context, (machine, path) => {
    strings(machine, ["id", "inventory", "mode"], path);
    const maximum = exactNatural(machine, "maximumQueues", path);
    records(machine, "queues", path, (queue, queuePath) => {
      queueIds.push(requireString(queue, "id", queuePath));
      const stage = requireString(queue, "stage", queuePath);
      if (!["input", "processing", "output"].includes(stage)) throw new Error(`${queuePath}.stage is invalid`);
      if (queue.capacity !== null) exactNatural(queue, "capacity", queuePath);
      records(queue, "entries", queuePath, (entry, entryPath) => {
        strings(entry, ["id", "kind"], entryPath);
        for (const key of ["ticket", "progress", "requiredWork"]) exactNatural(entry, key, entryPath);
      });
      assertUnique((queue.entries as ProcessView[]).map((entry) => entry.ticket), `${queuePath} tickets`);
      if (queue.capacity !== null && BigInt((queue.entries as unknown[]).length) > BigInt(queue.capacity as string)) throw new Error(`${queuePath} exceeds capacity`);
    });
    if (BigInt((machine.queues as unknown[]).length) > BigInt(maximum)) throw new Error(`${path} exceeds maximumQueues`);
  });
  assertUnique((state.machines as MachineView[]).map((machine) => machine.id), `${context} machine IDs`);
  assertUnique(queueIds, `${context} queue IDs`);
  records(state, "custody", context, (position, path) => {
    strings(position, ["id", "source", "destination"], path);
    requireBoolean(position, "active", path);
    amounts(position, "contents", path);
  });
  assertUnique((state.custody as CustodyPositionView[]).map((position) => position.id), `${context} custody IDs`);
  exactNatural(state, "nextProcessId", context);
  for (const key of ["logicalTick", "pendingIntents"]) if (state[key] !== null) exactNatural(state, key, context);
}

function validateObservations(record: Record<string, unknown>, context: string): void {
  records(record, "observations", context, (item, path) => {
    strings(item, ["account", "resource"], path);
    exactNatural(item, "required", path);
    exactNatural(item, "available", path);
  });
}

function canonicalData(value: unknown): string {
  if (Array.isArray(value)) return `[${value.map(canonicalData).join(",")}]`;
  if (isRecord(value)) return `{${Object.keys(value).sort().map((key) => `${JSON.stringify(key)}:${canonicalData(value[key])}`).join(",")}}`;
  return JSON.stringify(value);
}

function requireSameState(left: unknown, right: unknown, context: string): void {
  if (canonicalData(left) !== canonicalData(right)) throw new Error(`${context} states are disconnected`);
}

function validatePath(steps: unknown[], initial: unknown, context: string, target?: unknown): void {
  let previous = initial;
  for (const [index, raw] of steps.entries()) {
    const step = requireRecord(raw, `${context}[${index}]`);
    requireSameState(previous, step.before, `${context}[${index}].before`);
    previous = step.after;
  }
  if (target !== undefined) requireSameState(previous, target, `${context}.target`);
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
  requireNullableString(check, "account", context);
  if (check.requirementIndex !== null && (!Number.isSafeInteger(check.requirementIndex) || Number(check.requirementIndex) < 0)) throw new Error(`${context}.requirementIndex is invalid`);
  validateObservations(check, context);
  const issues = requireArray(check, "issues", context);
  for (const [index, issue] of issues.entries()) validateIssue(issue, `${context}.issues[${index}]`);
}

function validateEffect(value: unknown, context: string): void {
  const effect = requireRecord(value, context);
  requireString(effect, "kind", context);
  for (const key of ["stage", "sourceQueue", "destinationQueue", "process", "position", "account", "disposition"]) requireNullableString(effect, key, context);
  for (const key of ["ticket", "before", "after", "remaining"]) if (effect[key] !== null) exactNatural(effect, key, context);
  requireStringArray(effect, "positions", context);
  validateObservations(effect, context);
  records(effect, "movements", context, (movement, path) => {
    strings(movement, ["source", "destination", "resource"], path);
    for (const key of ["quantity", "sourceBefore", "sourceAfter", "destinationBefore", "destinationAfter"]) exactNatural(movement, key, path);
  });
  records(effect, "changes", context, (change, path) => {
    strings(change, ["direction", "account", "resource"], path);
    if (change.direction !== "debit" && change.direction !== "credit") throw new Error(`${path}.direction is invalid`);
    for (const key of ["quantity", "accountBefore", "accountAfter", "totalBefore", "totalAfter"]) exactNatural(change, key, path);
  });
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
  if (status === "rejected") {
    const { logicalTick: _a, pendingIntents: _b, ...before } = step.before as StateView;
    const { logicalTick: _c, pendingIntents: _d, ...after } = step.after as StateView;
    requireSameState(before, after, `${context} rejection`);
    if (effects.length !== 0) throw new Error(`${context} rejection cannot contain effects`);
  }
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
  const rawActors = requireArray(graph, "actors", context);
  const rawInformationSets = requireArray(graph, "informationSets", context);
  const actorIds = rawActors.map((rawActor, index) => {
    const actorContext = `${context}.actors[${index}]`;
    const actor = requireRecord(rawActor, actorContext);
    for (const key of ["id", "label", "role", "color"]) requireString(actor, key, actorContext);
    return requireString(actor, "id", actorContext);
  });
  assertUnique(actorIds, `${context} actor IDs`);
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
      exactNatural(metric, "value", metricContext);
      requireNullableString(metric, "unit", metricContext);
    }
    requireNullableString(node, "informationSet", nodeContext);
    const messages = requireArray(node, "messages", nodeContext);
    for (const [messageIndex, rawMessage] of messages.entries()) {
      const messageContext = `${nodeContext}.messages[${messageIndex}]`;
      const message = requireRecord(rawMessage, messageContext);
      for (const key of ["id", "sender", "audience", "statement", "verification"]) {
        requireString(message, key, messageContext);
      }
    }
    const agreements = requireArray(node, "agreements", nodeContext);
    for (const [agreementIndex, rawAgreement] of agreements.entries()) {
      const agreementContext = `${nodeContext}.agreements[${agreementIndex}]`;
      const agreement = requireRecord(rawAgreement, agreementContext);
      for (const key of ["id", "label", "status"]) requireString(agreement, key, agreementContext);
      requireStringArray(agreement, "parties", agreementContext);
      amounts(agreement, "escrow", agreementContext);
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
      if (candidate.actor !== graph.actor) {
        throw new Error(`${candidateContext}.actor must match the graph actor`);
      }
      requireString(candidate, "visibility", candidateContext);
      requireBoolean(candidate, "sealed", candidateContext);
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

  const informationSetIds: string[] = [];
  for (const [index, rawInformationSet] of rawInformationSets.entries()) {
    const informationSetContext = `${context}.informationSets[${index}]`;
    const informationSet = requireRecord(rawInformationSet, informationSetContext);
    informationSetIds.push(requireString(informationSet, "id", informationSetContext));
    for (const key of ["actor", "label", "detail", "observationKey"]) {
      requireString(informationSet, key, informationSetContext);
    }
    const memberIds = requireArray(informationSet, "nodeIds", informationSetContext);
    if (memberIds.length === 0 || memberIds.some((memberId) => typeof memberId !== "string")) {
      throw new Error(`${informationSetContext}.nodeIds must contain strings and cannot be empty`);
    }
    assertUnique(memberIds as string[], `${informationSetContext}.nodeIds`);
    if ((memberIds as string[]).some((memberId) => !nodeById.has(memberId))) {
      throw new Error(`${informationSetContext}.nodeIds must reference command nodes`);
    }
  }
  assertUnique(informationSetIds, `${context} information-set IDs`);
  const informationSetIdSet = new Set(informationSetIds);
  for (const node of nodes) {
    if (typeof node.informationSet === "string" && !informationSetIdSet.has(node.informationSet)) {
      throw new Error(`${context}.node(${String(node.id)}).informationSet must reference an information set`);
    }
  }

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
    requireNullableString(resolution, "reveal", resolutionContext);
    const steps = requireArray(resolution, "steps", resolutionContext);
    if (steps.length === 0) throw new Error(`${resolutionContext}.steps cannot be empty`);
    for (const [stepIndex, step] of steps.entries()) {
      validateStep(step, `${resolutionContext}.steps[${stepIndex}]`);
    }
    validatePath(steps, nodeById.get(source)!.state, `${resolutionContext}.steps`, nodeById.get(target)!.state);
    const firstStep = requireRecord(steps[0], `${resolutionContext}.steps[0]`);
    const firstIntentIds = requireArray(firstStep, "intentIds", `${resolutionContext}.steps[0]`);
    if (firstIntentIds.some((intentId) => typeof intentId !== "string")
      || actionSetKey(firstIntentIds as string[]) !== actionSetKey(actionIds as string[])) {
      throw new Error(`${resolutionContext} first tick must exactly match its selected action IDs`);
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

  for (const node of nodes) {
    const nodeId = requireString(node, "id", context);
    const acceptedIds = requireArray(node, "candidates", `${context}.node(${nodeId})`)
      .map((candidate, index) =>
        requireRecord(candidate, `${context}.node(${nodeId}).candidates[${index}]`))
      .filter((candidate) => candidate.status === "accepted")
      .map((candidate) => requireString(candidate, "id", `${context}.node(${nodeId}).candidate`));
    const outgoing = rawResolutions
      .map((resolution, index) =>
        requireRecord(resolution, `${context}.resolutions[${index}]`))
      .filter((resolution) => resolution.source === nodeId);
    if ((acceptedIds.length === 0) !== (outgoing.length === 0)) {
      throw new Error(`${context}.node(${nodeId}) terminal status is incomplete`);
    }
    for (const acceptedId of acceptedIds) {
      if (!outgoing.some((resolution) =>
        requireArray(resolution, "actionIds", `${context}.node(${nodeId}).resolution`)
          .includes(acceptedId))) {
        throw new Error(`${context}.node(${nodeId}) accepted candidate ${acceptedId} has no resolution`);
      }
    }
  }
}

function validatePresentation(presentation: Record<string, unknown>): void {
  const vector = (value: unknown, path: string) => {
    const position = requireRecord(value, path);
    for (const coordinate of ["x", "y", "z"]) if (typeof position[coordinate] !== "number" || !Number.isFinite(position[coordinate])) throw new Error(`${path}.${coordinate} must be finite`);
  };
  const theme = requireRecord(presentation.theme, "artifact.presentation.theme");
  strings(theme, ["background", "surface", "accent"], "artifact.presentation.theme");
  const camera = requireRecord(presentation.camera, "artifact.presentation.camera");
  vector(camera.position, "artifact.presentation.camera.position");
  vector(camera.target, "artifact.presentation.camera.target");
  for (const kind of ["resources", "accounts", "machines"]) {
    records(presentation, kind, "artifact.presentation", (style, path) => {
      strings(style, ["id", "label", "color"], path);
      if (kind === "resources") {
        strings(style, ["symbol", "geometry"], path);
        requireNullableString(style, "unit", path);
      } else {
        vector(style.position, `${path}.position`);
        if (kind === "accounts") requireString(style, "kind", path);
        else records(style, "modes", path, (mode, modePath) => {
          if (mode.position !== null) vector(mode.position, `${modePath}.position`);
        });
      }
    });
    assertUnique((presentation[kind] as { id: string }[]).map((style) => style.id), `artifact.presentation.${kind} IDs`);
  }
}

export function parseArtifact(value: unknown): ScenarioArtifact {
  const artifact = requireRecord(value, "artifact");
  requireVersion(artifact, "artifact");
  for (const key of ["id", "gameId", "title", "summary"]) {
    requireString(artifact, key, "artifact");
  }
  const provenance = requireRecord(artifact.provenance, "artifact.provenance");
  strings(provenance, ["engine", "toolchain"], "artifact.provenance");
  requireStringArray(provenance, "guarantees", "artifact.provenance");
  const presentation = requireRecord(artifact.presentation, "artifact.presentation");
  validatePresentation(presentation);
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
  validatePath(steps, artifact.initial, "artifact.steps");
  if (artifact.commandGraph !== undefined && artifact.commandGraph !== null) {
    validateCommandGraph(artifact.commandGraph, "artifact.commandGraph");
  }
  return { ...(value as Omit<ScenarioArtifact, "commandGraph">),
    commandGraph: (artifact.commandGraph as ScenarioArtifact["commandGraph"] | undefined) ?? null };
}

export function exactLabel(quantity: string, unit: string | null = null): string {
  return unit ? `${quantity} ${unit}` : quantity;
}
