import "./style.css";
import {
  exactLabel,
  parseArtifact,
  parseCatalog,
  type CatalogEntry,
  type CheckView,
  type CommandResolutionView,
  type EffectView,
  type ScenarioArtifact,
  type ShowcaseCatalog,
  type StateView,
  type StepView,
} from "./protocol";
import {
  advanceTrail,
  commandNode,
  compareMetrics,
  resolutionForSelection,
  rewindTrail,
  type CommandTrailEntry,
} from "./command";
import { projectScene } from "./scene";
import { ThreeSceneRenderer } from "./three-renderer";

const root = document.querySelector<HTMLDivElement>("#app");
if (!root) throw new Error("Missing application root");

root.innerHTML = `
  <div class="app-shell">
    <header class="topbar">
      <a class="brand" href="./" aria-label="Maquina visualizer home">
        <span class="brand-mark" aria-hidden="true"><i></i><i></i><i></i></span>
        <span><b>MAQUINA</b><small>proof-backed simulation atlas</small></span>
      </a>
      <div class="proof-chip"><span></span> Lean checked</div>
      <a class="source-link" href="https://github.com/BiomaAI/maquina" target="_blank" rel="noreferrer">Source ↗</a>
    </header>
    <div class="workspace">
      <aside class="catalog-panel panel">
        <div class="panel-heading"><span>Simulation atlas</span><small id="catalog-count">—</small></div>
        <div id="catalog-list" class="catalog-list" aria-label="Available simulations"></div>
        <div class="catalog-note">
          <span class="eyebrow">Shared protocol</span>
          <p>Every showcase is projected into the same scene document. The renderer contains no game rules.</p>
        </div>
      </aside>
      <main class="world-panel">
        <div class="world-heading">
          <div><span class="eyebrow" id="game-label">Loading</span><h1 id="scenario-title">Maquina</h1></div>
          <div class="world-heading-actions">
            <p id="scenario-summary">Loading proof-backed simulation artifacts…</p>
            <button id="command-mode" class="command-mode-button" type="button" hidden>Enter command mode</button>
          </div>
        </div>
        <div id="world" class="world" role="img" aria-label="Three-dimensional simulation state">
          <div class="loading-state"><span></span><p>Projecting Lean state</p></div>
          <div class="world-help">Drag to orbit · scroll to zoom · select an object</div>
        </div>
      </main>
      <aside class="inspector-panel panel">
        <div class="panel-heading"><span id="inspector-title">Receipt inspector</span><small id="step-counter">initial</small></div>
        <div id="inspector" class="inspector"></div>
      </aside>
    </div>
    <footer class="timeline-panel">
      <div class="transport">
        <button id="previous" class="transport-button" type="button" aria-label="Previous step">←</button>
        <button id="play" class="play-button" type="button" aria-label="Play simulation">▶</button>
        <button id="next" class="transport-button" type="button" aria-label="Next step">→</button>
      </div>
      <div id="timeline" class="timeline" aria-label="Simulation timeline"></div>
    </footer>
  </div>
`;

const elements = {
  catalogCount: document.querySelector<HTMLElement>("#catalog-count")!,
  catalogList: document.querySelector<HTMLElement>("#catalog-list")!,
  gameLabel: document.querySelector<HTMLElement>("#game-label")!,
  scenarioTitle: document.querySelector<HTMLElement>("#scenario-title")!,
  scenarioSummary: document.querySelector<HTMLElement>("#scenario-summary")!,
  commandMode: document.querySelector<HTMLButtonElement>("#command-mode")!,
  world: document.querySelector<HTMLElement>("#world")!,
  inspector: document.querySelector<HTMLElement>("#inspector")!,
  inspectorTitle: document.querySelector<HTMLElement>("#inspector-title")!,
  stepCounter: document.querySelector<HTMLElement>("#step-counter")!,
  timeline: document.querySelector<HTMLElement>("#timeline")!,
  previous: document.querySelector<HTMLButtonElement>("#previous")!,
  play: document.querySelector<HTMLButtonElement>("#play")!,
  next: document.querySelector<HTMLButtonElement>("#next")!,
};

let catalog: ShowcaseCatalog;
let selectedEntry: CatalogEntry;
let artifact: ScenarioArtifact;
let currentStep = -1;
let playing = false;
let playTimer: number | undefined;
let selectedSceneId: string | undefined;
let renderer: ThreeSceneRenderer;
let commandMode = false;
let commandNodeId = "";
let commandSelectedActions = new Set<string>();
let commandTrail: CommandTrailEntry[] = [];
let commandActiveResolution: CommandResolutionView | undefined;
let commandResolutionStep = -1;
let commandTimer: number | undefined;
let compareNodeId: string | undefined;

function escapeHtml(value: string): string {
  return value.replace(/[&<>'"]/g, (character) => ({
    "&": "&amp;",
    "<": "&lt;",
    ">": "&gt;",
    "'": "&#39;",
    '"': "&quot;",
  })[character] ?? character);
}

function assetUrl(path: string): string {
  return `${import.meta.env.BASE_URL}${path.replace(/^\//, "")}`;
}

async function fetchJson(path: string): Promise<unknown> {
  const response = await fetch(assetUrl(path));
  if (!response.ok) throw new Error(`Could not load ${path} (${response.status})`);
  return response.json() as Promise<unknown>;
}

function currentFrame(): { state: StateView; step?: StepView } {
  if (commandMode && artifact.commandGraph) {
    const animatedStep = commandActiveResolution?.steps[commandResolutionStep];
    const node = commandNode(artifact.commandGraph, commandNodeId);
    if (!node) throw new Error(`Unknown command snapshot ${commandNodeId}`);
    return { state: animatedStep?.after ?? node.state, step: animatedStep };
  }
  const step = currentStep >= 0 ? artifact.steps[currentStep] : undefined;
  return { state: step?.after ?? artifact.initial, step };
}

function accountLabel(id: string): string {
  return artifact.presentation.accounts.find((account) => account.id === id)?.label ?? id;
}

function resourceLabel(id: string): { label: string; unit: string | null; color: string } {
  const resource = artifact.presentation.resources.find((candidate) => candidate.id === id);
  return {
    label: resource?.label ?? id,
    unit: resource?.unit ?? null,
    color: resource?.color ?? artifact.presentation.theme.accent,
  };
}

function effectSummary(effect: EffectView): string[] {
  const summaries: string[] = [];
  for (const movement of effect.movements) {
    const resource = resourceLabel(movement.resource);
    summaries.push(
      `${exactLabel(movement.quantity, resource.unit)} ${resource.label}: ${accountLabel(movement.source)} → ${accountLabel(movement.destination)}`,
    );
  }
  for (const observation of effect.observations) {
    const resource = resourceLabel(observation.resource);
    summaries.push(
      `${accountLabel(observation.account)} has ${observation.available}; requires ${observation.required} ${resource.label}`,
    );
  }
  for (const change of effect.changes) {
    const resource = resourceLabel(change.resource);
    summaries.push(
      `${change.direction} ${exactLabel(change.quantity, resource.unit)} ${resource.label} at ${accountLabel(change.account)}`,
    );
  }
  if (summaries.length === 0) {
    const route = [effect.sourceQueue, effect.destinationQueue].filter(Boolean).join(" → ");
    const process = effect.process ? ` · ${effect.process.replace("process:", "process ")}` : "";
    summaries.push(`${effect.kind.replaceAll("-", " ")}${process}${route ? ` · ${route.split(":queue:").join(" / ")}` : ""}`);
  }
  return summaries;
}

function checkDetails(check: CheckView): string[] {
  const details = [check.detail];
  for (const observation of check.observations) {
    const resource = resourceLabel(observation.resource);
    details.push(
      `${accountLabel(observation.account)} has ${observation.available}; requires ${observation.required} ${resource.label}`,
    );
  }
  for (const issue of check.issues) {
    if (issue.detail !== check.detail) details.push(issue.detail);
  }
  return details;
}

function renderCatalog(): void {
  elements.catalogCount.textContent = `${catalog.entries.length} showcases`;
  elements.catalogList.innerHTML = catalog.entries.map((entry, index) => `
    <button class="catalog-entry${entry.id === selectedEntry.id ? " is-selected" : ""}" type="button" data-entry="${escapeHtml(entry.id)}">
      <span class="catalog-index">${String(index + 1).padStart(2, "0")}</span>
      <span><small>${escapeHtml(entry.gameId)} <i class="capability capability-${escapeHtml(entry.capability)}">${entry.capability === "both" ? "trace + command" : escapeHtml(entry.capability)}</i></small><b>${escapeHtml(entry.title)}</b><em>${escapeHtml(entry.summary)}</em></span>
    </button>
  `).join("");
  for (const button of elements.catalogList.querySelectorAll<HTMLButtonElement>("[data-entry]")) {
    button.addEventListener("click", () => void selectShowcase(button.dataset.entry ?? ""));
  }
}

function renderTimeline(): void {
  if (commandMode && artifact.commandGraph) {
    const trailPoints = commandTrail.map((entry, index) => {
      const node = commandNode(artifact.commandGraph!, entry.nodeId);
      if (!node) throw new Error(`Unknown command trail snapshot ${entry.nodeId}`);
      return `
        <button type="button" class="timeline-step command-trail-step status-${escapeHtml(node.outcome)}${index === commandTrail.length - 1 && !commandActiveResolution ? " is-selected" : ""}" data-command-trail="${index}" aria-label="Fork from ${escapeHtml(node.title)}">
          <i></i><span>${index}</span><small>${escapeHtml(node.title)}</small>
        </button>`;
    });
    const activePoints = commandActiveResolution?.steps.map((step, index) => `
      <div class="timeline-step command-tick status-${escapeHtml(step.status)}${index === commandResolutionStep ? " is-selected" : ""}">
        <i></i><span>${index + 1}</span><small>${escapeHtml(step.operation)}</small>
      </div>`) ?? [];
    elements.timeline.innerHTML = [...trailPoints, ...activePoints].join("");
    for (const button of elements.timeline.querySelectorAll<HTMLButtonElement>("[data-command-trail]")) {
      button.disabled = commandActiveResolution !== undefined;
      button.addEventListener("click", () => goToCommandTrail(Number(button.dataset.commandTrail)));
    }
    return;
  }
  const points = [{ label: "Initial", status: "initial" }, ...artifact.steps.map((step) => ({ label: step.operation, status: step.status }))];
  elements.timeline.innerHTML = points.map((point, index) => {
    const stepIndex = index - 1;
    const selected = stepIndex === currentStep;
    return `
      <button type="button" class="timeline-step status-${point.status}${selected ? " is-selected" : ""}" data-step="${stepIndex}" aria-label="${escapeHtml(point.label)}">
        <i></i><span>${index === 0 ? "0" : index}</span><small>${escapeHtml(point.label)}</small>
      </button>
    `;
  }).join("");
  for (const button of elements.timeline.querySelectorAll<HTMLButtonElement>("[data-step]")) {
    button.addEventListener("click", () => setStep(Number(button.dataset.step)));
  }
}

function renderStateData(state: StateView): string {
  const selected = selectedSceneId
    ? `<div class="selected-object"><span>Selected</span><b>${escapeHtml(selectedSceneId)}</b></div>`
    : "";
  const holdings = state.holdings.map((holding) => {
    const resource = resourceLabel(holding.resource);
    return `<div class="holding-row"><i style="--resource:${escapeHtml(resource.color)}"></i><span><b>${escapeHtml(resource.label)}</b><small>${escapeHtml(accountLabel(holding.account))}</small></span><strong>${escapeHtml(exactLabel(holding.quantity, resource.unit))}</strong></div>`;
  }).join("");
  const queues = state.machines.flatMap((machine) => machine.queues.map((queue) => `
    <div class="queue-row"><span class="stage-${escapeHtml(queue.stage)}">${escapeHtml(queue.stage)}</span><b>${queue.entries.length}/${escapeHtml(queue.capacity ?? "∞")}</b>${queue.entries.length > 0 ? `<small>${queue.entries.map((entry) => escapeHtml(entry.kind)).join(", ")}</small>` : ""}</div>
  `)).join("");
  const clock = state.logicalTick === null ? "" : `
    <section class="data-section"><div class="section-title"><span>Modeled time</span><b>tick ${escapeHtml(state.logicalTick)}</b></div>
      <div class="clock-row"><span>Pending scheduled intents</span><strong>${escapeHtml(state.pendingIntents ?? "0")}</strong></div>
    </section>`;
  return `${selected}${clock}
    <section class="data-section"><div class="section-title"><span>World holdings</span><b>${state.holdings.length}</b></div>${holdings || `<p class="empty-copy">No positive holdings</p>`}</section>
    <section class="data-section"><div class="section-title"><span>Machine queues</span><b>${state.machines.reduce((sum, machine) => sum + machine.queues.length, 0)}</b></div>${queues || `<p class="empty-copy">No queues</p>`}</section>`;
}

function commandCheckMarkup(check: CheckView): string {
  return `<div class="check-row status-${check.status}">
    <i>${check.status === "accepted" ? "✓" : "×"}</i>
    <span><b>${escapeHtml(check.condition.replaceAll("-", " "))}</b>${checkDetails(check).map((detail) => `<small>${escapeHtml(detail)}</small>`).join("")}</span>
  </div>`;
}

function commandStepMarkup(step: StepView, resolution: CommandResolutionView): string {
  return `<section class="receipt-card command-resolution-card status-${step.status}">
    <div class="receipt-kicker"><span>fork ${escapeHtml(resolution.id)}</span><b>tick ${commandResolutionStep + 1}/${resolution.steps.length}</b></div>
    <h2>${escapeHtml(step.operation)}</h2>
    <div class="semantic-proof">✓ immutable child history replays exactly</div>
    <p class="command-summary">${escapeHtml(resolution.summary)}</p>
    ${step.checks.map(commandCheckMarkup).join("")}
    ${step.issues.map((issue) => `<div class="issue"><b>${escapeHtml(issue.code.replaceAll("-", " "))}</b><small>${escapeHtml(issue.detail)}</small></div>`).join("")}
    ${step.effects.flatMap(effectSummary).map((summary) => `<div class="effect-row"><i></i><span>${escapeHtml(summary)}</span></div>`).join("")}
  </section>`;
}

function renderCommandInspector(): void {
  const graph = artifact.commandGraph;
  if (!graph) return;
  const node = commandNode(graph, commandNodeId);
  if (!node) throw new Error(`Unknown command snapshot ${commandNodeId}`);
  const { state, step } = currentFrame();
  elements.inspectorTitle.textContent = "Command assessment";

  if (commandActiveResolution && step) {
    elements.stepCounter.textContent = `resolving ${commandResolutionStep + 1}/${commandActiveResolution.steps.length}`;
    elements.inspector.innerHTML = `${commandStepMarkup(step, commandActiveResolution)}${renderStateData(state)}`;
    return;
  }

  elements.stepCounter.textContent = `snapshot ${node.id}`;
  const resolution = resolutionForSelection(graph, node.id, commandSelectedActions);
  const candidates = node.candidates.map((candidate) => {
    const selected = commandSelectedActions.has(candidate.id);
    const evidence = candidate.checks.map(commandCheckMarkup).join("");
    const effects = candidate.effects.flatMap(effectSummary)
      .map((summary) => `<div class="effect-row"><i></i><span>${escapeHtml(summary)}</span></div>`).join("");
    const issues = candidate.issues.map((issue) =>
      `<div class="issue"><b>${escapeHtml(issue.code.replaceAll("-", " "))}</b><small>${escapeHtml(issue.detail)}</small></div>`).join("");
    const heading = `
      <span class="command-candidate-top"><i>${candidate.status === "accepted" ? (selected ? "✓" : "+") : "×"}</i><b>${escapeHtml(candidate.label)}</b><em>${escapeHtml(candidate.status)}</em></span>
      <small>${escapeHtml(candidate.detail)}</small>
      <span class="command-component">${escapeHtml(candidate.component)}</span>`;
    const proof = `<details class="command-evidence"><summary>Proof evidence · ${candidate.checks.length} checks${candidate.issues.length > 0 ? ` · ${candidate.issues.length} issues` : ""}</summary>${evidence}${issues}${effects}</details>`;
    return candidate.status === "accepted"
      ? `<div class="command-candidate status-accepted${selected ? " is-selected" : ""}"><button type="button" class="command-candidate-select" data-command-action="${escapeHtml(candidate.id)}" aria-pressed="${selected}">${heading}</button>${proof}</div>`
      : `<div class="command-candidate status-rejected">${heading}${proof}</div>`;
  }).join("");

  const selectionMessage = commandSelectedActions.size === 0
    ? "Select one or more compatible accepted orders."
    : resolution
      ? `${resolution.label}: ${resolution.summary}`
      : "No modeled resolution matches this exact simultaneous order set.";
  const automaticOrders = resolution && resolution.automaticOrders.length > 0
    ? `<div class="automatic-orders"><span>Deterministic continuation</span>${resolution.automaticOrders.map((order) => `<i>${escapeHtml(order)}</i>`).join("")}</div>`
    : "";

  const terminals = graph.nodes.filter((candidate) => candidate.candidates.length === 0 && candidate.id !== node.id);
  const comparisonNode = compareNodeId ? commandNode(graph, compareNodeId) : undefined;
  const comparison = comparisonNode ? compareMetrics(node, comparisonNode) : [];
  const comparisonMarkup = node.candidates.length === 0 ? `
    <section class="command-comparison data-section">
      <div class="section-title"><span>Compare counterfactual</span><b>${comparisonNode ? "active" : "choose"}</b></div>
      <select id="command-compare" aria-label="Compare with another terminal snapshot">
        <option value="">Choose terminal snapshot…</option>
        ${terminals.map((terminal) => `<option value="${escapeHtml(terminal.id)}"${terminal.id === compareNodeId ? " selected" : ""}>${escapeHtml(`${terminal.title} · ${terminal.id}`)}</option>`).join("")}
      </select>
      ${comparisonNode ? `
        <div class="comparison-signature ${comparisonNode.stateKey === node.stateKey ? "is-equivalent" : ""}">${comparisonNode.stateKey === node.stateKey ? "Same actor-visible state · different immutable history" : "Distinct actor-visible state"}</div>
        ${comparison.map((metric) => `<div class="comparison-row"><span>${escapeHtml(metric.label)}</span><b>${escapeHtml(metric.baseline)} → ${escapeHtml(metric.alternative)}</b><strong class="${metric.delta.startsWith("-") ? "is-negative" : metric.delta === "0" ? "" : "is-positive"}">${escapeHtml(metric.delta)}</strong></div>`).join("")}` : ""}
    </section>` : "";

  elements.inspector.innerHTML = `
    <section class="command-node-card outcome-${escapeHtml(node.outcome)}">
      <div class="receipt-kicker"><span>immutable snapshot ${escapeHtml(node.id)}</span><b>${escapeHtml(node.outcome.replaceAll("-", " "))}</b></div>
      <h2>${escapeHtml(node.title)}</h2>
      <p>${escapeHtml(node.summary)}</p>
      <div class="state-signature" title="${escapeHtml(node.stateKey)}"><span>actor-visible state</span><code>${escapeHtml(node.stateKey)}</code></div>
      <div class="command-metrics">${node.metrics.map((metric) => `<div><span>${escapeHtml(metric.label)}</span><b>${escapeHtml(exactLabel(metric.value, metric.unit))}</b></div>`).join("")}</div>
    </section>
    ${node.candidates.length > 0 ? `<section class="command-orders"><div class="section-title"><span>Candidate orders</span><b>${node.candidates.filter((candidate) => candidate.status === "accepted").length} available</b></div>${candidates}
      <div class="command-resolution-bar"><p class="command-selection-message${commandSelectedActions.size > 0 && !resolution ? " is-warning" : ""}">${escapeHtml(selectionMessage)}</p>
      ${automaticOrders}
      <button id="resolve-command" class="resolve-command" type="button"${resolution ? "" : " disabled"}>Resolve exact order set</button></div>
    </section>` : `<section class="terminal-banner"><span>Mission outcome</span><b>${escapeHtml(node.outcome.replaceAll("-", " "))}</b><small>This bounded proof-backed branch has no further candidates.</small></section>`}
    <div class="command-controls"><button id="reset-command" type="button">Fork again from root</button><span>${commandTrail.length - 1} decisions</span></div>
    ${comparisonMarkup}
    ${renderStateData(state)}`;

  for (const button of elements.inspector.querySelectorAll<HTMLButtonElement>("[data-command-action]")) {
    button.addEventListener("click", () => toggleCommandAction(button.dataset.commandAction ?? ""));
  }
  elements.inspector.querySelector<HTMLButtonElement>("#resolve-command")
    ?.addEventListener("click", () => resolution && beginCommandResolution(resolution));
  elements.inspector.querySelector<HTMLButtonElement>("#reset-command")
    ?.addEventListener("click", resetCommandBranch);
  elements.inspector.querySelector<HTMLSelectElement>("#command-compare")
    ?.addEventListener("change", (event) => {
      compareNodeId = (event.currentTarget as HTMLSelectElement).value || undefined;
      renderCommandInspector();
    });
}

function renderInspector(): void {
  if (commandMode && artifact.commandGraph) {
    renderCommandInspector();
    return;
  }
  elements.inspectorTitle.textContent = "Receipt inspector";
  const { state, step } = currentFrame();
  elements.stepCounter.textContent = step?.logicalTick !== null && step?.logicalTick !== undefined
    ? `tick ${step.logicalTick} · ${step.index}/${artifact.steps.length}`
    : step ? `step ${step.index} / ${artifact.steps.length}` : "initial";
  const semanticProof = step?.status === "accepted"
    ? "✓ exact receipt replay"
    : step?.status === "mixed"
      ? "✓ accepted events replay · rejected intents preserve state"
      : "⊘ no successor exposed";
  const eventMetadata = step && (step.eventSequences.length > 0 || step.intentIds.length > 0) ? `
    <div class="event-metadata">
      ${step.logicalTick === null ? "" : `<span>tick <b>${escapeHtml(step.logicalTick)}</b></span>`}
      <span>events <b>${escapeHtml(step.eventSequences.join(", "))}</b></span>
      <span>intents <b>${escapeHtml(step.intentIds.join(", "))}</b></span>
    </div>` : "";
  const operation = step ? `
    <section class="receipt-card status-${step.status}">
      <div class="receipt-kicker"><span>${escapeHtml(step.trigger)}</span><b>${escapeHtml(step.status)}</b></div>
      <h2>${escapeHtml(step.operation)}</h2>
      <div class="semantic-proof">${semanticProof}</div>
      ${eventMetadata}
      ${step.checks.map((check) => `
        <div class="check-row status-${check.status}">
          <i>${check.status === "accepted" ? "✓" : "×"}</i>
          <span><b>${escapeHtml(check.condition.replaceAll("-", " "))}</b>${checkDetails(check).map((detail) => `<small>${escapeHtml(detail)}</small>`).join("")}</span>
        </div>`).join("")}
      ${step.issues.map((issue) => `<div class="issue"><b>${escapeHtml(issue.code.replaceAll("-", " "))}</b><small>${escapeHtml(issue.detail)}</small></div>`).join("")}
      ${step.effects.flatMap(effectSummary).map((summary) => `<div class="effect-row"><i></i><span>${escapeHtml(summary)}</span></div>`).join("")}
    </section>
  ` : `
    <section class="receipt-card status-initial">
      <div class="receipt-kicker"><span>scenario</span><b>ready</b></div>
      <h2>Initial state</h2>
      <div class="semantic-proof">Lean-constructed valid state</div>
      <p class="empty-copy">Advance the trace to inspect accepted effects and structured rejections.</p>
    </section>
  `;

  elements.inspector.innerHTML = `${operation}${renderStateData(state)}`;
}

function clearCommandTimer(): void {
  if (commandTimer !== undefined) window.clearTimeout(commandTimer);
  commandTimer = undefined;
}

function toggleCommandAction(actionId: string): void {
  if (!actionId || commandActiveResolution) return;
  if (commandSelectedActions.has(actionId)) commandSelectedActions.delete(actionId);
  else commandSelectedActions.add(actionId);
  compareNodeId = undefined;
  renderCommandInspector();
}

function finishCommandResolution(resolution: CommandResolutionView): void {
  clearCommandTimer();
  commandTrail = advanceTrail(commandTrail, resolution);
  commandNodeId = resolution.target;
  commandActiveResolution = undefined;
  commandResolutionStep = -1;
  commandSelectedActions.clear();
  compareNodeId = undefined;
  selectedSceneId = undefined;
  renderFrame();
}

function scheduleCommandTick(resolution: CommandResolutionView): void {
  commandTimer = window.setTimeout(() => {
    if (commandResolutionStep < resolution.steps.length - 1) {
      commandResolutionStep += 1;
      selectedSceneId = undefined;
      renderFrame();
      scheduleCommandTick(resolution);
    } else {
      finishCommandResolution(resolution);
    }
  }, 1350);
}

function beginCommandResolution(resolution: CommandResolutionView): void {
  if (!commandMode || commandActiveResolution || resolution.source !== commandNodeId) return;
  stopPlayback();
  clearCommandTimer();
  commandActiveResolution = resolution;
  commandResolutionStep = 0;
  selectedSceneId = undefined;
  renderFrame();
  scheduleCommandTick(resolution);
}

function goToCommandTrail(index: number): void {
  if (!artifact.commandGraph || commandActiveResolution) return;
  commandTrail = rewindTrail(commandTrail, index);
  commandNodeId = commandTrail.at(-1)!.nodeId;
  commandSelectedActions.clear();
  compareNodeId = undefined;
  selectedSceneId = undefined;
  renderFrame();
}

function resetCommandBranch(): void {
  const graph = artifact.commandGraph;
  if (!graph) return;
  clearCommandTimer();
  commandActiveResolution = undefined;
  commandResolutionStep = -1;
  commandNodeId = graph.root;
  commandTrail = [{ nodeId: graph.root, resolutionId: null }];
  commandSelectedActions.clear();
  compareNodeId = undefined;
  selectedSceneId = undefined;
  renderFrame();
}

function setCommandMode(enabled: boolean): void {
  if (enabled && !artifact.commandGraph) return;
  stopPlayback();
  clearCommandTimer();
  commandMode = enabled;
  commandActiveResolution = undefined;
  commandResolutionStep = -1;
  currentStep = -1;
  if (enabled) resetCommandBranch();
  else {
    commandTrail = [];
    commandSelectedActions.clear();
    compareNodeId = undefined;
    selectedSceneId = undefined;
    renderFrame();
  }
}

function renderFrame(resetCamera = false): void {
  const { state, step } = currentFrame();
  document.documentElement.style.setProperty("--accent", artifact.presentation.theme.accent);
  document.documentElement.style.setProperty("--world-background", artifact.presentation.theme.background);
  renderer.update(projectScene(artifact, state, step?.effects ?? []), resetCamera);
  renderer.setSelected(selectedSceneId);
  renderTimeline();
  renderInspector();
  elements.commandMode.hidden = artifact.commandGraph === null || selectedEntry.capability === "commandable";
  elements.commandMode.textContent = commandMode ? "Return to fixed trace" : "Enter command mode";
  elements.commandMode.classList.toggle("is-active", commandMode);
  elements.previous.disabled = commandMode || currentStep < 0;
  elements.play.disabled = commandMode || artifact.steps.length === 0;
  elements.next.disabled = commandMode || currentStep >= artifact.steps.length - 1;
}

function stopPlayback(): void {
  playing = false;
  elements.play.textContent = "▶";
  elements.play.setAttribute("aria-label", "Play simulation");
  if (playTimer !== undefined) window.clearInterval(playTimer);
  playTimer = undefined;
}

function togglePlayback(): void {
  if (playing) {
    stopPlayback();
    return;
  }
  if (currentStep >= artifact.steps.length - 1) setStep(-1);
  playing = true;
  elements.play.textContent = "Ⅱ";
  elements.play.setAttribute("aria-label", "Pause simulation");
  playTimer = window.setInterval(() => {
    if (currentStep >= artifact.steps.length - 1) {
      stopPlayback();
      return;
    }
    setStep(currentStep + 1, false);
  }, 1850);
}

function setStep(step: number, stop = true): void {
  if (stop) stopPlayback();
  currentStep = Math.max(-1, Math.min(artifact.steps.length - 1, step));
  selectedSceneId = undefined;
  renderFrame();
}

async function selectShowcase(id: string): Promise<void> {
  const entry = catalog.entries.find((candidate) => candidate.id === id) ?? catalog.entries[0];
  if (!entry) throw new Error("The showcase catalog is empty");
  stopPlayback();
  clearCommandTimer();
  selectedEntry = entry;
  artifact = parseArtifact(await fetchJson(entry.artifact));
  currentStep = -1;
  commandMode = entry.capability === "commandable" && artifact.commandGraph !== null;
  commandNodeId = artifact.commandGraph?.root ?? "";
  commandTrail = artifact.commandGraph ? [{ nodeId: artifact.commandGraph.root, resolutionId: null }] : [];
  commandSelectedActions.clear();
  commandActiveResolution = undefined;
  commandResolutionStep = -1;
  compareNodeId = undefined;
  selectedSceneId = undefined;
  elements.gameLabel.textContent = artifact.gameId;
  elements.scenarioTitle.textContent = artifact.title;
  elements.scenarioSummary.textContent = artifact.summary;
  const loading = elements.world.querySelector(".loading-state");
  loading?.remove();
  const url = new URL(window.location.href);
  url.searchParams.set("showcase", artifact.id);
  window.history.replaceState(null, "", url);
  renderCatalog();
  renderFrame(true);
}

async function initialize(): Promise<void> {
  catalog = parseCatalog(await fetchJson("generated/catalog.v3.json"));
  const requested = new URL(window.location.href).searchParams.get("showcase");
  selectedEntry = catalog.entries.find((entry) => entry.id === requested) ?? catalog.entries[0]!;
  renderer = new ThreeSceneRenderer(elements.world, (id) => {
    selectedSceneId = id;
    renderInspector();
  });
  renderCatalog();
  await selectShowcase(selectedEntry.id);
  elements.previous.addEventListener("click", () => setStep(currentStep - 1));
  elements.next.addEventListener("click", () => setStep(currentStep + 1));
  elements.play.addEventListener("click", togglePlayback);
  elements.commandMode.addEventListener("click", () => setCommandMode(!commandMode));
  window.addEventListener("keydown", (event) => {
    if (event.target instanceof HTMLInputElement || event.target instanceof HTMLSelectElement) return;
    if (commandMode) {
      if (event.key === "Escape") resetCommandBranch();
      return;
    }
    if (event.key === "ArrowLeft") setStep(currentStep - 1);
    if (event.key === "ArrowRight") setStep(currentStep + 1);
    if (event.key === " ") {
      event.preventDefault();
      togglePlayback();
    }
  });
}

initialize().catch((error: unknown) => {
  console.error(error);
  elements.world.innerHTML = `<div class="fatal-error"><b>Visualizer could not start</b><p>${escapeHtml(error instanceof Error ? error.message : String(error))}</p></div>`;
});
