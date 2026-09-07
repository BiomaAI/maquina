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
  outgoingResolutions,
  orderPlanCopy,
  isTerminalNode,
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
      <a class="brand" href="./" aria-label="Maquina Playground home">
        <span class="brand-mark" aria-hidden="true"><i></i><i></i><i></i></span>
        <span><b>MAQUINA</b><small>WORLD COMMAND</small></span>
      </a>
      <div class="proof-chip"><span></span> Lean checked</div>
      <a class="source-link" href="https://github.com/BiomaAI/maquina" target="_blank" rel="noreferrer">Source ↗</a>
    </header>
    <div class="workspace">
      <aside class="catalog-panel panel">
        <div class="panel-heading"><span>Playground</span><small id="catalog-count">—</small></div>
        <div id="catalog-list" class="catalog-list" aria-label="Available simulations"></div>
        <div class="catalog-note">
          <span class="eyebrow">Every choice leaves a trace</span>
          <p>Command a world. Follow the consequences. Rewind and discover another future.</p>
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
        <div id="world" class="world" role="region" aria-label="Interactive three-dimensional world">
          <div class="loading-state"><span></span><p>Projecting Lean state</p></div>
          <div id="world-hud" class="world-hud" aria-live="polite"></div>
          <div class="world-tools"><button id="camera-reset" type="button" aria-label="Reset camera">⌖ Overview</button><button id="camera-top" type="button">◇ Tactical</button><button id="labels-toggle" type="button" aria-pressed="false">Labels: focus</button><button id="branch-map-toggle" type="button">↗ Run history</button></div>
          <select id="object-select" class="object-select" aria-label="Inspect a world object"></select>
          <div id="branch-map" class="branch-map" hidden></div>
          <div class="world-help">DRAG TO ORBIT <i>·</i> SCROLL TO ZOOM <i>·</i> CLICK TO INSPECT</div>
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
      <div class="playback-options"><label for="playback-speed">Speed</label><select id="playback-speed" aria-label="Playback speed"><option value="0.5">0.5×</option><option value="1" selected>1×</option><option value="2">2×</option></select></div>
    </footer>
  </div>
`;

const elements = {
  hud: document.querySelector<HTMLElement>("#world-hud")!,
  objectSelect: document.querySelector<HTMLSelectElement>("#object-select")!,
  branchButton: document.querySelector<HTMLButtonElement>("#branch-map-toggle")!,
  branchMap: document.querySelector<HTMLElement>("#branch-map")!,
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
let commandPaused = false;
let playbackSpeed = 1;
let branchMapOpen = false;
let showcaseRequest = 0;
let renderedState: StateView | undefined;
let renderedStep: StepView | undefined;
let visitedTrails = new Map<string, CommandTrailEntry[]>();

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
  const activeEntry = elements.catalogList.querySelector<HTMLElement>(".is-selected");
  if (activeEntry && elements.catalogList.scrollWidth > elements.catalogList.clientWidth) {
    elements.catalogList.scrollLeft = activeEntry.offsetLeft - elements.catalogList.offsetLeft;
  }
  for (const button of elements.catalogList.querySelectorAll<HTMLButtonElement>("[data-entry]")) {
    button.addEventListener("click", () => void selectShowcase(button.dataset.entry ?? "").catch((error: unknown) => {
      elements.scenarioSummary.textContent = `Could not load this world: ${error instanceof Error ? error.message : String(error)}. Choose another world to retry.`;
    }));
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
  const reveal = resolution.reveal === null ? "" : `
    <div class="sealed-reveal">
      <span>simultaneous sealed reveal</span>
      <b>${escapeHtml(resolution.reveal)}</b>
    </div>`;
  return `<section class="receipt-card command-resolution-card status-${step.status}">
    <div class="receipt-kicker"><span>fork ${escapeHtml(resolution.id)}</span><b>tick ${commandResolutionStep + 1}/${resolution.steps.length}</b></div>
    <h2>${escapeHtml(step.operation)}</h2>
    <div class="semantic-proof">✓ immutable child history replays exactly</div>
    <p class="command-summary">${escapeHtml(resolution.summary)}</p>
    ${reveal}
    ${step.checks.map(commandCheckMarkup).join("")}
    ${step.issues.map((issue) => `<div class="issue"><b>${escapeHtml(issue.code.replaceAll("-", " "))}</b><small>${escapeHtml(issue.detail)}</small></div>`).join("")}
    ${step.effects.flatMap(effectSummary).map((summary) => `<div class="effect-row"><i></i><span>${escapeHtml(summary)}</span></div>`).join("")}
  </section>`;
}

function sceneObjectName(id: string): string {
  return projectScene(artifact, currentFrame().state).nodes.find((node) => node.id === id)?.label ?? accountLabel(id);
}

function inspectObject(id?: string): void {
  selectedSceneId = id;
  renderer.setSelected(id);
  if (id) renderer.focus(id);
  renderInspector();
  renderWorldHud();
}

function renderObjectCard(state: StateView): string {
  if (!selectedSceneId) return "";
  const machine = state.machines.find((item) => item.id === selectedSceneId);
  const account = machine?.inventory ?? selectedSceneId;
  const holdings = state.holdings.filter((holding) => holding.account === account);
  return `<section class="object-card"><div class="section-title"><span>Selected object</span><button type="button" id="clear-object" aria-label="Clear selected object">×</button></div>
    <h3>${escapeHtml(sceneObjectName(selectedSceneId))}</h3>
    ${machine ? `<span class="object-mode">${escapeHtml(machine.mode.replaceAll("-", " "))}</span>` : ""}
    ${holdings.map((holding) => `<div class="object-balance"><span>${escapeHtml(resourceLabel(holding.resource).label)}</span><b>${escapeHtml(exactLabel(holding.quantity, resourceLabel(holding.resource).unit))}</b></div>`).join("")}
    ${machine?.queues.map((queue) => `<div class="object-balance"><span>${escapeHtml(queue.stage)} queue</span><b>${queue.entries.length} / ${queue.capacity ?? "∞"}</b></div>`).join("") ?? ""}
    <small>Select an order below to direct this world.</small></section>`;
}

function bindObjectCard(): void {
  document.querySelector("#clear-object")?.addEventListener("click", () => inspectObject());
}

function renderCommandInspector(): void {
  const graph = artifact.commandGraph;
  if (!graph) return;
  const node = commandNode(graph, commandNodeId)!;
  const { state, step } = currentFrame();
  elements.inspectorTitle.textContent = commandActiveResolution ? "Resolution in progress" : "Command deck";
  elements.stepCounter.textContent = `TICK ${state.logicalTick ?? "0"}`;
  if (commandActiveResolution && step) {
    elements.inspector.innerHTML = `<div class="resolution-progress"><span>${commandPaused ? "PAUSED" : "RESOLVING"}</span><b>${commandResolutionStep + 1} / ${commandActiveResolution.steps.length}</b><progress value="${commandResolutionStep + 1}" max="${commandActiveResolution.steps.length}"></progress></div>
      ${commandStepMarkup(step, commandActiveResolution)}
      <button type="button" class="secondary-action" id="skip-resolution">Skip to result →</button>
      <details class="diagnostics"><summary>World state</summary>${renderStateData(state)}</details>`;
    document.querySelector("#skip-resolution")?.addEventListener("click", () => commandActiveResolution && finishCommandResolution(commandActiveResolution));
    return;
  }
  const terminal = isTerminalNode(graph, node);
  const resolution = resolutionForSelection(graph, node.id, commandSelectedActions);
  const plans = outgoingResolutions(graph, node.id);
  const focusedPlans = selectedSceneId ? plans.filter((plan) => plan.actionIds.some((id) => node.candidates.find((c) => c.id === id)?.component === selectedSceneId)) : [];
  const orderedPlans = [...focusedPlans, ...plans.filter((plan) => !focusedPlans.includes(plan))];
  const comparisonNode = compareNodeId ? commandNode(graph, compareNodeId) : undefined;
  const terminals = graph.nodes.filter((other) => other.id !== node.id && visitedTrails.has(other.id) && isTerminalNode(graph, other));
  const rootNode = commandNode(graph, graph.root)!;
  const metricMarkup = node.metrics.map((metric) => {
    const original = rootNode.metrics.find((other) => other.id === metric.id);
    const delta = original ? BigInt(metric.value) - BigInt(original.value) : 0n;
    return `<div><span>${escapeHtml(metric.label)}</span><b>${escapeHtml(exactLabel(metric.value, metric.unit))}</b>${delta !== 0n ? `<small>${delta > 0n ? "+" : ""}${delta} this run</small>` : ""}</div>`;
  }).join("");
  const evidence = node.candidates.map((candidate) => `<div class="command-candidate status-${candidate.status}">
    <div class="command-candidate-top"><i>${candidate.status === "accepted" ? "✓" : "×"}</i><b>${escapeHtml(candidate.label)}</b><em>${candidate.status === "accepted" ? "available" : "blocked"}</em></div>
    <small>${escapeHtml(candidate.detail)}</small><details class="command-evidence"><summary>Inspect ${candidate.checks.length} checks</summary>
    ${candidate.checks.map(commandCheckMarkup).join("")}${candidate.issues.map((issue) => `<div class="issue"><b>${escapeHtml(issue.code)}</b><small>${escapeHtml(issue.detail)}</small></div>`).join("")}
    </details></div>`).join("");
  elements.inspector.innerHTML = `${renderObjectCard(state)}
    <section class="decision-heading ${terminal ? "is-terminal" : ""}"><span class="eyebrow">${terminal ? "Run complete" : `Decision ${commandTrail.length}`}</span>
      <h2>${escapeHtml(node.title)}</h2><p>${escapeHtml(node.summary)}</p></section>
    ${node.messages.length ? `<section class="comms"><span class="eyebrow">Incoming transmission</span>${node.messages.map((message) => `<blockquote>“${escapeHtml(message.statement)}”<cite>${escapeHtml(graph.actors.find((actor) => actor.id === message.sender)?.label ?? "Command")} · ${escapeHtml(message.verification)}</cite></blockquote>`).join("")}</section>` : ""}
    ${node.agreements.length ? `<div class="pact-status">◇ ${node.agreements.map((agreement) => `${escapeHtml(agreement.label)} · ${escapeHtml(agreement.status)}`).join(" · ")}</div>` : ""}
    ${!terminal ? `<section class="order-plans"><div class="section-title"><span>Choose your next move</span><b>${plans.length} OPTIONS</b></div>${orderedPlans.map((plan, index) => {
      const copy = orderPlanCopy(graph, plan);
      const selected = plan.id === resolution?.id;
      return `<button type="button" class="order-plan${selected ? " is-selected" : ""}" data-plan="${escapeHtml(plan.id)}" aria-pressed="${selected}">
        <span class="order-number">${String(index + 1).padStart(2, "0")}</span><span class="order-copy"><b>${escapeHtml(copy.label)}</b><small>${escapeHtml(copy.detail)}</small><em>${copy.sealed ? "◇ SEALED ORDER" : `${plan.actionIds.length > 1 ? `${plan.actionIds.length} SIMULTANEOUS ORDERS` : "SINGLE ORDER"} · ${plan.steps.length} ${plan.steps.length === 1 ? "TICK" : "TICKS"}`}</em></span><span class="order-arrow">${selected ? "✓" : "↗"}</span></button>`;
    }).join("")}</section>
    <div class="command-resolution-bar"><button id="resolve-command" class="resolve-command" type="button"${resolution ? "" : " disabled"}>${resolution ? "Execute orders" : "Select a plan"}<span>→</span></button><p>${resolution ? "Your choice creates a new, rewindable branch." : "Choose a complete plan. Every combination shown is supported."}</p></div>` : `<section class="terminal-banner"><span>Outcome secured</span><b>${escapeHtml(node.outcome.replaceAll("-", " "))}</b><small>Rewind any decision to explore another future.</small></section>`}
    <div class="command-metrics">${metricMarkup}</div>
    ${terminal && terminals.length ? `<section class="command-comparison"><div class="section-title"><span>Compare your runs</span><b>${terminals.length}</b></div><select id="command-compare" aria-label="Compare with an explored outcome"><option value="">Choose another completed run…</option>${terminals.map((other) => `<option value="${escapeHtml(other.id)}"${other.id === compareNodeId ? " selected" : ""}>${escapeHtml(other.title)}</option>`).join("")}</select>${comparisonNode ? compareMetrics(node, comparisonNode).map((metric) => `<div class="comparison-row"><span>${escapeHtml(metric.label)}</span><b>${metric.baseline} → ${metric.alternative}</b><strong>${metric.delta}</strong></div>`).join("") : ""}</section>` : ""}
    <div class="command-controls"><button id="reset-command" type="button">↶ Start a new branch</button><span>${visitedTrails.size} snapshots explored</span></div>
    <details class="diagnostics"><summary>Rules & proof evidence</summary>${evidence}<code class="state-key">${escapeHtml(node.stateKey)}</code></details>
    <details class="diagnostics"><summary>Resources & queues</summary>${renderStateData(state)}</details>`;
  for (const button of elements.inspector.querySelectorAll<HTMLButtonElement>("[data-plan]")) {
    button.addEventListener("click", () => {
      const plan = plans.find((item) => item.id === button.dataset.plan)!;
      commandSelectedActions = new Set(plan.actionIds);
      renderCommandInspector();
      renderWorldHud();
      elements.inspector.querySelector<HTMLButtonElement>(`[data-plan="${plan.id}"]`)?.focus({ preventScroll: true });
    });
    button.addEventListener("mouseenter", () => {
      const plan = plans.find((item) => item.id === button.dataset.plan)!;
      renderer.highlight(plan.actionIds.map((id) => node.candidates.find((c) => c.id === id)?.component ?? ""));
    });
    button.addEventListener("mouseleave", () => renderer.highlight([]));
  }
  document.querySelector("#resolve-command")?.addEventListener("click", () => resolution && beginCommandResolution(resolution));
  document.querySelector("#reset-command")?.addEventListener("click", resetCommandBranch);
  document.querySelector<HTMLSelectElement>("#command-compare")?.addEventListener("change", (event) => {
    compareNodeId = (event.target as HTMLSelectElement).value || undefined;
    renderCommandInspector();
  });
  bindObjectCard();
}

function renderWorldHud(): void {
  const { state, step } = currentFrame();
  const node = commandMode && artifact.commandGraph ? commandNode(artifact.commandGraph, commandNodeId) : undefined;
  elements.hud.innerHTML = `<div class="hud-status"><span class="live-dot"></span>${commandActiveResolution ? (commandPaused ? "RESOLUTION PAUSED" : "ORDERS IN MOTION") : node ? (isTerminalNode(artifact.commandGraph!, node) ? "RUN COMPLETE" : "AWAITING YOUR COMMAND") : "MISSION REPLAY"}<b>T+${state.logicalTick ?? Math.max(0, currentStep + 1)}</b></div>
    <div class="hud-title">${escapeHtml(step?.operation ?? node?.title ?? "The world awaits.")}</div>
    <div class="hud-caption">${commandActiveResolution ? "Watch the consequences. Pause or step through any tick." : node ? `${commandTrail.length - 1} decisions made · ${visitedTrails.size} snapshots explored` : "A deterministic world. Every change leaves a trace."}</div>`;
  const scene = projectScene(artifact, state);
  const options = scene.nodes.filter((item) => item.kind === "machine" || item.kind === "account");
  elements.objectSelect.innerHTML = `<option value="">Inspect an object…</option>${options.map((item) => `<option value="${escapeHtml(item.id)}"${item.id === selectedSceneId ? " selected" : ""}>${escapeHtml(item.label)}</option>`).join("")}`;
  elements.branchButton.hidden = !node;
  elements.branchButton.textContent = `↗ Run history (${visitedTrails.size})`;
  elements.branchMap.hidden = !branchMapOpen || !node;
  if (node && artifact.commandGraph) {
    elements.branchMap.innerHTML = `<div class="section-title"><span>Your explored futures</span><button id="close-map" type="button" aria-label="Close run history">×</button></div><p>Return to an explored snapshot and choose again.</p>${[...visitedTrails.entries()].map(([id, trail]) => {
      const other = commandNode(artifact.commandGraph!, id)!;
      return `<button type="button" data-visited="${escapeHtml(id)}" class="branch-node${id === node.id ? " is-current" : ""}" style="--depth:${Math.min(trail.length - 1, 5)}"><span>${trail.length - 1}</span><b>${escapeHtml(other.title)}</b><small>${isTerminalNode(artifact.commandGraph!, other) ? "OUTCOME" : "DECISION"}</small></button>`;
    }).join("")}`;
    elements.branchMap.querySelector("#close-map")?.addEventListener("click", () => { branchMapOpen = false; renderWorldHud(); });
    for (const button of elements.branchMap.querySelectorAll<HTMLButtonElement>("[data-visited]")) {
      button.disabled = !!commandActiveResolution;
      button.addEventListener("click", () => {
        commandTrail = visitedTrails.get(button.dataset.visited!)!.map((item) => ({ ...item }));
        goToCommandTrail(commandTrail.length - 1);
        branchMapOpen = false;
        renderWorldHud();
      });
    }
  }
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

  elements.inspector.innerHTML = `${renderObjectCard(state)}${operation}<details class="diagnostics"><summary>Resources & queues</summary>${renderStateData(state)}</details>`;
  bindObjectCard();
}

function clearCommandTimer(): void {
  if (commandTimer !== undefined) window.clearTimeout(commandTimer);
  commandTimer = undefined;
}


function finishCommandResolution(resolution: CommandResolutionView): void {
  clearCommandTimer();
  commandTrail = advanceTrail(commandTrail, resolution);
  commandNodeId = resolution.target;
  visitedTrails.set(commandNodeId, commandTrail.map((entry) => ({ ...entry })));
  commandPaused = false;
  elements.inspector.scrollTop = 0;
  commandActiveResolution = undefined;
  commandResolutionStep = -1;
  commandSelectedActions.clear();
  compareNodeId = undefined;
  selectedSceneId = undefined;
  renderFrame();
}

function scheduleCommandTick(resolution: CommandResolutionView): void {
  clearCommandTimer();
  if (commandPaused) return;
  commandTimer = window.setTimeout(() => {
    if (commandResolutionStep < resolution.steps.length - 1) {
      commandResolutionStep += 1;
      selectedSceneId = undefined;
      renderFrame();
      scheduleCommandTick(resolution);
    } else {
      finishCommandResolution(resolution);
    }
  }, 1600 / playbackSpeed);
}

function beginCommandResolution(resolution: CommandResolutionView): void {
  if (!commandMode || commandActiveResolution || resolution.source !== commandNodeId) return;
  stopPlayback();
  clearCommandTimer();
  commandActiveResolution = resolution;
  commandPaused = false;
  elements.inspector.scrollTop = 0;
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
  if (resetCamera || state !== renderedState || step !== renderedStep) {
    renderer.update(projectScene(artifact, state, step?.effects ?? []), resetCamera);
    renderedState = state;
    renderedStep = step;
  }
  renderer.setSelected(selectedSceneId);
  renderTimeline();
  renderInspector();
  renderWorldHud();
  elements.commandMode.hidden = artifact.commandGraph === null || selectedEntry.capability === "commandable";
  elements.commandMode.textContent = commandMode ? "Return to fixed trace" : "Enter command mode";
  elements.commandMode.classList.toggle("is-active", commandMode);
  const resolving = commandMode && !!commandActiveResolution;
  elements.previous.disabled = commandMode ? (!resolving || commandResolutionStep <= 0) : currentStep < 0;
  elements.play.disabled = commandMode ? !resolving : artifact.steps.length === 0;
  elements.next.disabled = commandMode ? !resolving : currentStep >= artifact.steps.length - 1;
  const running = commandMode ? resolving && !commandPaused : playing;
  elements.play.textContent = running ? "Ⅱ" : "▶";
  elements.play.setAttribute("aria-label", running ? "Pause simulation" : "Play simulation");
}

function stopPlayback(): void {
  playing = false;
  elements.play.textContent = "▶";
  elements.play.setAttribute("aria-label", "Play simulation");
  if (playTimer !== undefined) window.clearInterval(playTimer);
  playTimer = undefined;
}

function togglePlayback(): void {
  if (commandMode) {
    if (!commandActiveResolution) return;
    commandPaused = !commandPaused;
    if (commandPaused) clearCommandTimer();
    else scheduleCommandTick(commandActiveResolution);
    renderFrame();
    return;
  }
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
  }, 1850 / playbackSpeed);
}

function setStep(step: number, stop = true): void {
  if (stop) stopPlayback();
  currentStep = Math.max(-1, Math.min(artifact.steps.length - 1, step));
  selectedSceneId = undefined;
  renderFrame();
}

function transportStep(direction: number): void {
  if (!commandMode) { setStep(currentStep + direction); return; }
  if (!commandActiveResolution) return;
  clearCommandTimer();
  commandPaused = true;
  if (direction > 0 && commandResolutionStep >= commandActiveResolution.steps.length - 1) {
    finishCommandResolution(commandActiveResolution);
    return;
  }
  commandResolutionStep = Math.max(0, commandResolutionStep + direction);
  renderFrame();
}

async function selectShowcase(id: string): Promise<void> {
  const request = ++showcaseRequest;
  const entry = catalog.entries.find((candidate) => candidate.id === id) ?? catalog.entries[0];
  if (!entry) throw new Error("The showcase catalog is empty");
  stopPlayback();
  clearCommandTimer();
  const loaded = parseArtifact(await fetchJson(entry.artifact));
  if (request !== showcaseRequest) return;
  selectedEntry = entry;
  artifact = loaded;
  visitedTrails = new Map();
  branchMapOpen = false;
  elements.inspector.scrollTop = 0;
  currentStep = -1;
  commandMode = entry.capability === "commandable" && artifact.commandGraph !== null;
  commandNodeId = artifact.commandGraph?.root ?? "";
  commandTrail = artifact.commandGraph ? [{ nodeId: artifact.commandGraph.root, resolutionId: null }] : [];
  if (commandTrail.length) visitedTrails.set(commandNodeId, commandTrail.map((item) => ({ ...item })));
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
  catalog = parseCatalog(await fetchJson("generated/catalog.v4.json"));
  const requested = new URL(window.location.href).searchParams.get("showcase");
  selectedEntry = catalog.entries.find((entry) => entry.id === requested) ?? catalog.entries[0]!;
  renderer = new ThreeSceneRenderer(elements.world, (id) => {
    inspectObject(id);
  });
  renderCatalog();
  await selectShowcase(selectedEntry.id);
  elements.previous.addEventListener("click", () => transportStep(-1));
  elements.next.addEventListener("click", () => transportStep(1));
  elements.play.addEventListener("click", togglePlayback);
  elements.commandMode.addEventListener("click", () => setCommandMode(!commandMode));
  elements.objectSelect.addEventListener("change", () => inspectObject(elements.objectSelect.value || undefined));
  elements.branchButton.addEventListener("click", () => { branchMapOpen = !branchMapOpen; renderWorldHud(); });
  document.querySelector("#camera-reset")!.addEventListener("click", () => renderer.overview());
  document.querySelector("#camera-top")!.addEventListener("click", () => renderer.overview(true));
  document.querySelector<HTMLButtonElement>("#labels-toggle")!.addEventListener("click", (event) => {
    const button = event.currentTarget as HTMLButtonElement;
    const all = button.getAttribute("aria-pressed") !== "true";
    button.setAttribute("aria-pressed", String(all));
    button.textContent = all ? "Labels: all" : "Labels: focus";
    renderer.setAllLabels(all);
  });
  document.querySelector<HTMLSelectElement>("#playback-speed")!.addEventListener("change", (event) => {
    playbackSpeed = Number((event.target as HTMLSelectElement).value);
    if (commandActiveResolution && !commandPaused) scheduleCommandTick(commandActiveResolution);
    else if (playing) { stopPlayback(); togglePlayback(); }
  });
  window.addEventListener("keydown", (event) => {
    if (event.target instanceof HTMLElement && (event.target.closest("input, select, textarea, button, summary, a") || event.target.isContentEditable)) return;
    if (event.key === "ArrowLeft") { event.preventDefault(); transportStep(-1); }
    if (event.key === "ArrowRight") { event.preventDefault(); transportStep(1); }
    if (event.key === " ") { event.preventDefault(); togglePlayback(); }
    if (event.key === "Escape") { branchMapOpen = false; inspectObject(); }
  });
}

initialize().catch((error: unknown) => {
  console.error(error);
  elements.world.innerHTML = `<div class="fatal-error"><b>Playground could not start</b><p>${escapeHtml(error instanceof Error ? error.message : String(error))}</p></div>`;
});
