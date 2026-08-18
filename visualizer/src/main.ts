import "./style.css";
import {
  exactLabel,
  parseArtifact,
  parseCatalog,
  type CatalogEntry,
  type EffectView,
  type ScenarioArtifact,
  type ShowcaseCatalog,
  type StateView,
  type StepView,
} from "./protocol";
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
          <p id="scenario-summary">Loading proof-backed simulation artifacts…</p>
        </div>
        <div id="world" class="world" role="img" aria-label="Three-dimensional simulation state">
          <div class="loading-state"><span></span><p>Projecting Lean state</p></div>
          <div class="world-help">Drag to orbit · scroll to zoom · select an object</div>
        </div>
      </main>
      <aside class="inspector-panel panel">
        <div class="panel-heading"><span>Receipt inspector</span><small id="step-counter">initial</small></div>
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
  world: document.querySelector<HTMLElement>("#world")!,
  inspector: document.querySelector<HTMLElement>("#inspector")!,
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

function renderCatalog(): void {
  elements.catalogCount.textContent = `${catalog.entries.length} showcases`;
  elements.catalogList.innerHTML = catalog.entries.map((entry, index) => `
    <button class="catalog-entry${entry.id === selectedEntry.id ? " is-selected" : ""}" type="button" data-entry="${escapeHtml(entry.id)}">
      <span class="catalog-index">${String(index + 1).padStart(2, "0")}</span>
      <span><small>${escapeHtml(entry.gameId)}</small><b>${escapeHtml(entry.title)}</b><em>${escapeHtml(entry.summary)}</em></span>
    </button>
  `).join("");
  for (const button of elements.catalogList.querySelectorAll<HTMLButtonElement>("[data-entry]")) {
    button.addEventListener("click", () => void selectShowcase(button.dataset.entry ?? ""));
  }
}

function renderTimeline(): void {
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

function renderInspector(): void {
  const { state, step } = currentFrame();
  elements.stepCounter.textContent = step ? `step ${step.index} / ${artifact.steps.length}` : "initial";
  const operation = step ? `
    <section class="receipt-card status-${step.status}">
      <div class="receipt-kicker"><span>${escapeHtml(step.trigger)}</span><b>${escapeHtml(step.status)}</b></div>
      <h2>${escapeHtml(step.operation)}</h2>
      <div class="semantic-proof">${step.status === "accepted" ? "✓ exact receipt replay" : "⊘ no successor exposed"}</div>
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

  const selected = selectedSceneId ? `<div class="selected-object"><span>Selected</span><b>${escapeHtml(selectedSceneId)}</b></div>` : "";
  const holdings = state.holdings.map((holding) => {
    const resource = resourceLabel(holding.resource);
    return `<div class="holding-row"><i style="--resource:${escapeHtml(resource.color)}"></i><span><b>${escapeHtml(resource.label)}</b><small>${escapeHtml(accountLabel(holding.account))}</small></span><strong>${escapeHtml(exactLabel(holding.quantity, resource.unit))}</strong></div>`;
  }).join("");
  const queues = state.machines.flatMap((machine) => machine.queues.map((queue) => `
    <div class="queue-row"><span class="stage-${escapeHtml(queue.stage)}">${escapeHtml(queue.stage)}</span><b>${queue.entries.length}/${escapeHtml(queue.capacity ?? "∞")}</b>${queue.entries.length > 0 ? `<small>${queue.entries.map((entry) => escapeHtml(entry.kind)).join(", ")}</small>` : ""}</div>
  `)).join("");

  elements.inspector.innerHTML = `${operation}${selected}
    <section class="data-section"><div class="section-title"><span>World holdings</span><b>${state.holdings.length}</b></div>${holdings || `<p class="empty-copy">No positive holdings</p>`}</section>
    <section class="data-section"><div class="section-title"><span>Machine queues</span><b>${state.machines.reduce((sum, machine) => sum + machine.queues.length, 0)}</b></div>${queues || `<p class="empty-copy">No queues</p>`}</section>
  `;
}

function renderFrame(resetCamera = false): void {
  const { state, step } = currentFrame();
  document.documentElement.style.setProperty("--accent", artifact.presentation.theme.accent);
  document.documentElement.style.setProperty("--world-background", artifact.presentation.theme.background);
  renderer.update(projectScene(artifact, state, step?.effects ?? []), resetCamera);
  renderTimeline();
  renderInspector();
  elements.previous.disabled = currentStep < 0;
  elements.next.disabled = currentStep >= artifact.steps.length - 1;
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
  selectedEntry = entry;
  artifact = parseArtifact(await fetchJson(entry.artifact));
  currentStep = -1;
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
  catalog = parseCatalog(await fetchJson("generated/catalog.v1.json"));
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
  window.addEventListener("keydown", (event) => {
    if (event.target instanceof HTMLInputElement || event.target instanceof HTMLSelectElement) return;
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
