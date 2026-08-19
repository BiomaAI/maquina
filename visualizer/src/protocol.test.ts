import { readFileSync } from "node:fs";
import { describe, expect, it } from "vitest";
import { parseArtifact, parseCatalog } from "./protocol";
import { projectScene } from "./scene";

function fixture(name: string): unknown {
  const url = new URL(`../public/generated/${name}`, import.meta.url);
  return JSON.parse(readFileSync(url, "utf8")) as unknown;
}

describe("Lean-owned showcase artifacts", () => {
  it("publishes a versioned catalog with multiple scenarios", () => {
    const catalog = parseCatalog(fixture("catalog.v2.json"));
    expect(catalog.schemaVersion).toBe(2);
    expect(catalog.entries.map((entry) => entry.id)).toEqual([
      "foundry-refuel-lifecycle",
      "foundry-active-presence",
      "foundry-operating-guards",
      "foundry-multi-machine-body-contention",
    ]);
  });

  it("retains exact decimal quantities and replay provenance", () => {
    const artifact = parseArtifact(fixture("foundry-refuel-lifecycle.v2.json"));
    expect(typeof artifact.initial.nextProcessId).toBe("string");
    expect(artifact.steps).toHaveLength(7);
    expect(artifact.steps.every((step) => step.semanticStatus.startsWith("lean-"))).toBe(true);
    expect(artifact.steps.flatMap((step) => step.checks).some((check) => check.condition === "possession")).toBe(true);
    expect(artifact.steps.flatMap((step) => step.effects).some((effect) => effect.kind === "transfer")).toBe(true);
  });

  it("represents rejections as unchanged states with no effects", () => {
    const artifact = parseArtifact(fixture("foundry-active-presence.v2.json"));
    const rejected = artifact.steps.filter((step) => step.status === "rejected");
    expect(rejected).toHaveLength(2);
    for (const step of rejected) {
      expect(step.after).toEqual(step.before);
      expect(step.effects).toEqual([]);
      expect(step.issues.length).toBeGreaterThan(0);
      expect(step.semanticStatus).toBe("lean-rejected-no-successor");
    }
  });

  it("exports accepted evidence and exact structured guard failures", () => {
    const artifact = parseArtifact(fixture("foundry-operating-guards.v2.json"));
    const checks = artifact.steps.flatMap((step) => step.checks);
    expect(checks.some((check) => check.condition === "processing-idle" && check.status === "accepted")).toBe(true);
    expect(checks.some((check) => check.condition === "processing-active" && check.status === "accepted")).toBe(true);
    expect(checks.some((check) => check.issues.some((issue) => issue.code === "active-work-present"))).toBe(true);
    expect(checks.some((check) => check.issues.some((issue) => issue.code === "active-work-missing"))).toBe(true);
  });

  it("projects two targeted machines over one authoritative world", () => {
    const artifact = parseArtifact(fixture("foundry-multi-machine-body-contention.v2.json"));
    expect(artifact.initial.machines).toHaveLength(2);
    expect(artifact.steps).toHaveLength(2);
    expect(artifact.steps[0]?.status).toBe("accepted");
    expect(artifact.steps[0]?.semanticStatus).toBe("lean-proved-shared-world-replay");
    expect(artifact.steps[1]?.status).toBe("rejected");
    expect(artifact.steps[1]?.after).toEqual(artifact.steps[1]?.before);
    expect(artifact.steps[1]?.effects).toEqual([]);
    expect(artifact.steps[1]?.issues.some((issue) => issue.code === "transfer-rejected")).toBe(true);
    expect(artifact.provenance.guarantees).toContain(
      "unique resources cannot simultaneously occupy two machines",
    );
  });

  it("keeps adjacent machine queues visually separated", () => {
    const artifact = parseArtifact(fixture("foundry-multi-machine-body-contention.v2.json"));
    const scene = projectScene(artifact, artifact.initial);
    const primaryOutput = scene.nodes.find(
      (node) => node.id === "machine:foundry-service:0:queue:output:0",
    );
    const secondaryInput = scene.nodes.find(
      (node) => node.id === "machine:foundry-service:1:queue:input:0",
    );

    expect(primaryOutput).toBeDefined();
    expect(secondaryInput).toBeDefined();
    expect(secondaryInput!.position.x - primaryOutput!.position.x).toBeGreaterThan(3);
  });
});
