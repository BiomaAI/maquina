import { readFileSync } from "node:fs";
import { describe, expect, it } from "vitest";
import { parseArtifact, parseCatalog } from "./protocol";

function fixture(name: string): unknown {
  const url = new URL(`../public/generated/${name}`, import.meta.url);
  return JSON.parse(readFileSync(url, "utf8")) as unknown;
}

describe("Lean-owned showcase artifacts", () => {
  it("publishes a versioned catalog with multiple scenarios", () => {
    const catalog = parseCatalog(fixture("catalog.v1.json"));
    expect(catalog.schemaVersion).toBe(1);
    expect(catalog.entries.map((entry) => entry.id)).toEqual([
      "foundry-refuel-lifecycle",
      "foundry-active-presence",
    ]);
  });

  it("retains exact decimal quantities and replay provenance", () => {
    const artifact = parseArtifact(fixture("foundry-refuel-lifecycle.v1.json"));
    expect(typeof artifact.initial.nextProcessId).toBe("string");
    expect(artifact.steps).toHaveLength(7);
    expect(artifact.steps.every((step) => step.semanticStatus.startsWith("lean-"))).toBe(true);
    expect(artifact.steps.flatMap((step) => step.effects).some((effect) => effect.kind === "transfer")).toBe(true);
  });

  it("represents rejections as unchanged states with no effects", () => {
    const artifact = parseArtifact(fixture("foundry-active-presence.v1.json"));
    const rejected = artifact.steps.filter((step) => step.status === "rejected");
    expect(rejected).toHaveLength(2);
    for (const step of rejected) {
      expect(step.after).toEqual(step.before);
      expect(step.effects).toEqual([]);
      expect(step.issues.length).toBeGreaterThan(0);
      expect(step.semanticStatus).toBe("lean-rejected-no-successor");
    }
  });
});
