// Run from the repository root: node docs/reviews/2026-09-06/protocol-probes.mjs
// Diagnostic probes: an ACCEPTED result documents a validation gap, not success.
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { createRequire } from "node:module";
import { pathToFileURL } from "node:url";

const root = new URL("../../../", import.meta.url);
const require = createRequire(new URL("visualizer/package.json", root));
const ts = require("typescript");
const temporary = fs.mkdtempSync(path.join(os.tmpdir(), "maquina-review-"));
try {
  const modulePath = path.join(temporary, "protocol.mjs");
  fs.writeFileSync(modulePath, ts.transpileModule(
    fs.readFileSync(new URL("visualizer/src/protocol.ts", root), "utf8"),
    { compilerOptions: { target: ts.ScriptTarget.ES2022, module: ts.ModuleKind.ES2022 } },
  ).outputText);
  const { parseArtifact } = await import(pathToFileURL(modulePath).href);
  const fresh = (name = "veiled-accord") => JSON.parse(fs.readFileSync(
    new URL(`visualizer/public/generated/${name}.v4.json`, root), "utf8",
  ));
  const trials = [
    ["numeric holding instead of exact string", (a) => { a.initial.holdings[0].quantity = 9007199254740992; }],
    ["missing provenance", (a) => { delete a.provenance; }],
    ["nonnumeric metric", (a) => { a.commandGraph.nodes[0].metrics[0].value = "not-a-number"; }],
    ["edge before disconnected from source", (a) => { a.commandGraph.resolutions[0].steps[0].before.holdings = []; }],
    ["edge after disconnected from target", (a) => { a.commandGraph.resolutions[0].steps.at(-1).after.holdings = []; }],
    ["null machine", (a) => { a.initial.machines.push(null); }],
    ["rejected step changes world", (a) => { a.steps.find((s) => s.status === "rejected").after.holdings = []; }, "foundry-active-presence"],
  ];
  for (const [name, mutate, fixture] of trials) {
    const artifact = fresh(fixture);
    mutate(artifact);
    try {
      parseArtifact(artifact);
      console.log(`ACCEPTED: ${name}`);
    } catch (error) {
      console.log(`REJECTED: ${name}: ${error.message}`);
    }
  }
} finally {
  fs.rmSync(temporary, { recursive: true, force: true });
}
