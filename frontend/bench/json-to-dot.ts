import { performance } from "node:perf_hooks";
import { spawn } from "node:child_process";
import { mkdir, readFile, readdir, writeFile } from "node:fs/promises";
import { basename, dirname, relative, resolve } from "node:path";

import { instance, type Graph as DotGraph } from "@viz-js/viz";
import { TamarinGraph, TamarinGraphBuildContext } from "../src/tmgraph";
import type { JSONGraph, JSONGraphs } from "../src/jsongraph";

type Options = {
  abbreviations: boolean;
  dotDirectory: string;
  fixtures: string[];
  samples: number;
  simplification: number;
  warmup: number;
};

type GraphStats = {
  edges: number;
  nodes: number;
};

type BenchmarkRecord = {
  abbreviations: boolean;
  edges: number;
  fixture: string;
  graphIndex: number;
  heapDeltaBytes: number;
  inputBytes: number;
  nodes: number;
  phase: "json-parse" | "json-to-dot";
  sample: number;
  simplification: number;
  timeMs: number;
};

const defaultOptions: Options = {
  abbreviations: true,
  dotDirectory: "bench/dot",
  fixtures: [],
  samples: 15,
  simplification: 2,
  warmup: 5,
};

function usage(): string {
  return `Usage: node --expose-gc bench/dist/json-to-dot.js [options] [json-file ...]

Options:
  --dot-dir <directory>     Directory for computed DOT files (default: bench/dot)
  --samples <count>          Measured samples per graph (default: 15)
  --warmup <count>           Unmeasured conversion runs per graph (default: 5)
  --simplification <level>   Tamarin graph simplification level (default: 2)
  --no-abbreviations         Disable JSON graph abbreviations
  --help                     Show this message

When no JSON files are provided, all JSON files below frontend/examples are used.
Each output line is a JSON record suitable for collection as JSONL.`;
}

function parseNonNegativeInteger(value: string, option: string): number {
  const parsed = Number(value);
  if (!Number.isInteger(parsed) || parsed < 0) {
    throw new Error(`${option} must be a non-negative integer, got ${value}.`);
  }
  return parsed;
}

function parseOptions(args: string[]): Options {
  const options = { ...defaultOptions };

  for (let index = 0; index < args.length; index += 1) {
    const argument = args[index];
    switch (argument) {
      case "--help":
        console.log(usage());
        process.exit(0);
      case "--dot-dir":
        options.dotDirectory = args[++index] ?? "";
        if (!options.dotDirectory) {
          throw new Error(`${argument} requires a directory.`);
        }
        break;
      case "--no-abbreviations":
        options.abbreviations = false;
        break;
      case "--samples":
        options.samples = parseNonNegativeInteger(args[++index] ?? "", argument);
        break;
      case "--simplification":
        options.simplification = parseNonNegativeInteger(args[++index] ?? "", argument);
        break;
      case "--warmup":
        options.warmup = parseNonNegativeInteger(args[++index] ?? "", argument);
        break;
      default:
        if (argument.startsWith("--")) {
          throw new Error(`Unknown option: ${argument}`);
        }
        options.fixtures.push(argument);
    }
  }

  return options;
}

async function findJsonFiles(directory: string): Promise<string[]> {
  const entries = await readdir(directory, { withFileTypes: true });
  const files = await Promise.all(entries.map(async entry => {
    const path = resolve(directory, entry.name);
    if (entry.isDirectory()) {
      return findJsonFiles(path);
    }
    return entry.isFile() && entry.name.endsWith(".json") ? [path] : [];
  }));
  return files.flat().sort();
}

function graphStats(graph: JSONGraph): GraphStats {
  return {
    nodes: graph.jgNodes.length,
    edges: graph.jgEdges.length,
  };
}

function runConversion(graph: JSONGraph, options: Options): DotGraph {
  const context = new TamarinGraphBuildContext(
    options.abbreviations ? graph.jgAbbrevs : [],
  );
  return new TamarinGraph(graph, context, options.simplification).dot();
}

function dotFilePath(fixture: string, graphIndex: number, dotDirectory: string): string {
  const fixturePath = relative(process.cwd(), fixture);
  const sourceName = fixturePath.startsWith("..")
    ? basename(fixture)
    : fixturePath;
  const stem = sourceName.replace(/\.json$/, "");
  return resolve(dotDirectory, `${stem}.graph-${graphIndex}.dot`);
}

async function writeDotFile(
  fixture: string,
  graphIndex: number,
  graph: JSONGraph,
  options: Options,
): Promise<string> {
  const dotGraph = runConversion(graph, options);
  const dotSource = (await instance()).renderString(dotGraph, { format: "dot" });
  const path = dotFilePath(fixture, graphIndex, options.dotDirectory);
  await mkdir(dirname(path), { recursive: true });
  await writeFile(path, dotSource, "utf8");
  return path;
}

function renderDotFile(dotPath: string): Promise<string> {
  const pdfPath = dotPath.replace(/\.dot$/, ".pdf");
  const logPath = `${dotPath}.log`;

  return new Promise(resolveRender => {
    const process = spawn("dot", ["-Tpdf", dotPath, "-o", pdfPath]);
    let stderr = "";

    process.stderr.setEncoding("utf8");
    process.stderr.on("data", (chunk: string) => {
      stderr += chunk;
    });
    process.on("error", error => {
      stderr += `${error.message}\n`;
    });
    process.on("close", async code => {
      if (code !== 0) {
        stderr += `Graphviz exited with status ${code}.\n`;
      }
      await writeFile(logPath, stderr, "utf8");
      resolveRender(code === 0 ? "" : dotPath);
    });
  });
}

async function renderDotFiles(dotPaths: string[]): Promise<void> {
  const failures: string[] = [];
  for (const dotPath of dotPaths) {
    const failedPath = await renderDotFile(dotPath);
    if (failedPath) {
      failures.push(failedPath);
    }
  }
  if (failures.length > 0) {
    throw new Error(`Graphviz failed to render: ${failures.join(", ")}`);
  }
}

function forceGc(): void {
  if (typeof global.gc === "function") {
    global.gc();
  }
}

function emit(record: BenchmarkRecord): void {
  console.log(JSON.stringify(record));
}

function emitParseSample(
  fixture: string,
  input: string,
  graphIndex: number,
  graph: JSONGraph,
  options: Options,
  sample: number,
): void {
  forceGc();
  const before = process.memoryUsage().heapUsed;
  const started = performance.now();
  JSON.parse(input) as JSONGraphs;
  const elapsed = performance.now() - started;
  const after = process.memoryUsage().heapUsed;
  const stats = graphStats(graph);

  emit({
    abbreviations: options.abbreviations,
    edges: stats.edges,
    fixture,
    graphIndex,
    heapDeltaBytes: after - before,
    inputBytes: Buffer.byteLength(input),
    nodes: stats.nodes,
    phase: "json-parse",
    sample,
    simplification: options.simplification,
    timeMs: elapsed,
  });
}

function emitConversionSample(
  fixture: string,
  input: string,
  graphIndex: number,
  options: Options,
  sample: number,
): void {
  // Reparse before each run because conversion abbreviates term objects in place.
  const graph = (JSON.parse(input) as JSONGraphs).graphs[graphIndex];
  forceGc();
  const before = process.memoryUsage().heapUsed;
  const started = performance.now();
  runConversion(graph, options);
  const elapsed = performance.now() - started;
  forceGc();
  const after = process.memoryUsage().heapUsed;
  const stats = graphStats(graph);

  emit({
    abbreviations: options.abbreviations,
    edges: stats.edges,
    fixture,
    graphIndex,
    heapDeltaBytes: after - before,
    inputBytes: Buffer.byteLength(input),
    nodes: stats.nodes,
    phase: "json-to-dot",
    sample,
    simplification: options.simplification,
    timeMs: elapsed,
  });
}

async function benchmarkFixture(path: string, options: Options): Promise<string[]> {
  const input = await readFile(path, "utf8");
  const graphs = (JSON.parse(input) as JSONGraphs).graphs;
  if (!Array.isArray(graphs) || graphs.length === 0) {
    throw new Error(`${path} does not contain any graphs.`);
  }

  const dotPaths: string[] = [];
  for (let graphIndex = 0; graphIndex < graphs.length; graphIndex += 1) {
    // DOT serialization is intentionally outside the measured benchmark phases.
    dotPaths.push(await writeDotFile(path, graphIndex, graphs[graphIndex], options));

    for (let warmup = 0; warmup < options.warmup; warmup += 1) {
      const graph = (JSON.parse(input) as JSONGraphs).graphs[graphIndex];
      runConversion(graph, options);
    }

    for (let sample = 0; sample < options.samples; sample += 1) {
      emitParseSample(path, input, graphIndex, graphs[graphIndex], options, sample);
      emitConversionSample(path, input, graphIndex, options, sample);
    }
  }
  return dotPaths;
}

async function main(): Promise<void> {
  const options = parseOptions(process.argv.slice(2));
  const fixtures = options.fixtures.length > 0
    ? options.fixtures.map(path => resolve(path))
    : await findJsonFiles(resolve(process.cwd(), "examples"));

  if (typeof global.gc !== "function") {
    console.error("Warning: run with --expose-gc for comparable heap measurements.");
  }

  const dotPaths: string[] = [];
  for (const fixture of fixtures) {
    dotPaths.push(...await benchmarkFixture(fixture, options));
  }

  // Render only after timing has completed so Graphviz work cannot affect samples.
  await renderDotFiles(dotPaths);
}

main().catch(error => {
  console.error(error instanceof Error ? error.stack : String(error));
  process.exitCode = 1;
});