# JSON-to-DOT Benchmark

This harness measures the frontend's existing `TamarinGraph` construction and
`dot()` conversion without changing production code. It does not measure Viz.js
layout, SVG rendering, fetching, or DOM processing.

## Run

From `frontend/`, run every JSON fixture below `examples/` and write JSONL timing
records to `benchmark.jsonl`:

```sh
make benchmark
```

The target builds the standalone Node runner, writes one DOT file per graph to
`bench/dot/`, invokes it with garbage collection exposed, then renders every
generated DOT file with Graphviz. Each DOT file receives a sibling PDF and a
`.dot.log` file containing Graphviz's warning and error output. Rendering occurs
only after timing has completed, so it does not affect benchmark samples.
Configure output locations or runner options through Make variables:

```sh
make benchmark RESULTS=results.jsonl DOT_DIR=output/dot \
  BENCH_ARGS="--samples 30 --warmup 10"
```

For a single input, use `INPUTS`:

```sh
make benchmark INPUTS=examples/graphs/tutorial-lm1-a-contra.json
```

## Baseline

Capture a comparison baseline for the current macOS ARM64 environment with:

```sh
make baseline
```

This runs the full corpus with the default benchmark configuration and stores its
JSONL timing and memory records, DOT files, PDFs, Graphviz logs, Git revision,
Node version, Graphviz version, and platform information under
`bench/baseline/macos-arm64/`. Use a separate `BASELINE_DIR` for measurements on
another machine or toolchain:

```sh
make baseline BASELINE_DIR=bench/baseline/linux-x86_64
```

The runner can also be built and executed directly:

```sh
npx vite build --config bench/vite.config.ts
node --expose-gc bench/dist/json-to-dot.js \
  examples/graphs/tutorial-lm1-a-contra.json > benchmark.jsonl
```

With no input files, the runner measures every JSON file below `examples/`.

```sh
node --expose-gc bench/dist/json-to-dot.js > benchmark.jsonl
```

Useful options are `--samples 30`, `--warmup 10`, `--simplification 0`, and
`--no-abbreviations`. The harness writes one DOT file per graph to `bench/dot/`.
Use `--dot-dir path/to/dots` to select another directory. Run
`node bench/dist/json-to-dot.js --help` for the full interface.

DOT files use the source fixture's relative path and a graph index. For example,
the first graph in `examples/graphs/tutorial-lm1-a-contra.json` is stored at:

```text
bench/dot/examples/graphs/tutorial-lm1-a-contra.graph-0.dot
```

The files are Graphviz-normalized DOT generated from the same `DotGraph` passed
to Viz.js in the frontend. DOT serialization is performed once per input graph,
before warm-up and measured samples, and therefore does not affect reported
conversion timings.

After all timing samples have been recorded, Graphviz renders the example above
to `bench/dot/examples/graphs/tutorial-lm1-a-contra.graph-0.pdf` and writes its
stderr output to `tutorial-lm1-a-contra.graph-0.dot.log`. Empty logs indicate
that Graphviz produced no warnings or errors. A Graphviz rendering failure is
reported after every generated DOT file has been attempted, leaving its log on
disk for inspection.

## Output

The runner writes one JSON object per line. Each graph receives separate records
for `json-parse` and `json-to-dot`. Records include input size, graph index,
node and edge counts, simplification mode, elapsed milliseconds, and heap delta.

The runner reparses the source JSON before each conversion sample. The existing
conversion may apply abbreviations by mutating term objects, so reusing one parsed
object would make later samples unrepresentative.

Use the median and p95 of `timeMs` for comparisons. Heap deltas are meaningful
only when runs use `--expose-gc` and execute on the same Node version and host.