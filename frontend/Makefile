RUNNER := bench/dist/json-to-dot.js
RESULTS ?= benchmark.jsonl
DOT_DIR ?= bench/dot
BASELINE_DIR ?= bench/baseline/macos-arm64
BENCH_ARGS ?=
INPUTS ?=

.PHONY: baseline benchmark benchmark-build clean-benchmark

baseline: RESULTS := $(BASELINE_DIR)/benchmark.jsonl
baseline: DOT_DIR := $(BASELINE_DIR)/dot
baseline: benchmark
	git describe --always --dirty --broken > "$(BASELINE_DIR)/git-revision.txt"
	node --version > "$(BASELINE_DIR)/node-version.txt"
	dot -V 2> "$(BASELINE_DIR)/graphviz-version.txt"
	uname -srm > "$(BASELINE_DIR)/platform.txt"

benchmark: benchmark-build
	mkdir -p "$$(dirname "$(RESULTS)")" "$(DOT_DIR)"
	node --expose-gc "$(RUNNER)" --dot-dir "$(DOT_DIR)" $(BENCH_ARGS) $(INPUTS) > "$(RESULTS)"

benchmark-build:
	npx vite build --config bench/vite.config.ts

clean-benchmark:
	rm -rf bench/dist bench/dot