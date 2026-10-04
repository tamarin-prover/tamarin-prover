# RegressionTests - CI for Tamarin Prover

RegressionTests is a script that runs tests for Tamarin either locally or in [GitHub Actions](../.github/workflows/tamarin-integration-test.yaml).



## Usage

Basic usage is to execute the script without any arguments. To do so, go to the directory root:

```bash
$ cd tamarin-prover
```

and type:

```bash
$ python3 regressionTests.py
```



## What does the script do?

- it calls `stack install` (prevented by `-noi`)
- it runs the Tree-sitter parser tests if `-p` is given
- it discovers `.spthy.test.json` companion files under `examples/` and runs their command checks (unless `-nom` is given)
- it runs the case studies (unless `-nom` is given), using `make -j` for parallel execution:
  - `make fast-case-studies sapic-case-studies-fast FAST=y` by default
  - `make case-studies` if `-s` (slow) is given
- for each `.spthy` in the folder `case-studies`
  - it searches for the equivalent in `case-studies-regression` (or another folder specified by `-d`)
  - it checks that the generated output can be parsed, and that printing and reparsing the source with `--parse-only` preserves its output (prevented by `-nopt`)
  - it parses the steps and times for both files
  - it assures that the files have the same amount of lemmas and they have the same outcome (verified vs. trace-found)
- it outputs the comparison of steps and times depending on the level of verbosity `-v`
- it repeats the command checks, case-study generation and comparisons `-r` times to provide more confidence in time measurements
- it returns `0` if the checks succeed, or `1` if a check fails or results, step counts or files do not match

With `--command-tests-only`, it runs only the command checks after installation,
skipping Tree-sitter tests, case-study generation and ordinary output comparisons.
`-nom` instead compares existing case-study outputs without generating new ones;
it still runs their output-parsing checks unless `-nopt` is also given.
These flags cannot be used together.

Warning:
- The make command can take more than an hour to run, consider `-j` if you run on a server with many cores
- The tool does not show any differences in the proofs if the step count didn't change



## Arguments

Here is the output of `python3 regressionTests.py -h`:

```
usage: regressionTests.py [-h] [-s] [-noi] [-nom] [-j JOBS] [-d DIRECTORY]
                          [-r REPEAT] [-v VERBOSE] [-p] [-nopt]
                          [--no-sapic-output-parse-test]
                          [--command-tests-only [FILE ...]]
                          [--tamarin TAMARIN]

options:
  -h, --help            show this help message and exit
  -s, --slow            Run slow tests (instead of fast tests)
  -noi, --no-install    Do not call 'stack install' before starting the tests
  -nom, --no-make       Skip command checks and case-study generation; compare existing outputs
  -j, --jobs JOBS       The amount of Tamarin instances used simultaneously. Each Tamarin instance should have 3 threads and 16GB RAM available
  -d, --directory DIRECTORY
                        The directory to compare the test results with. The default is case-studies-regression
  -r, --repeat REPEAT   Repeat everything r times (except for 'stack install'). This gives more confidence in time measurements
  -v, --verbose VERBOSE
                        Level of verbosity, values are from 0 to 6. Default is 3
                        0: show only critical error output and changes of verified vs. trace found
                        1: show summary of time and step differences
                        2: show step differences for changed lemmas
                        3: show step differences for changed lemmas and changed functions, rules, equations, warning, builtins and macros
                        4: show time differences for all lemmas
                        5: show shell command output
                        6: show diff output if the corresponding proofs changed
  -p, --parser-test     Run the parser tests.
  -nopt, --no-output-parse-test
                        Skip the output parse tests and the --parse-only round-trip tests
  --no-sapic-output-parse-test
                        Disable SAPIC/accountability output parse tests
  --command-tests-only [FILE ...]
                        Run only command checks (all sidecars, or the specified .spthy.test.json files)
  --tamarin TAMARIN     Tamarin executable (default: TAMARIN environment variable or tamarin-prover)
```



## Adding new files to test

For an ordinary case study, add the input under `examples/` and include it in
the appropriate case-study list in the Makefile. Run that target and put its
analysed output in the matching directory under `case-studies-regression/`.
The reference file **must** be output from the make command.

For a fast case study (also run in CI), include it in a list used by
`fast-case-studies` or `sapic-case-studies-fast`, and generate it with `FAST=y`.
Put its reference output under `case-studies-regression/fast-tests/`. Slow
reference outputs go under `case-studies-regression/` without `fast-tests/`.

For a command check, add `<example>.spthy.test.json` beside the input under
`examples/`. These files are discovered automatically; no Makefile entry is
needed just to run a command check. Tests that check an exit status or output
assertions do not need a reference file. Tests using `checks` or `baseline`
do need one; see [Command checks and expected failures](#command-checks-and-expected-failures).

## CI

[GitHub Actions](../.github/workflows/tamarin-integration-test.yaml) builds Tamarin
and runs `python3 regressionTests.py -v 6 -noi`. This includes the command checks
and fast case studies. Generated outputs and command-check logs are available
in the `case-studies` artifact, including when the tests fail.



## Makefile

The Makefile is also important. To make the `fast-case-studies` (used in the script with the fast tests), you should use the command `make fast-case-studies FAST=y`. If you don't precise `FAST=y`, the files will be in the directory `case-studies` and not `case-studies/fast-tests` and the script won't work.





## Contact

For any problem, please contact Philip Lukert.

## Command checks and expected failures

Some regressions concern rejection, translation, or saved-proof handling rather
than the result of a single proof search. Add a companion file named
`<example>.spthy.test.json` beside the affected input to enable these checks.
Examples without a companion file do not get additional prover runs.

`regressionTests.py` discovers companion files under `examples/` and runs their
checks before the ordinary case studies. They also run in CI. No separate shell
script or Makefile target is needed. `--no-make` skips these executions, just as
it skips generating case studies. Each repetition requested with `-r` reruns them.

To run only the command checks, optionally selecting particular companion files:

```sh
python3 regressionTests.py -noi --command-tests-only
python3 regressionTests.py -noi --command-tests-only examples/regression/negative/missing-end.spthy.test.json
python3 regressionTests.py -noi --command-tests-only --tamarin=/path/to/tamarin-prover
```

Run these commands from the repository root. File arguments are relative to
that working directory (so include `examples/`), or can be absolute paths to
companion files under `examples/`. Diagnostic labels and artifact subdirectories
use the path relative to `examples/`.

`--tamarin` selects the executable for command checks, case-study generation,
and existing output-parsing checks. It defaults to the `TAMARIN` environment
variable, or `tamarin-prover` on `PATH`. Use `-noi` with an already built executable;
otherwise the usual `stack install` runs first.

### Negative tests

For example, `examples/regression/negative/missing-end.spthy.test.json` contains:

```json
{
  "tests": [
    {
      "name": "missing-end",
      "args": ["--parse-only"],
      "exit_code": 1,
      "contains": ["unexpected end of input"]
    }
  ]
}
```

`exit_code` is the expected process exit status, an integer from 0 to 255. It
defaults to 0 (success). A nonzero value also requires at least one diagnostic
substring in `contains`, and cannot be combined with `checks` or `baseline`.

Both the exit status and every diagnostic substring must match. A timeout,
signal, missing executable, or unrelated rejection fails the test. Use a stable
part of the diagnostic rather than a full message containing paths or line numbers.
Arguments are passed directly to Tamarin, without a shell. The runner supplies
`-d=0` to disable derivation-check timeouts in these focused tests.

Put intentionally invalid parser inputs in `examples/regression/negative/`.
The Tree-sitter success-only sweep excludes that directory; the command runner
still discovers its companion files.

### Comparing exports and saved proofs

Use an existing regression baseline as the expected result:

```json
{
  "tests": [
    {
      "name": "saved-diff-proofs",
      "args": ["--diff", "--quit-on-warning"],
      "checks": ["roundtrip"]
    }
  ]
}
```

For these checks, the baseline is inferred from the input path with the
`examples/` prefix removed: `examples/ccs15/probEnc.spthy` uses
`ccs15/probEnc_analyzed-diff.spthy` when `args` includes `--diff`, or
`ccs15/probEnc_analyzed.spthy` otherwise.
Only set `baseline` to override this convention for a differently named target.

Baseline paths, including an explicit `baseline`, are relative to
`case-studies-regression/fast-tests/`, or to `case-studies-regression/` with
`--slow`. `--directory` changes that root using
the same convention as ordinary regression comparisons. A missing baseline or
missing proof summary fails the test. The runner never updates baselines.

The runner first proves the source. Each requested check then
compares its proof results with that same baseline:

- `roundtrip`: print without proofs and prove the reloaded output; also replay
  the saved original proof without `--prove`. Set `roundtrip_module` to
  `spthy`, `spthytyped`, or `msr` to select the unproved export format. This
  affects only printing; source and reloaded proofs still use normal proving.
- `partial-evaluation`: prove the partially evaluated source; export without
  proofs and prove the reloaded output; replay the saved evaluated proof; and
  partially evaluate and prove the unproved export again.

Both checks can be requested together. Comparisons preserve lemma names,
quantifiers, LHS/RHS labels, duplicate results, and verdicts (including incomplete
results), but ignore proof-step counts and timings. In particular, two equally
wrong runs do not pass merely because they agree with each other. The ordinary
baseline comparison still checks step counts as before.

For these proof checks, leave `--prove`, `--partial-evaluation`, and output paths
out of `args`: the runner controls them separately for each step. Tests without
`checks` or a `baseline` override run their specified command once, expecting exit
status zero by default. An explicit `baseline` without `checks` compares just the source proof.

### Other output assertions

`contains` checks literal substrings in the combined stdout/stderr. `matches`
can count regular-expression matches, for example to bound generated rule growth:

```json
"matches": [
  {"regex": "^rule ", "min": 8, "max": 52, "theory_only": true}
]
```

Either bound can be omitted; use equal bounds for an exact count. Regexes use
Python syntax with multiline matching. `theory_only` removes comments (including nested comments) before
counting, so source-process comments cannot masquerade as generated rules.
Assertions apply to every invocation in a test. For checks specific to one export
format, add a separate test with that format in `args`.

`fact_arities` bounds the number of arguments in generated facts, for example
to check that SAPIC intermediate facts do not retain unnecessary variables:

```json
"fact_arities": {"Let_[0-9]+": 2}
```

Each regex matches a whole fact name and maps to its maximum allowed arity.
At least one matching fact must occur, and every occurrence must fit the bound.
Comments are ignored; commas inside nested function applications, tuples, or
quoted strings do not count as argument separators.

Each test needs a unique `name` within its companion file. Optional `timeout`
sets a positive per-invocation limit in seconds (default 120). On POSIX systems a
timeout kills the process group, including Maude. Set `slow` to `true` for tests
that should run only with `--slow`; other tests run in both suites. Unknown fields
and malformed settings fail rather than silently disabling a check.

Logs and generated theories are kept under `case-studies/command-tests/`, grouped
by input and test name, and included in the existing CI artifact. Generated
copies use a `.theory` extension so the ordinary `.spthy` baseline scan does not
pick them up. They are diagnostic artifacts, never expected results.

The runner itself has tests that need no Tamarin build:

```sh
python3 -m unittest discover -s tests -p test_regression_commands.py
```
