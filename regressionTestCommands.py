"""Opt-in command checks for regressionTests.py; see doc/READMEregressionTests.md."""

import json
import logging
import math
import os
from pathlib import Path
import re
import signal
import subprocess
import tempfile
from collections import Counter


class RegressionFailure(Exception):
    pass


def verdicts(text):
    """Read summary verdicts, keeping side/name/quantifier but not step counts."""
    marker = "summary of summaries:"
    if marker not in text:
        raise RegressionFailure("No proof summary found")
    summary = text.rsplit(marker, 1)[1]
    pattern = (r"^  ((?:(?:LHS|RHS) :  )?\w+ \((?:all-traces|exists-trace)\): .+?|"
               r"DiffLemma:  .+?) \(\d+ steps\)$")
    results = Counter(" ".join(s.split()) for s in re.findall(pattern, summary, re.MULTILINE))
    if not results:
        raise RegressionFailure("No lemma verdicts found in proof summary")
    return results


def theory_text(text):
    """Remove nested comments, preserving quoted strings and line boundaries."""
    tokens = re.compile(r'''"(?:\\.|[^"\\])*"|'(?:\\.|[^'\\])*'|/\*|//[^\n]*''')
    delimiters = re.compile(r"/\*|\*/")
    result = []
    position = depth = 0
    while position < len(text):
        match = (delimiters if depth else tokens).search(text, position)
        end = match.end() if match else len(text)
        if depth:
            result.append(re.sub(r"[^\n]", " ", text[position:end]))
            if match:
                depth += 1 if match[0] == "/*" else -1
        elif match:
            result.append(text[position:match.start()])
            token = match[0]
            result.append(" " * len(token) if token.startswith(("/*", "//")) else token)
            if token == "/*":
                depth = 1
        else:
            result.append(text[position:end])
        position = end
    return "".join(result)


def validate(test):
    allowed = {"name", "args", "exit_code", "contains", "matches", "fact_arities", "baseline", "checks", "timeout", "slow"}
    if not isinstance(test, dict) or set(test) - allowed:
        raise RegressionFailure(f"Unknown test fields or invalid test: {test!r}")
    if not isinstance(test.get("name"), str) or not re.fullmatch(r"[\w-]+", test["name"]):
        raise RegressionFailure("Each test needs a name containing only letters, digits, underscores or hyphens")
    args = test.get("args", [])
    contains = test.get("contains", [])
    if not isinstance(args, list) or not all(isinstance(a, str) for a in args):
        raise RegressionFailure("args must be a list of strings")
    if not isinstance(contains, list) or not all(isinstance(s, str) and s for s in contains):
        raise RegressionFailure("contains must be a list of non-empty diagnostic substrings")
    code = test.get("exit_code", 0)
    if type(code) is not int or not 0 <= code <= 255:
        raise RegressionFailure("exit_code must be an integer between 0 and 255")
    if code and not contains:
        raise RegressionFailure("An expected failure also needs a diagnostic in contains")
    timeout = test.get("timeout", 120)
    if type(timeout) not in (int, float) or not math.isfinite(timeout) or timeout <= 0:
        raise RegressionFailure("timeout must be a positive, finite number of seconds")
    if type(test.get("slow", False)) is not bool:
        raise RegressionFailure("slow must be true or false")
    checks = test.get("checks", [])
    if not isinstance(checks, list) or any(c not in ("roundtrip", "partial-evaluation") for c in checks):
        raise RegressionFailure("checks may contain roundtrip and partial-evaluation")
    if len(set(checks)) != len(checks):
        raise RegressionFailure("Duplicate checks")
    baseline = test.get("baseline")
    if "baseline" in test and (not isinstance(baseline, str) or not baseline or
                                 Path(baseline).is_absolute() or ".." in Path(baseline).parts):
        raise RegressionFailure("baseline must be a relative path inside the baseline directory")
    if (checks or baseline is not None) and code:
        raise RegressionFailure("A proof baseline cannot be combined with an expected command failure")
    # The runner owns output files and proof/export flags in baseline workflows.
    if any(a in ("-o", "-O", "--output", "--Output") or
           a.startswith(("-o", "-O", "--output=", "--Output=")) for a in args):
        raise RegressionFailure("Output paths are managed by the regression runner")
    if (checks or baseline is not None) and any(a.startswith(("--prove", "--partial-evaluation")) for a in args):
        raise RegressionFailure("Baseline checks manage --prove and --partial-evaluation themselves")
    matches = test.get("matches", [])
    if not isinstance(matches, list):
        raise RegressionFailure("matches must be a list")
    for match in matches:
        if not isinstance(match, dict) or set(match) - {"regex", "min", "max", "theory_only"}:
            raise RegressionFailure(f"Invalid match assertion: {match!r}")
        if not isinstance(match.get("regex"), str) or not match["regex"]:
            raise RegressionFailure("Each match assertion needs a non-empty regex")
        try:
            re.compile(match["regex"])
        except re.error as error:
            raise RegressionFailure(f"Invalid regex: {error}") from error
        if not any(k in match for k in ("min", "max")):
            raise RegressionFailure("Each match assertion needs min or max")
        if any(type(match[k]) is not int or match[k] < 0 for k in ("min", "max") if k in match):
            raise RegressionFailure("Match bounds must be non-negative integers")
        if match.get("min", 0) > match.get("max", math.inf):
            raise RegressionFailure("Match min exceeds max")
        if type(match.get("theory_only", False)) is not bool:
            raise RegressionFailure("theory_only must be true or false")
    arities = test.get("fact_arities", {})
    if not isinstance(arities, dict):
        raise RegressionFailure("fact_arities must map fact-name regexes to maximum arities")
    for pattern, maximum in arities.items():
        if not isinstance(pattern, str) or not pattern or type(maximum) is not int or maximum < 0:
            raise RegressionFailure("Fact arity assertions need a non-empty regex and a non-negative integer maximum")
        try:
            re.compile(pattern)
        except re.error as error:
            raise RegressionFailure(f"Invalid fact-name regex: {error}") from error


def check_fact_arities(text, assertions):
    # Quoted terms are single tokens; commas in tuples and function applications
    # belong to the nested term, not to the enclosing fact's argument list.
    tokens = re.findall(r'''"(?:\\.|[^"\\])*"|'(?:\\.|[^'\\])*'|\w+|[^\s]''', theory_text(text))
    for pattern, maximum in assertions.items():
        found = False
        for index, name in enumerate(tokens[:-1]):
            if not re.fullmatch(r"\w+", name) or not re.fullmatch(pattern, name) or tokens[index + 1] != "(":
                continue
            found = True
            closing = [")"]
            arity = 0 if tokens[index + 2:index + 3] == [")"] else 1
            for position in range(index + 2, len(tokens)):
                token = tokens[position]
                if token in ("(", "<"):
                    closing.append(")" if token == "(" else ">")
                elif token in (")", ">"):
                    if token != closing.pop():
                        raise RegressionFailure(f"Unbalanced term in {name}")
                    if not closing:
                        break
                elif token == "," and len(closing) == 1:
                    arity += 1
            else:
                raise RegressionFailure(f"Unterminated argument list in {name}")
            if arity > maximum:
                raise RegressionFailure(f"Fact {name}: arity {arity} exceeds maximum {maximum}")
        if not found:
            raise RegressionFailure(f"No facts match {pattern!r}")


def run_process(command, timeout):
    # Kill the process group on timeout: Maude must not outlive a failed test.
    with subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                          text=True, encoding="utf-8", errors="replace",
                          start_new_session=(os.name == "posix")) as process:
        try:
            output, _ = process.communicate(timeout=timeout)
        except subprocess.TimeoutExpired:
            if os.name == "posix":
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
            else:
                process.kill()
            output, _ = process.communicate()
            raise RegressionFailure(f"Timed out after {timeout}s\n{output}") from None
    return process.returncode, output


def check_output(test, code, output):
    expected = test.get("exit_code", 0)
    if code != expected:
        raise RegressionFailure(f"Expected exit {expected}, got {code}\n{output}")
    for diagnostic in test.get("contains", []):
        if diagnostic not in output:
            raise RegressionFailure(f"Missing diagnostic {diagnostic!r}\n{output}")
    for match in test.get("matches", []):
        text = theory_text(output) if match.get("theory_only") else output
        count = len(re.findall(match["regex"], text, re.MULTILINE))
        if not match.get("min", 0) <= count <= match.get("max", math.inf):
            raise RegressionFailure(f"Pattern {match['regex']!r}: {count} matches, expected {match}\n{output}")
    if test.get("fact_arities"):
        check_fact_arities(output, test["fact_arities"])


def run_test(source, test, tamarin, baseline_dir, artifacts):
    expected = None
    if "baseline" in test:
        expected = verdicts((baseline_dir / test["baseline"]).read_text(encoding="utf-8"))
    artifacts.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="tamarin-regression-") as temporary:
        work = Path(temporary)

        def invoke(label, input_file, flags=(), prove=False, export=False, check_verdicts=False):
            command = [tamarin, str(input_file), "-d=0", *test.get("args", []), *flags]
            if prove:
                command.append("--prove")
            generated = work / f"{label}.spthy"
            if export:
                command.append(f"--output={generated}")
            log_path = artifacts / f"{label}.log"
            try:
                code, output = run_process(command, test.get("timeout", 120))
            except (OSError, RegressionFailure) as error:
                log_path.write_text(f"Command: {command!r}\n{error}\n", encoding="utf-8")
                raise RegressionFailure(f"{label}: {error}; log: {log_path}") from error
            log_path.write_text(f"Command: {command!r}\nExit: {code}\n{output}", encoding="utf-8")
            check_output(test, code, output)
            if export:
                if not generated.is_file():
                    raise RegressionFailure(f"{label}: no exported theory was written")
                # Keep generated theories for diagnosis, without making them case-study inputs.
                (artifacts / f"{label}.theory").write_bytes(generated.read_bytes())
            if prove or check_verdicts:
                actual = verdicts(output)
                if actual != expected:
                    raise RegressionFailure(f"{label}: verdicts differ from {test['baseline']}\n"
                                            f"Expected: {expected}\nActual: {actual}\nLog: {log_path}")
            return generated

        if expected is None:
            invoke("command", source)
            return
        checks = test.get("checks", [])
        original = invoke("original", source, prove=True, export="roundtrip" in checks)
        if "roundtrip" in checks:
            printed = invoke("printed", source, export=True)
            invoke("reloaded", printed, prove=True)
            invoke("replay", original, check_verdicts=True)
        if "partial-evaluation" in checks:
            flags = ("--partial-evaluation=summary",)
            evaluated = invoke("evaluated", source, flags, prove=True, export=True)
            unproved = invoke("unproved", source, flags, export=True)
            invoke("evaluated-reloaded", unproved, prove=True)
            invoke("evaluated-replay", evaluated, check_verdicts=True)
            invoke("reevaluated", unproved, flags, prove=True)


def run_tests(tamarin, baseline_dir, slow=False, files=None, root=Path("."), artifacts=None):
    """Discover only sidecar files; ordinary examples gain no extra invocations."""
    root = root.resolve()
    baseline_dir = Path(baseline_dir) / ("" if slow else "fast-tests")
    artifacts = Path(artifacts) if artifacts is not None else root / "case-studies" / "command-tests"
    selected = [Path(f).resolve() for f in files] if files else sorted((root / "examples").rglob("*.spthy.test.json"))
    successful = True
    total = 0
    for sidecar in selected:
        try:
            relative = sidecar.relative_to(root / "examples")
            if not str(sidecar).endswith(".spthy.test.json"):
                raise RegressionFailure("Expected a .spthy.test.json sidecar")
            source = Path(str(sidecar).removesuffix(".test.json"))
            if not source.is_file():
                raise RegressionFailure(f"Missing input theory: {source}")
            document = json.loads(sidecar.read_text(encoding="utf-8"))
            if not isinstance(document, dict) or set(document) != {"tests"} or not isinstance(document["tests"], list) or not document["tests"]:
                raise RegressionFailure("A sidecar must contain a non-empty tests list")
            names = set()
            for test in document["tests"]:
                validate(test)
                if test["name"] in names:
                    raise RegressionFailure(f"Duplicate test name: {test['name']}")
                names.add(test["name"])
            for test in document["tests"]:
                if test.get("slow") and not slow:
                    continue
                if test.get("checks") and "baseline" not in test:
                    example = source.relative_to(root / "examples")
                    suffix = "_analyzed-diff.spthy" if "--diff" in test.get("args", []) else "_analyzed.spthy"
                    test = dict(test, baseline=str(example.with_name(example.stem + suffix)))
                total += 1
                label = f"{relative}: {test['name']}"
                logging.info(f"Command regression: {label}")
                try:
                    run_test(source, test, tamarin, baseline_dir,
                             artifacts / str(relative).removesuffix(".spthy.test.json") / test["name"])
                except (OSError, RegressionFailure) as error:
                    logging.error(f"FAIL {label}: {error}")
                    successful = False
        except (OSError, ValueError, RegressionFailure) as error:
            logging.error(f"FAIL {sidecar}: {error}")
            successful = False
    logging.warning(f"Command regressions: {total} tests; {'passed' if successful else 'FAILED'}")
    return successful
