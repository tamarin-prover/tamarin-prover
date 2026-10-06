"""Test the runner's failure detection without requiring a Tamarin build."""

import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import regressionTestCommands as commands
import regressionTests


def summary(*lines):
    return "summary of summaries:\n\n" + "\n".join("  " + line for line in lines) + "\n"


BASELINE = summary("LHS :  reachable (exists-trace): verified (3 steps)",
                   "RHS :  reachable (exists-trace): falsified - no trace found (4 steps)",
                   "DiffLemma:  Observational_equivalence : analysis incomplete (8 steps)")


class VerdictTests(unittest.TestCase):
    def test_steps_and_order_do_not_matter(self):
        changed = summary(*reversed(BASELINE.splitlines()[2:])).replace("(3 steps)", "(30 steps)")
        # Preserve the summary's indentation when reversing its lines.
        changed = changed.replace("    ", "  ")
        self.assertEqual(commands.verdicts(BASELINE), commands.verdicts(changed))

    def test_sides_and_result_kinds_matter(self):
        for changed in [BASELINE.replace("LHS", "TEMP").replace("RHS", "LHS").replace("TEMP", "RHS"),
                        BASELINE.replace("analysis incomplete", "falsified - found trace"),
                        BASELINE.replace("no trace found", "found trace")]:
            with self.subTest(changed=changed):
                self.assertNotEqual(commands.verdicts(BASELINE), commands.verdicts(changed))

    def test_missing_and_duplicate_lemmas_matter(self):
        line = "RHS :  reachable (exists-trace): falsified - no trace found (4 steps)"
        self.assertNotEqual(commands.verdicts(BASELINE), commands.verdicts(BASELINE + "  " + line + "\n"))
        self.assertNotEqual(commands.verdicts(BASELINE), commands.verdicts(BASELINE.replace("  " + line + "\n", "")))

    def test_missing_summary_cannot_pass(self):
        for text in ["", "verified", "summary of summaries:\nprocessing time: 0.1s"]:
            with self.subTest(text=text), self.assertRaises(commands.RegressionFailure):
                commands.verdicts(text)


class ExpectationTests(unittest.TestCase):
    def test_expected_failure_needs_both_status_and_diagnostic(self):
        test = {"name": "negative", "exit_code": 1, "contains": ["expected diagnostic"]}
        commands.validate(test)
        commands.check_output(test, 1, "expected diagnostic")
        for status, output in [(0, "expected diagnostic"), (-11, "expected diagnostic"),
                               (2, "expected diagnostic"), (1, "unrelated error")]:
            with self.subTest(status=status, output=output), self.assertRaises(commands.RegressionFailure):
                commands.check_output(test, status, output)

    def test_metadata_errors_cannot_silently_disable_checks(self):
        for fields in [{"check": ["roundtrip"]}, {"checks": ["unknown"]},
                       {"checks": "roundtrip"}, {"baseline": None},
                       {"checks": ["roundtrip"], "exit_code": 1, "contains": ["error"]},
                       {"checks": ["roundtrip"], "args": ["--prove"]},
                       {"exit_code": 1}, {"exit_code": True}, {"exit_code": -1},
                       {"timeout": 0}, {"timeout": float("nan")},
                       {"baseline": "../other.spthy"}, {"baseline": ""},
                       {"args": "--diff"}, {"args": ["--output=elsewhere"]}, {"args": ["-oelsewhere"]},
                       {"baseline": "a.spthy", "args": ["--prove"]},
                       {"matches": [{"regex": "(", "min": 1}]},
                       {"matches": [{"regex": "x", "min": 2, "max": 1}]}]:
            with self.subTest(fields=fields), self.assertRaises(commands.RegressionFailure):
                commands.validate({"name": "test", **fields})

    def test_counts_ignore_source_comments_but_preserve_quoted_terms(self):
        text = "/* rule ignored */\n// rule ignored\nrule A: [F('/* literal */')] --> []\n"
        test = {"matches": [{"regex": "rule ", "min": 1, "max": 1, "theory_only": True}]}
        commands.check_output(test, 0, text)
        self.assertIn("'/* literal */'", commands.theory_text(text))
        with self.assertRaises(commands.RegressionFailure):
            commands.check_output(test, 0, text + "rule B: [] --> []\n")

    def test_nested_comments_do_not_contribute_matches(self):
        text = '''/* outer " unmatched quote
/* inner */
rule Commented: [] --> []
// /* another nested comment */
*/
rule Real: [F('/* literal */'), G("// literal")] --> []
'''
        commands.check_output({"matches": [{"regex": "^rule ", "min": 1, "max": 1,
                                             "theory_only": True}]}, 0, text)
        stripped = commands.theory_text(text)
        self.assertNotIn("Commented", stripped)
        self.assertIn("F('/* literal */'), G(\"// literal\")", stripped)
        self.assertEqual(stripped.count("\n"), text.count("\n"))

    def test_fact_arity_counts_only_outer_arguments(self):
        test = {"name": "payload", "fact_arities": {"Let_[0-9]+": 2, "Empty": 0}}
        commands.validate(test)
        output = '''/* Let_0(a,b,c) /* nested */ */
// Let_1(a,b,c)
rule Test:
  [ Let_11(f(a,g(b,c)), <x,<y,z>>), Empty(),
    Let_12('commas, brackets () <>', "Let_13(a,b,c)"),
    OtherLet_14(a,b,c) ]
  --> [ Let_15(
    h(<x,y>), z) ]
'''
        commands.check_output(test, 0, output)
        with self.assertRaisesRegex(commands.RegressionFailure, "arity 3 exceeds maximum 2"):
            commands.check_output(test, 0, output + "Let_16(f(a,b), <c,d>, e)")

    def test_fact_arity_requires_a_matching_fact(self):
        for output in ["", "/* Let_1(x) */", "'Let_1(x)'", "OtherLet_1(x)"]:
            with self.subTest(output=output), self.assertRaisesRegex(commands.RegressionFailure, "No facts match"):
                commands.check_output({"fact_arities": {"Let_[0-9]+": 2}}, 0, output)

    def test_fact_arity_rejects_incomplete_or_unbalanced_terms(self):
        for output in ["Let_1(", "Let_1(f(x)", "Let_1(<x,y))", "Let_1(x>"]:
            with self.subTest(output=output), self.assertRaises(commands.RegressionFailure):
                commands.check_output({"fact_arities": {"Let_[0-9]+": 2}}, 0, output)

    def test_fact_arity_metadata_is_validated(self):
        for assertions in [[], {"": 2}, {"(": 2}, {"Let_.*": -1}, {"Let_.*": True}, {"Let_.*": 2.5}]:
            with self.subTest(assertions=assertions), self.assertRaises(commands.RegressionFailure):
                commands.validate({"name": "payload", "fact_arities": assertions})


class ProcessTests(unittest.TestCase):
    def test_stderr_and_exit_status_are_retained(self):
        code, output = commands.run_process([sys.executable, "-c",
                                            "import sys; print('diagnostic', file=sys.stderr); sys.exit(1)"], 5)
        self.assertEqual(code, 1)
        self.assertIn("diagnostic", output)

    def test_timeout_is_always_a_failure(self):
        with self.assertRaisesRegex(commands.RegressionFailure, "Timed out"):
            commands.run_process([sys.executable, "-c", "import time; time.sleep(30)"], 0.1)

    @unittest.skipUnless(os.name == "posix", "POSIX signal exit status")
    def test_crash_is_distinct_from_expected_rejection(self):
        code, _ = commands.run_process([sys.executable, "-c",
                                       "import os,signal; os.kill(os.getpid(),signal.SIGTERM)"], 5)
        self.assertEqual(code, -signal.SIGTERM)

    def test_missing_executable_cannot_pass(self):
        with self.assertRaises(OSError):
            commands.run_process(["/nonexistent/tamarin-regression-executable"], 5)


class WorkflowTests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        self.source = self.root / "input.spthy"
        self.source.write_text("theory Test begin end\n")
        (self.root / "baseline.spthy").write_text(BASELINE)
        self.test = {"name": "export", "args": ["--diff", "--quit-on-warning"],
                     "baseline": "baseline.spthy", "checks": ["roundtrip", "partial-evaluation"]}

    def prover(self, argv, timeout):
        for arg in argv:
            if arg.startswith("--output="):
                Path(arg.split("=", 1)[1]).write_text("theory Export begin end\n")
        return 0, BASELINE.replace("(3 steps)", "(20 steps)")

    def run_test(self):
        commands.run_test(self.source, self.test, "tamarin-prover", self.root, self.root / "logs")

    def test_export_reload_and_replay_use_distinct_inputs(self):
        with patch.object(commands, "run_process", side_effect=self.prover) as run:
            self.run_test()
        invocations = [call.args[0] for call in run.call_args_list]
        self.assertEqual(len(invocations), 9)
        # Replaying a proved existential must not search its remaining branches.
        replays = [argv for argv in invocations if Path(argv[1]).name in ("original.spthy", "evaluated.spthy")]
        self.assertEqual(len(replays), 2)
        for argv in replays:
            self.assertNotIn("--prove", argv)
        fresh_searches = [argv for argv in invocations if Path(argv[1]).name in ("printed.spthy", "unproved.spthy")]
        self.assertEqual(len(fresh_searches), 3)
        for argv in fresh_searches:
            self.assertIn("--prove", argv)
        self.assertTrue((self.root / "logs" / "replay.log").is_file())

    def test_agreeing_wrong_results_still_fail_against_baseline(self):
        def wrong(argv, timeout):
            code, output = self.prover(argv, timeout)
            return code, output.replace("analysis incomplete", "verified")
        with patch.object(commands, "run_process", side_effect=wrong), \
                self.assertRaisesRegex(commands.RegressionFailure, "verdicts differ"):
            self.run_test()

    def test_replay_verdict_is_checked(self):
        for input_name, label in [("original.spthy", "replay"), ("evaluated.spthy", "evaluated-replay")]:
            def wrong(argv, timeout):
                code, output = self.prover(argv, timeout)
                if Path(argv[1]).name == input_name:
                    output = output.replace("analysis incomplete", "verified")
                return code, output
            with self.subTest(input=input_name), patch.object(commands, "run_process", side_effect=wrong), \
                    self.assertRaisesRegex(commands.RegressionFailure, f"{label}: verdicts differ"):
                self.run_test()

    def test_original_export_is_only_needed_for_roundtrip(self):
        for checks in [[], ["partial-evaluation"], ["roundtrip"]]:
            self.test["checks"] = checks
            with self.subTest(checks=checks), patch.object(commands, "run_process", side_effect=self.prover) as run:
                self.run_test()
                original = run.call_args_list[0].args[0]
                self.assertIn("--prove", original)
                self.assertEqual(any(arg.startswith("--output=") for arg in original), "roundtrip" in checks)

    def test_missing_export_does_not_reuse_an_old_file(self):
        with patch.object(commands, "run_process", side_effect=self.prover):
            self.run_test()
        with patch.object(commands, "run_process", return_value=(0, BASELINE)), \
                self.assertRaisesRegex(commands.RegressionFailure, "no exported theory"):
            self.run_test()

    def test_missing_baseline_is_an_error(self):
        (self.root / "baseline.spthy").unlink()
        with self.assertRaises(FileNotFoundError):
            self.run_test()


class IntegrationTests(unittest.TestCase):
    def setUp(self):
        # The mocked CLI runs should not print pretend make commands in CI.
        for level in ("info", "warning"):
            stub = patch.object(commands.logging, level)
            stub.start()
            self.addCleanup(stub.stop)

    def test_only_opted_in_sources_run(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            examples = root / "examples"
            examples.mkdir()
            (examples / "ordinary.spthy").write_text("ordinary")
            source = examples / "selected.spthy"
            source.write_text("selected")
            (examples / "selected.spthy.test.json").write_text(json.dumps({"tests": [{"name": "selected"}]}))
            with patch.object(commands, "run_test") as run:
                self.assertTrue(commands.run_tests("prover", root, root=root))
            self.assertEqual(run.call_count, 1)
            self.assertEqual(run.call_args.args[0], source)

    def test_baseline_is_inferred_from_source_and_mode(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            examples = root / "examples" / "nested"
            examples.mkdir(parents=True)
            (examples / "input.spthy").write_text("theory Test begin end")
            sidecar = examples / "input.spthy.test.json"
            for args, override, expected in [([], None, "nested/input_analyzed.spthy"),
                                             (["--diff"], None, "nested/input_analyzed-diff.spthy"),
                                             (["--diff"], "special.spthy", "special.spthy")]:
                test = {"name": "proof", "checks": ["roundtrip"], "args": args}
                if override is not None:
                    test["baseline"] = override
                sidecar.write_text(json.dumps({"tests": [test]}))
                with self.subTest(args=args, override=override), patch.object(commands, "run_test") as run:
                    self.assertTrue(commands.run_tests("prover", root, root=root))
                    self.assertEqual(run.call_args.args[1]["baseline"], expected)

    def test_slow_selection_and_baseline_directories(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "examples").mkdir()
            (root / "examples" / "input.spthy").write_text("theory Test begin end")
            sidecar = root / "examples" / "input.spthy.test.json"
            sidecar.write_text(json.dumps({"tests": [{"name": "fast"}, {"name": "slow", "slow": True}]}))
            for slow, expected in [(False, 1), (True, 2)]:
                with self.subTest(slow=slow), patch.object(commands, "run_test") as run:
                    self.assertTrue(commands.run_tests("prover", root / "reference", slow=slow, root=root))
                    self.assertEqual(run.call_count, expected)
                    expected_dir = root / "reference" if slow else root / "reference" / "fast-tests"
                    self.assertEqual(run.call_args.args[3], expected_dir)

    def test_explicit_selection_and_missing_file(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "examples").mkdir()
            for name in ("one", "two"):
                (root / "examples" / f"{name}.spthy").write_text("theory Test begin end")
                (root / "examples" / f"{name}.spthy.test.json").write_text(json.dumps({"tests": [{"name": name}]}))
            selected = root / "examples" / "two.spthy.test.json"
            with patch.object(commands, "run_test") as run:
                self.assertTrue(commands.run_tests("prover", root, files=[selected], root=root))
                self.assertEqual(run.call_count, 1)
                self.assertEqual(run.call_args.args[1]["name"], "two")
            selected.unlink()
            with self.assertLogs(level="ERROR"):
                self.assertFalse(commands.run_tests("prover", root, files=[selected], root=root))

    def test_malformed_sidecar_fails_suite(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "examples").mkdir()
            (root / "examples" / "input.spthy").write_text("theory Test begin end")
            sidecar = root / "examples" / "input.spthy.test.json"
            for content in ['{', '{"tests": []}', '{"tests": [{"name": "x"}, {"name": "x"}]}']:
                sidecar.write_text(content)
                with self.subTest(content=content), self.assertLogs(level="ERROR"):
                    self.assertFalse(commands.run_tests("prover", root, root=root))

    def test_command_failure_survives_successful_baseline_comparison(self):
        argv = ["regressionTests.py", "-noi", "--tamarin", sys.executable]
        with patch.object(sys, "argv", argv), patch.object(regressionTests, "runCommandTests", return_value=False), \
                patch.object(regressionTests, "compare", return_value=True), \
                patch.object(subprocess, "check_output", return_value=b""), self.assertRaises(SystemExit) as stopped:
            regressionTests.main()
        self.assertEqual(stopped.exception.code, 1)

    def test_no_make_does_not_rerun_commands(self):
        with patch.object(sys, "argv", ["regressionTests.py", "-noi", "-nom"]), \
                patch.object(regressionTests, "runCommandTests") as run, \
                patch.object(regressionTests, "compare", return_value=True), self.assertRaises(SystemExit) as stopped:
            regressionTests.main()
        self.assertEqual(stopped.exception.code, 0)
        run.assert_not_called()

    def test_command_only_repeats_and_retains_failures(self):
        argv = ["regressionTests.py", "-noi", "--command-tests-only", "selected.spthy.test.json", "-r", "3"]
        for results, status in [([True, True, True], 0), ([False, True, True], 1)]:
            with self.subTest(results=results), patch.object(sys, "argv", argv), \
                    patch.object(regressionTests, "runCommandTests", side_effect=results) as run, \
                    patch.object(regressionTests, "compare") as compare, \
                    patch.object(subprocess, "check_output") as build, \
                    patch.object(regressionTests.shutil, "rmtree") as remove, \
                    self.assertRaises(SystemExit) as stopped:
                regressionTests.main()
            self.assertEqual(stopped.exception.code, status)
            self.assertEqual(run.call_count, 3)
            self.assertEqual(run.call_args.args[3], ["selected.spthy.test.json"])
            compare.assert_not_called()
            build.assert_not_called()
            remove.assert_not_called()


if __name__ == "__main__":
    unittest.main()
