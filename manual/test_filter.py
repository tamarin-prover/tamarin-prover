"""Grammar selections must not silently disappear from the manual."""

import pathlib
import re
import tempfile
import unittest

import filter as manual_filter


class GrammarSelectionTests(unittest.TestCase):
    def test_missing_rule_is_an_error_even_when_other_rules_exist(self):
        with tempfile.TemporaryDirectory() as directory:
            grammar = pathlib.Path(directory) / "grammar.ebnf"
            grammar.write_text("  heuristic  ::=  ranking_sequence+\n")
            with self.assertRaisesRegex(ValueError, "unknown grammar rules: old_ranking"):
                manual_filter.includefilerules(str(grammar), ["heuristic", "old_ranking"])

    def test_rule_selection_matches_whole_names(self):
        with tempfile.TemporaryDirectory() as directory:
            grammar = pathlib.Path(directory) / "grammar.ebnf"
            grammar.write_text("  _term  ::=  ident\n  nested_term  ::=  '(' _term ')'\n")
            self.assertEqual(
                manual_filter.includefilerules(str(grammar), ["_term"]),
                ["  _term  ::=  ident\n"],
            )

    def test_all_manual_grammar_selectors_resolve(self):
        manual = pathlib.Path(__file__).resolve().parent
        count = 0
        for source in sorted((manual / "src").glob("*.md")):
            for line in source.read_text().splitlines():
                grammar = re.search(r'grammar\s*=\s*"([^"]+)"', line)
                rules = re.search(r'rules\s*=\s*"([^"]+)"', line)
                if grammar and rules:
                    with self.subTest(source=source.name, rules=rules[1]):
                        self.assertTrue(manual_filter.includefilerules(
                            str(manual / grammar[1]), rules[1].split(",")
                        ))
                    count += 1
        self.assertGreater(count, 0, "no grammar sections were checked")


if __name__ == "__main__":
    unittest.main()
