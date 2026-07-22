from unittest import TestCase

import tree_sitter
import tree_sitter_spthy


class TestLanguage(TestCase):
    def test_can_parse_grammar(self):
        language = tree_sitter.Language(tree_sitter_spthy.language())
        parser = tree_sitter.Parser()
        parser.language = language

        source = b"theory Example\nbegin\n/* scanner comment */\nrule Empty: [] --> [Out(<>) ]\nend"
        tree = parser.parse(source)
        self.assertFalse(tree.root_node.has_error, str(tree.root_node))
