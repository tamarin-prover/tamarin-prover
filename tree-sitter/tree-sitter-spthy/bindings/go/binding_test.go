package tree_sitter_spthy_test

import (
	"testing"

	tree_sitter_spthy "github.com/tamarin-prover/tamarin-prover/tree-sitter/tree-sitter-spthy/bindings/go"
	tree_sitter "github.com/tree-sitter/go-tree-sitter"
)

func TestCanParseGrammar(t *testing.T) {
	language := tree_sitter.NewLanguage(tree_sitter_spthy.Language())
	parser := tree_sitter.NewParser()
	defer parser.Close()
	if err := parser.SetLanguage(language); err != nil {
		t.Fatalf("error loading Spthy grammar: %v", err)
	}

	source := []byte("theory Example\nbegin\n/* scanner comment */\nrule Empty: [] --> [Out(<>) ]\nend")
	tree := parser.Parse(source, nil)
	defer tree.Close()
	if tree.RootNode().HasError() {
		t.Fatalf("unexpected parse errors: %s", tree.RootNode().ToSexp())
	}
}
