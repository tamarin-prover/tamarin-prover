package tree_sitter_spthy_test

import (
	"testing"

	tree_sitter "github.com/tree-sitter/go-tree-sitter"
	tree_sitter_spthy "github.com/tree-sitter/tree-sitter-spthy/bindings/go"
)

func TestCanLoadGrammar(t *testing.T) {
	language := tree_sitter.NewLanguage(tree_sitter_spthy.Language())
	if language == nil {
		t.Errorf("Error loading Spthy grammar")
	}
}
