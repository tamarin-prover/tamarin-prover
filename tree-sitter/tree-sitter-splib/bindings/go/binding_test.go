package tree_sitter_splib_test

import (
	"testing"

	tree_sitter "github.com/smacker/go-tree-sitter"
	"github.com/tree-sitter/tree-sitter-splib"
)

func TestCanLoadGrammar(t *testing.T) {
	language := tree_sitter.NewLanguage(tree_sitter_splib.Language())
	if language == nil {
		t.Errorf("Error loading Splib grammar")
	}
}
