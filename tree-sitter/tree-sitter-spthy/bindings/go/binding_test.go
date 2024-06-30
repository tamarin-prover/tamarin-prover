package tree_sitter_spthy_test

import (
	"testing"

	tree_sitter "github.com/smacker/go-tree-sitter"
	"github.com/tamarin-prover/tamarin-prover/tree-sitter/tree-sitter-spthy"
)

func TestCanLoadGrammar(t *testing.T) {
	language := tree_sitter.NewLanguage(tree_sitter_spthy.Language())
	if language == nil {
		t.Errorf("Error loading Spthy grammar")
	}
}
