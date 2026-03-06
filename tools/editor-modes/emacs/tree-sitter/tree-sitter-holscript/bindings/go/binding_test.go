package tree_sitter_holscript_test

import (
	"testing"

	tree_sitter "github.com/tree-sitter/go-tree-sitter"
	tree_sitter_holscript "github.com/hol-theorem-prover/hol//bindings/go"
)

func TestCanLoadGrammar(t *testing.T) {
	language := tree_sitter.NewLanguage(tree_sitter_holscript.Language())
	if language == nil {
		t.Errorf("Error loading Holscript grammar")
	}
}
