# Variables
NPM ?= npm
TREE_SITTER_DIR := tree-sitter-spthy

# Default target
.DEFAULT_GOAL := all

# Phony targets
.PHONY: all install generate

# Default task
all: generate

# Install the locked Node.js dependencies
install:
	cd $(TREE_SITTER_DIR) && $(NPM) ci

# Generate the tree-sitter grammar with the locked CLI version
generate: install
	cd $(TREE_SITTER_DIR) && $(NPM) run generate
