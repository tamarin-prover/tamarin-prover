# Variables
CARGO = cargo
TREE_SITTER_CLI = tree-sitter-cli
TREE_SITTER_DIR = tree-sitter-spthy

# Default target
.DEFAULT_GOAL := all

# Phony targets
.PHONY: all install generate

# Default task
all: install generate

# Install tree-sitter-cli
install:
	$(CARGO) install $(TREE_SITTER_CLI)

# Generate tree-sitter grammar
generate:
	cd $(TREE_SITTER_DIR) && tree-sitter generate
